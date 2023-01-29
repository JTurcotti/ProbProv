open Expr
open Typecheck
open Util

type local_set = LocalSet.t
type label_set = LabelSet.t

exception InterferencePathFailure of string

(**
   A trace_entry is either an assignment of a local to an
   aexp, with all locals mentioned in the aexp listed, or
   it is a branch on an aexp, with all locals similarly
   listed and the direction the branch took noted
*)
type trace_entry =
  | AssignEntry of local * aexp * local_set
  | BranchEntry of aexp * local_set * branch * bool

(**
   a `trace` is a list of trace_entry's - 
   represents a sequence of program expressions corresponding to a possible
   flow 
*)
type trace = trace_entry list

(** a trace_pos is a trace along with an indexing int into it *)
type trace_pos = {t: trace; pos: int}

module TraceSet = Set(struct type t = trace end)
type trace_set = TraceSet.t

(**
   A subtrace is a trace along with an ascending list of
   indices of that trace identifying a subsequence of it,
   and a boolean flag indicating whether it is an explicit flow
*)
type subtrace = {
  underlying: trace;
  filter: int list;
  is_explicit: bool;
}

let subtrace_nth st n =
  List.nth st.underlying (List.nth st.filter n)

module SubtraceSet = Set(struct type t = subtrace end)
type subtrace_set = SubtraceSet.t

(**
   A branch tree represents a prefix tree of subtraces
*)
type branch_tree =
  | Branch of
      local_set (* the locals that this branch depends on *)
      * trace_pos list (* the set of program traces
                        that pass through this branch,
                        with this branch pointed out *)
      * branch_tree (* left subtree (branch taken) *)
      * branch_tree (* right subtree (branch not taken) *)
  | Leaf of
      subtrace_set (* the subtraces that lead to this leaf *)

(** trace_labels takes a trace and returns the labels of all
    aexprs contained in the trace (useful for displaying trace)
*)
let rec trace_labels (t : trace) : label_set =
  match t with
  | [] -> LabelSet.empty
  | AssignEntry(_, a, _) :: t'
  | BranchEntry(a, _, _, _) :: t'-> LabelSet.union
                                      (aexpr_labels a)
                                      (trace_labels t')

module OptLabelMap = Map(struct type t = label option end)

(**
   Split a subtrace_set into partitions based on the label of the
   first entry in the subtrace
*)
let partition_by_head (st_set : subtrace_set) : subtrace_set OptLabelMap.t =
  SubtraceSet.fold (fun st partition_map ->
      let label = if List.length st.filter = 0 then None else
          match subtrace_nth st 0 with
          | AssignEntry (_, a, _) -> Some (aexpr_label a)
          | BranchEntry _ ->
            raise (InterferencePathFailure "subtrace contains a branch")
      in
      OptLabelMap.update label
        (function
          | None -> Some (SubtraceSet.singleton st)
          | Some st_set -> Some (SubtraceSet.add st st_set)
        ) partition_map
    ) st_set OptLabelMap.empty

(** given a subtrace, compute_leading_branches returns the set of branches
    that occur before the first assignment in the subtrace, mapped to
    their position in the trace *)
let compute_leading_branches (st : subtrace) : int BranchMap.t =
  let rec acc n =
    if n = List.nth st.filter 0 then BranchMap.empty else
      match List.nth st.underlying n with
      | AssignEntry(_, _, _) -> (acc (n + 1))
      | BranchEntry(_, _, b, _) -> BranchMap.add b n (acc (n + 1))
  in
  acc 0
    
(** intersects two branch->int maps, taking max values for vals *)
let intersect_leading_branches =
  BranchMap.merge (fun _ opt_fst opt_snd -> match opt_fst, opt_snd with
      | Some fst, Some snd -> Some (max fst snd)
      | _ -> None)

(**
   Given a partition of a subtrace_set, compute the last branch that
   traces from each part have in common
*)
let compute_splitting_branch (partition: subtrace_set OptLabelMap.t) : branch =
  let max_branch_map =
    OptLabelMap.map_reduce_nonempty
      (fun _ st -> compute_leading_branches (SubtraceSet.choose st))
      intersect_leading_branches
      partition
  in
  let max_branch, _ =
    BranchMap.map_reduce_nonempty
      (fun k v -> (k, v))
      (fun (k1, v1) (k2, v2) ->
         if v1 > v2 then (k1, v1) else (k2, v2))
      max_branch_map in
  max_branch

exception ProgrammerLogicError of string

(** looks up the passed branch in the passed trace, returning its position and
    direction *)
let find_branch_in_trace b tr =
  let rec acc n tr = 
    match tr with
    | AssignEntry(_, _, _) :: tr -> acc (n+1) tr
    | BranchEntry(_, deps, b', dir) :: tr ->
      if b = b' then n, deps, dir else acc (n+1) tr
    | [] -> raise (ProgrammerLogicError "the passed branch should be in the trace")
  in
  acc 0 tr
    
let check_pos_of_branch_in_st b st =
  let pos, _, _ = find_branch_in_trace b st.underlying in pos

let check_deps_of_branch_in_st b st =
  let _, deps, _ = find_branch_in_trace b st.underlying in deps

let check_dir_of_branch_in_st b st =
  let _, _, dir = find_branch_in_trace b st.underlying in dir

(**
   Given a subtrace_set, verify that all traces in it contain this branch
   and take it the same way, then return that way
*)
let check_dir_of_branch (b : branch) (st_set: subtrace_set) : bool =
  SubtraceSet.map_reduce_nonempty
    (fun st -> check_dir_of_branch_in_st b st)
    (fun b1 b2 -> if b1 = b2 then b1 else
        raise (ProgrammerLogicError "the passed branch should not split this class"))
    st_set

(** find the passed branch in each trace in subtrace, and return as a trace_pos *)
let extract_trace_pos_list (b : branch) (st_set : subtrace_set) : trace_pos list =
  SubtraceSet.fold (fun st ->
      List.cons {t = st.underlying;
                 pos = check_pos_of_branch_in_st b st})
    st_set
    []

let rec split_trace_pos {t=trace; pos=n} : trace * trace =
  if n = 0 then ([], trace) else
    let l, r = split_trace_pos {t=List.tl trace; pos=n-1} in
    List.hd trace :: l, r

(**
   Given a set of traces that all pass through a common point
   (identified by their pos in trace_pos), split into a set of traces
   leading up to that point and a set of traces including and following it
*)
let split_trace_pos_list (trace_pos_list : trace_pos list) :
  trace_set * trace_set =
  List.fold_right
    (fun tp (lset, rset) ->
       let l, r = split_trace_pos tp in
       (TraceSet.add l lset, TraceSet.add r rset))
    trace_pos_list
    (TraceSet.empty, TraceSet.empty)

let filter_explicit_traces (st_set : subtrace_set) : trace_set =
  SubtraceSet.fold
    (fun st ts -> if st.is_explicit then TraceSet.add st.underlying ts else ts)
    st_set TraceSet.empty
    
      
    
(**
   compute_trace_set computes the set of all program traces
   corresponding to the passed expression

   precondition: no function calls in e
   postcondition: all returned traces begin with the same entry (up to branch dir)
*)
let rec compute_trace_set: expr -> trace_set = function
  | Skip | Assert _ | AExp _ | FAssign (_, _) -> TraceSet.empty
    | Cond (c, et, ef, b) ->
      let branch_entry dir =
        BranchEntry(c, aexp_locals c, b, dir) in
      let ts_t = compute_trace_set et in
      let ts_f = compute_trace_set ef in
      TraceSet.union
        (TraceSet.map (List.cons (branch_entry true)) ts_t)
        (TraceSet.map (List.cons (branch_entry false)) ts_f)
    | Seq(e1, e2) ->
      let ts1 = compute_trace_set e1 in
      let ts2 = compute_trace_set e2 in
      TraceSet.prod List.append ts1 ts2
    | Assign (l, a) ->
      TraceSet.singleton ([AssignEntry(l, a, aexp_locals a)])
(**
   compute_subtrace_set maps each trace in t_set to a subtrace
   containing exactly the assignments that explicitly flow to one
   of the passed variables `tgts`.
   If `src` is concluded to flow to `tgts`, then `is_explicit` is
   set to true for that flow.

   pre/postcondition: (underlying) trace sets
      all begin with the same entry (up to branch dir)

   Step 1/3 in refine_trace_set
*)
let compute_subtrace_set (src : local) (tgts: local_set) :
  trace_set -> subtrace_set =
  let rec compute_subtrace_rec tr = (
    match tr with
    | [] -> [], 0, tgts
    | entry :: tr_tail ->
      let st_tail, pos, new_tgts = compute_subtrace_rec tr_tail in
      match entry with
      | AssignEntry(l, _, l_deps) ->
        if LocalSet.mem l new_tgts then
          (* this is an assignment to a local var that explicitly
             flows to our eventual targets *)
          pos :: st_tail, pos+1, LocalSet.union new_tgts l_deps
        else
          (* this is an assignment that does not explicitly
             flow to our targets *)
          st_tail, pos+1, new_tgts
      | BranchEntry(_, _, _, _) ->
        (* branches don't get included in subtraces *)
        st_tail, pos+1, new_tgts
  ) in
  let compute_subtrace tr =
    let st, _, new_tgts = compute_subtrace_rec tr in
    SubtraceSet.singleton {
      underlying = tr;
      filter = st;
      is_explicit = LocalSet.mem src new_tgts;
    }
  in
  TraceSet.map_reduce compute_subtrace SubtraceSet.union SubtraceSet.empty 


(**
   compute_branch_tree computes a prefix tree of the passed Sub.trace_set,
   annotating each node with the last branch point the two children traces
   have in common. That branch point is represented by pointers to its position
   in each underlying trace.

   Step 2/3 in refine_trace_set
*)
let rec compute_branch_tree (st_set: subtrace_set) : branch_tree =
  let partition = partition_by_head st_set in
  match OptLabelMap.cardinal partition with
  | 0 -> raise (ProgrammerLogicError "empty set of subtraces not expected")
  | 1 ->
    (* all subtraces begin the same way *)
    (match OptLabelMap.choose partition with
     | None, _ ->
       (* there are no remaining flowing assignments *)
       Leaf st_set
     | Some _, st_set ->
       (* all subtraces begin with the same assignment, so remove it and continue *)
       let st_tail_set = SubtraceSet.map (
           fun st -> {st with filter = List.tl st.filter}
         ) st_set in
       compute_branch_tree st_tail_set
    )
  | _ -> ( (* subtraces begin in different ways - create a branch node! *)
      let splitting_branch = compute_splitting_branch partition in
      let trace_pos_list = extract_trace_pos_list splitting_branch st_set in
      let pos_st_set, neg_st_set = SubtraceSet.partition
          (check_dir_of_branch_in_st splitting_branch)
          st_set in
      Branch(check_deps_of_branch_in_st
               splitting_branch (SubtraceSet.choose st_set),
             trace_pos_list,
             compute_branch_tree pos_st_set,
             compute_branch_tree neg_st_set)
    )

(**
   compute_interference_paths takes a branch tree and returns
   all underlying traces that correspond to interference paths.
   These can be either fully explicit, or implicit up to a point and then explicit.

   Step 3/3 in refine_trace_set   
*)
let rec compute_interference_paths (src: local) (bt : branch_tree) : trace_set =
  match bt with
  | Leaf st_set ->
    (* at leaves, we retain all explicit flows and discard all others *)
    filter_explicit_traces st_set
  | Branch(deps, trace_pos_list, l_branch_tree, r_branch_tree) ->
    (* at branches, we evaluate implicit flows by considering all
       flows to the deps of this branch (recursively obtained) adjoined
       to all explicit flows from the branch onwards
    *)
    let pre_flows, post_flows = split_trace_pos_list trace_pos_list in
    let pre_flows_refined = refine_trace_set src deps pre_flows in
    let implicit_flows = TraceSet.prod List.append pre_flows_refined post_flows in
    TraceSet.union implicit_flows
      (TraceSet.union
         (compute_interference_paths src l_branch_tree)
         (compute_interference_paths src r_branch_tree))

(**
   refine_trace_set takes a set of traces and returns only those corresponding
   to interference paths
*)
and refine_trace_set (src : local) (tgts : local_set) (ts : trace_set) : trace_set =
  ts
  |> compute_subtrace_set src tgts
  |> compute_branch_tree
  |> compute_interference_paths src

let compute_interference_flows (e : expr) (src: local) (tgt: local) : trace_set =
  refine_trace_set src (LocalSet.singleton tgt) (compute_trace_set e)
