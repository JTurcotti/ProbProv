open Expr
open Util

type local_set = LocalSet.t
type label_set = LabelSet.t

exception InterferencePathFailure of string
exception ProgrammerLogicError of string

let debug_output = ref false
let noop_formatter = Format.make_formatter
    (fun _ _ _ -> ()) (fun _ -> ())
let debug_formatter _ = if !debug_output then
    Format.std_formatter else noop_formatter

(**
   A trace_entry is either an assignment of a local to an
   aexp, with all locals mentioned in the aexp listed, or
   it is a branch on an aexp, with all locals similarly
   listed and the direction the branch took noted
*)
type trace_entry =
  | AssignEntry of local (* var assigned to *)
                   * aexp (* what expr is assigned *)
                   * local_set (* set of vars that aexp depends on *)
  | BranchEntry of aexp (* aexp branched on *)
                   * local_set (* set of vars that aexp depends on *)
                   * branch (* branch label *)
                   * bool (* how the branch is taken in this trace *)
  | ReturnEntry of aexp list (* list of aexps returned *)
                   * local_set list (* list of var dependencies for those aexps *)
  
  | Skip

let format_trace_entry ff = function
  | AssignEntry(Local s, a, _) ->
    Format.fprintf ff "[%s = %s] " s (Expr_repr.aexp_repr a)
  | BranchEntry(a, _, _, dir) ->
    Format.fprintf ff "[if %s:%b] " (Expr_repr.aexp_repr a) dir
  | ReturnEntry(alist, _) ->
    Format.fprintf ff "[ret %s] " (Expr_repr.aexp_reprs alist)
  | Skip ->
    Format.fprintf ff "[Skip]"

(**
   a `trace` is a list of trace_entry's - 
   represents a sequence of program expressions corresponding to a possible
   flow 
*)
type trace = trace_entry list

let format_trace ff trace =
  Format.fprintf ff "{";
  List.iter (format_trace_entry ff) trace;
  Format.fprintf ff "}"

(** a trace_pos is a trace along with an indexing int into it *)
type trace_pos = {t: trace; pos: int}

module TraceSet = Set(struct type t = trace end)
type trace_set = TraceSet.t

let format_trace_set = TraceSet.lift_format format_trace ",\n\t" "0"

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

let format_subtrace ff {underlying=t; filter=f; is_explicit=b} =
  Format.fprintf ff "%a[" format_trace t;
  List.iter (Format.fprintf ff "%d ") f;
  Format.fprintf ff "]%s" (if b then "E" else "")

let subtrace_nth st n =
  List.nth st.underlying (List.nth st.filter n)

module SubtraceSet = Set(struct type t = subtrace end)
type subtrace_set = SubtraceSet.t

let format_subtrace_set = SubtraceSet.lift_format format_subtrace ",\n\t" "0"

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
(**
   a suff_impl represents a sufficient condition for an implicit
   flow to occur: a list of branches that, if all are influenced
   by HIGH, the flow will reveal HIGH. Each branch is paired with
   the list of traces that reach it for ease of computation later.
*)
type suff_impl = (branch * (trace_pos list)) list

(** trace_labels takes a trace and returns the labels of all
    aexprs contained in the trace (useful for displaying trace)
*)
let rec trace_labels (t : trace) : label_set =
  match t with
  | [] -> LabelSet.empty
  | Skip :: t' -> trace_labels t'
  | AssignEntry(_, a, _) :: t'
  | BranchEntry(a, _, _, _) :: t'->
    LabelSet.union
      (aexpr_labels a)
      (trace_labels t')
  | [ReturnEntry(alist, _)] ->
    List.fold_right (compose aexpr_labels LabelSet.union) alist LabelSet.empty
  | ReturnEntry _ :: _ ->
    raise (ProgrammerLogicError "ReturnEntry should terminate trace")


module OptEntryMap = Map(struct type t = trace_entry option end)

let format_opt_entry ff = function
  | None -> Format.fprintf ff "none"
  | Some entry -> format_trace_entry ff entry

let format_partition =
  OptEntryMap.lift_format format_opt_entry format_subtrace_set ",\n\t" "0"

(**
   Split a subtrace_set into partitions based on the label of the
   first entry in the subtrace
*)
let partition_by_head (st_set : subtrace_set) : subtrace_set OptEntryMap.t =
  SubtraceSet.fold (fun st partition_map ->
      let head_entry = if List.length st.filter = 0 then None else
          match subtrace_nth st 0 with
          | BranchEntry _ ->
            raise (InterferencePathFailure "expected no branches in subtrace ")
          | entry -> Some entry
      in
      OptEntryMap.update head_entry
        (function
          | None -> Some (SubtraceSet.singleton st)
          | Some st_set -> Some (SubtraceSet.add st st_set)
        ) partition_map
    ) st_set OptEntryMap.empty

(** given a subtrace, compute_leading_branches returns the set of branches
    that occur in the trace, mapped to their position in the trace
*)
let compute_branches (t : trace) : int BranchMap.t =
  let rec acc n =
    if n = List.length t then BranchMap.empty else
      match List.nth t n with
      | BranchEntry(_, _, b, _) ->
        BranchMap.add b n (acc (n + 1))
      | _ -> acc (n + 1)
  in
  acc 0
    
(** intersects two of the maps used to compute splitting branches
    branches get given the largest position `n` of any subtrace
    they occur in, and their values `occ` are disjuncted together
    to aid reasoning in `compute_splitting_branch`
*)
let intersect_branch_maps = 
  BranchMap.merge (fun _ opt_fst opt_snd -> match opt_fst, opt_snd with
      | Some n1, Some n2 -> Some (max n1 n2)
      | _ -> None)
    
let last_common_branch trace1 trace2 : branch =
  let intersected = intersect_branch_maps
      (compute_branches trace1)
      (compute_branches trace2) in
  let (b, _) = BranchMap.fold (fun b n (b_prev, n_prev) ->
      if n > n_prev then (b, n) else (b_prev, n_prev))
      intersected (BranchMap.choose intersected) in
  b

(** looks up the passed branch in the passed trace, returning its position and
    direction *)
let find_branch_in_trace_opt b tr =
  let rec acc n tr = 
    match tr with
    | BranchEntry(_, deps, b', dir) :: tr ->
      if b = b' then Some (n, deps, dir) else acc (n+1) tr
    | _ :: tr -> acc (n + 1) tr
    | [] -> None
  in
  acc 0 tr

let find_branch_in_trace b tr =
  match find_branch_in_trace_opt b tr with
  | None ->  raise (ProgrammerLogicError "the passed branch should be in the trace")
  | Some v -> v

let check_pos_of_branch_in_trace b t =
  let pos, _, _ = find_branch_in_trace b t in pos

let check_deps_of_branch_in_trace b t =
  let _, deps, _ = find_branch_in_trace b t in deps

(** find the passed branch in each trace in subtrace, and return as a trace_pos *)
let extract_trace_pos_list (b : branch) (st_set : subtrace_set) : trace_pos list =
  SubtraceSet.fold (fun st ->
      match find_branch_in_trace_opt b st.underlying with
      | None -> id
      | Some (pos, _, _) ->
        List.cons {t = st.underlying;
                   pos = pos})
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

(* unused *)
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
let rec compute_trace_set : expr -> trace_set =
  function
  | Skip | Assert _ | AExp _ | FAssign (_, _) -> TraceSet.singleton [Skip]
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
  | Return alist ->
    TraceSet.singleton ([ReturnEntry(alist, List.map aexp_locals alist)])

(** we can search for either subtraces that flow to a return,
    or to a set of local variables - this type indicates that choice *)
type subtrace_type =
  | ReturnTrace of int
  | LocalTrace of local_set

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
let compute_subtrace_set (src : local) (tgt: subtrace_type)
    (ts : trace_set) : subtrace_set =
  Format.fprintf (debug_formatter ()) "\n<call compute_subtrace_set of: %a>\n"
      format_trace_set ts;
  let rec compute_subtrace_rec pos tr = (
    match tr, tgt with
    | [], LocalTrace local_tgts ->
      [], local_tgts
    | [ReturnEntry (_, ret_locals)], ReturnTrace n ->
      [pos], List.nth ret_locals n
    | entry :: tr_tail, _ -> (
      let st_tail, new_tgts = compute_subtrace_rec (pos + 1) tr_tail in
      match entry with
      | AssignEntry(l, _, l_deps) ->
        if LocalSet.mem l new_tgts then
          (* this is an assignment to a local var that explicitly
             flows to our eventual targets *)
          pos :: st_tail,
          LocalSet.union l_deps
            (LocalSet.remove l new_tgts)
        else
          (* this is an assignment that does not explicitly
             flow to our targets *)
          st_tail, new_tgts
      | BranchEntry(_, _, _, _) | Skip ->
        (* branches don't get included in subtraces *)
        st_tail, new_tgts
      | ReturnEntry _ ->
        raise (ProgrammerLogicError "return found in nonterminal position of trace"))
    | _ -> raise (ProgrammerLogicError "invalid call to compute_subtrace_set"))
  in
  let compute_subtrace tr =
    let st, new_tgts = compute_subtrace_rec 0 tr in
    SubtraceSet.singleton {
      underlying = tr;
      filter = st;
      is_explicit = LocalSet.mem src new_tgts;
    }
  in
  let subtraces = TraceSet.map_reduce
      compute_subtrace
      SubtraceSet.union
      SubtraceSet.empty ts in
  Format.fprintf (debug_formatter ()) "\n<result subtraces: %a>\n"
    format_subtrace_set subtraces;
  subtraces

(**
   Filter subtraces back down to only those containing explicit flows
*)
let compute_explicit_flows (st_set : subtrace_set) : trace_set =
  SubtraceSet.fold (fun st ->
      if st.is_explicit then TraceSet.add st.underlying else id)
    st_set TraceSet.empty

(* module QA(Arg: sig type q type a val ans: q -> a end) =
struct
  include Arg
  module QMap = Map(struct type t = q end)
  type state = a QMap.t

  let ask (s : state) (q : q) : state * a =
    match QMap.find_opt q s with
    | Some a -> (s, a)
    | None ->
      let a = (ans q) in
      (QMap.add q a s, a)
   end *)
  
(**
   Given a set of subtraces, determine the implicit flows
*)
let rec compute_implicit_flows src (st_set: subtrace_set) : trace_set = 
  let partition = partition_by_head st_set in
  match OptEntryMap.cardinal partition with
  | 0 -> raise (ProgrammerLogicError "empty set of subtraces not expected")
  | 1 ->
    (* all subtraces begin the same way *)
    (match OptEntryMap.choose partition with
     | None, _ ->
       (* there are no remaining flowing assignments so no implicit flows *)
       TraceSet.empty 
     | Some _, st_set ->
       (* all subtraces begin with the same assignment, so
          it's irrelevant to implicit flows: remove it and continue *)
       let st_tail_set = SubtraceSet.map (
           fun st -> {st with filter = List.tl st.filter}
         ) st_set in
       compute_implicit_flows src st_tail_set
    )
  | _ -> ( (* subtraces begin in different ways - there are implicit flows ! *)
      let implicit_flows_here =
        OptEntryMap.fold (fun k st_set1 ->
            OptEntryMap.fold (fun _ st_set2 ->
                (* st_set1 and st_set2 are sets of subtraces that yield
                   different explicit values, so figure out if this
                   yields any implicit flows *)
                SubtraceSet.fold (fun st1 ->
                    SubtraceSet.fold (fun st2 ->
                        TraceSet.union
                          (compute_trace_v_trace_implicit_flows
                             src st_set
                             st1.underlying
                             st2.underlying
                          )
                      ) st_set2
                  ) st_set1
              ) (OptEntryMap.remove k partition)
          ) partition TraceSet.empty in

      (* we now recursively join all explicit flows in subtrees of the
         prefix tree of explicitly flowing assignments to the implicit
         flows computed here *)
      OptEntryMap.fold (fun _ st_set ->
          TraceSet.union (compute_implicit_flows src st_set)
        ) partition
        implicit_flows_here
    )
    
(**
   Given that st1 and st2 yield different explicit values, compute
   all the resulting implicit flows. In particular, find the last branch
   at which they agree, and compute the explicit flows to the value
   that branch depends on (out of the set of all subtraces under consideration)
*)
and compute_trace_v_trace_implicit_flows src st_set trace1 trace2 : trace_set =
  (* find the last branch both traces took *)
  let lcb = last_common_branch trace1 trace2 in
  let (pos1, deps, _), (pos2, _, _) =
    find_branch_in_trace lcb trace1,
    find_branch_in_trace lcb trace2 in
  (* extract the portion of trace that occurred after that branch *)
  let (_, trace1_tail), (_, trace2_tail) =
    split_trace_pos {t=trace1; pos = pos1},
    split_trace_pos {t=trace2; pos = pos2} in

  (* extract the portion of all subtraces under consideration that leads
     up to this branch *)
  let prefix, _ = split_trace_pos_list (extract_trace_pos_list lcb st_set) in
  (* refine that set to just those that flow to the dependencies of the branch *)
  let refined_prefix =
    refine_trace_set src (LocalTrace deps) prefix in
  (* return all traces that lead up to the lcb, flow to the value it branches on,
     and then proceed as trace1 or trace2 do *)
  TraceSet.union
    (TraceSet.map (fun tr -> List.append tr trace1_tail) refined_prefix)
    (TraceSet.map (fun tr -> List.append tr trace2_tail) refined_prefix)

(**
   refine_trace_set takes a set of traces and returns only those corresponding
   to interference paths
*)
and refine_trace_set (src : local) (tgt : subtrace_type)
    (ts : trace_set) : trace_set =
  let subtraces = compute_subtrace_set src tgt ts in
  let implicit_flows = compute_implicit_flows src subtraces in
  let explicit_flows = compute_explicit_flows subtraces in
  TraceSet.union implicit_flows explicit_flows

(**
   compute the interference flows from the passed src to the indicated
   return number for a function with body e
*)
let compute_interference_flows (e : expr) (src: local) (which_ret: int) : trace_set =
  refine_trace_set src (ReturnTrace which_ret) (compute_trace_set e)
