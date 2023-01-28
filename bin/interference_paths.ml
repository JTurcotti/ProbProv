open Expr
open Typecheck
open Util

(**
   A trace_entry is either an assignment of a local to an
   aexp, with all locals mentioned in the aexp listed, or
   it is a branch on an aexp, with all locals similarly
   listed and the direction the branch took noted
*)
type trace_entry =
  | AssignEntry of local * aexp
  | BranchEntry of aexp * branch * bool

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
   indices of that trace identifying a subsequence of it
*)
type subtrace = {
  underlying: trace;
  filter: int list;
}

module SubtraceSet = Set(struct type t = subtrace end)
type subtrace_set = SubtraceSet.t

type branch_tree =
  | Branch of trace list * branch_tree * branch_tree
  | Leaf

(**
   compute_trace_set computes the set of all program traces
   corresponding to the passed expression

   precondition: no function calls in e
*)
let rec compute_trace_set: expr -> trace_set = function
  | Skip | Assert _ | AExp _ | FAssign (_, _) -> TraceSet.empty
    | Cond (c, et, ef, b) ->
      let branch_entry dir =
        BranchEntry(c, b, dir) in
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
      TraceSet.singleton ([AssignEntry(l, a)])
(**
   compute_sub_trace_set maps each trace in t_set to a Sub.trace
   based on the entries that explicitly flow to t_set.tgts

   Step 1/3 in refine_trace_set
*)
let compute_sub_trace_set (tgt : local) (t_set : trace_set) : subtrace_set = _


(**
   compute_branch_tree computes a prefix tree of the passed Sub.trace_set,
   annotating each node with the last branch point the two children traces
   have in common. That branch point is represented by pointers to its position
   in each underlying trace.

  Step 2/3 in refine_trace_set
*)
let compute_branch_tree (st_set: subtrace_set) : branch_tree = _


(**
   compute_interference_paths takes a branch tree and returns
   all underlying traces that correspond to interference paths.
   These can be either fully explicit, or implicit up to a point and then explicit.

   Step 3/3 in refine_trace_set   
*)
let compute_interference_paths  (src tgt : local) (bt : branch_tree) : trace_set = _

(**
   refine_trace_set takes a set of traces and returns only those corresponding
   to interference paths
*)
let refine_trace_set (src tgt : local) (t_set : trace_set) : trace_set =
  t_set
  |> compute_sub_trace_set tgt
  |> compute_branch_tree
  |> compute_inteference_paths src tgt

module TraceAnalyzer (Arg : sig val prog : typechecked_program end) =
struct
  include Arg

  let 

end
  
