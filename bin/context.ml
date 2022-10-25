open Expr

let double_option_map combine opt1 opt2 =
  match (opt1, opt2) with
  | None, None -> None
  | Some v, None -> Some v
  | None, Some v -> Some v
  | Some v1, Some v2 -> Some (combine v1 v2)

type atomic_external_event =
  (* refers to the event of a function's return depending on its arg (
     or if it doesn't depend on its arg and `bool` is false) - 
     `call` identifies both a function at the specific callsite
  *)
    CallEvent of call * arg * ret * bool

module AEEOrdered = struct
  type t = atomic_external_event
  let compare = Stdlib.compare
end
module AEEConjunctiveSet = Set.Make(AEEOrdered)

(* aee conjunction utilities *)

let aee_one = AEEConjunctiveSet.empty
let aee_conj = AEEConjunctiveSet.add

(* end aee conjunction utilities *)

module AEEConjunctiveSetOrdered = struct
  type t = AEEConjunctiveSet.t
  let compare = Stdlib.compare
end
module AEEDNFSet = Set.Make(AEEConjunctiveSetOrdered)

(* an external event is a combination of atomic
   external events in DNF *)
type external_event = AEEDNFSet.t

(* external event utilities *)

(* the external event that always occurs *)
let external_event_one : external_event =
  AEEDNFSet.singleton aee_one

(* the external event that never occurs *)
let external_event_zero : external_event =
  AEEDNFSet.empty

(* conjunct a new atomic external event onto this external event *)
let external_event_conj aee ee : external_event =
  AEEDNFSet.map (aee_conj aee) ee

(* disjunt together two external events *)
let external_event_disj = AEEDNFSet.union

(* end external event utilities *)

module BranchOrdered = struct
  type t = branch
  let compare = Stdlib.compare
end
module BranchMap = Map.Make(BranchOrdered)

(* an atomic_internal_event is a preference about how a branch is taken *)
type atomic_internal_event = AIE of branch * bool

(* an internal event is statement about branches being taken.
   Not present means "don't care"
   mapped to true means must be taken true
   mapped to false means must be taken false
*) 
type internal_event = bool BranchMap.t

(* internal event utilities *)

(* the internal event that "always occurs"
   -i.e. no branches have to be taken for it to occur *)
let internal_event_one : internal_event = BranchMap.empty

exception BranchAlreadyPresentInEvent of branch
(* return the internal event that occurs if `ie` occurs and
   branch `br` is taken `dir`. Throws an exception of `ie`
   already states how `b` must be taken*)
let internal_event_conj (AIE (br, dir)) ie : internal_event =
  let () = if BranchMap.mem br ie then
      raise (BranchAlreadyPresentInEvent br) else () in
  BranchMap.add br dir ie
(* end internal event utilities *)

module IEKey = struct
  type t = internal_event
  let compare = Stdlib.compare
end
module IEMap = Map.Make(IEKey)

(* an event is a set of sequences of branches (internal events),
   each associated with an external event.

   The interpretation is that an event "happens" iff, for any KV pair
   (internal, external) present, the internal event corresponds to
   a sequence of branches actually taken, and the external event occurs
   with appropriate probability independent of the internal event *)
type event = external_event IEMap.t

(* event utilities *)

let event_zero : event =
  IEMap.empty

(* the event that "always occurs" *)
let event_one : event =
  IEMap.singleton internal_event_one external_event_one

(* combines two events - result occurs if either of the sources do *)
let event_disj : event -> event -> event =
  let merge_func _ =
    double_option_map external_event_disj
  in
  IEMap.merge merge_func

(* conjuncts an event with a new atomic external event -
   result occurs if original occurs and atomic external event occurs *)
let event_external_conj aee : event -> event =
  IEMap.map (external_event_conj aee)

(* conjuncts an event with a new atomic internal event -
   result occurs if any case of the original occurs followed
   by the passed internal event *)
let event_internal_conj aie e : event =
  let build_new_event ie =
    (IEMap.add (internal_event_conj aie ie)) in
  IEMap.fold build_new_event e event_zero

exception BadPrecondition

(* returns the conjunction of two events
      Precondition: e1 contains no external events *)
let event_conj e1 e2 : event =
  let e2_with_ie ie =
    let acc_func br dir : event -> event = 
      event_internal_conj (AIE(br, dir)) in
    BranchMap.fold acc_func ie e2 in
  let acc_func ie ee : event -> event =
    if ee != external_event_one then raise BadPrecondition else
      event_disj (e2_with_ie ie)
  in
  IEMap.fold acc_func e1 IEMap.empty


(* performs a merge of event options, doing either the trivial thing
   or applying event_disj if two non-empties are passed
   meant to be used in Map.Make().Merge *)
let merge_event_ops _ =
  double_option_map event_disj

(* performs a merge of event options, first applying
   internal event conjunctions in accordance with the passed branch
   meant to be used in Map.Make().Merge *)
let merge_event_ops_across_branch br _ op_e1 op_e2 =
  match (op_e1, op_e2) with
  | None, None -> None
  | Some e, None ->
    Some (event_internal_conj (AIE(br, true)) e)
  | None, Some e ->
    Some (event_internal_conj (AIE(br, false)) e)
  | Some e1, Some e2 ->
    if e1 = e2 then
      (* if we didn't handle this case separately,
         we'd still have a correct result, but a
         needlessly large and expanded one. This is why we don't
         use double_option_map*)
      Some e1
    else
      Some (event_disj
              (event_internal_conj (AIE(br, true)) e1)
              (event_internal_conj (AIE(br, false)) e2))

(* end event utilities *)

type site =
  (* these sites represent source positions of AST nodes *)
  | LabelSite of label
  (* these sites represent a stand-in for the blame created
     by calling a function at the site `call` *)
  | CallSite of call * ret
  (* these sites represent the arguments passed to our function *)
  | ArgSite of arg
  (* these sites represent the return variables; "initial values" -
     they must not be present at the end of the function *)
  | PhantomRetSite of ret

(* checks whether the passed site is a phantom return *)
let is_phantom_ret s =
  match s with
  | PhantomRetSite _ -> true
  | _ -> false

module SiteKey = struct
  type t = site
  let compare = Stdlib.compare
end
module SiteMap = Map.Make(SiteKey)

(* a blame provides all the information one could care to know about
   provenance of a value - initially it is a very complex object but
   eventually it will just map LabelSites and ArgSites to [0, 1] numbers
   interpretation is that this blame object indicates a dependence on each site iff site is mapped to some event and that event occurs
*)
type blame = event SiteMap.t

(* blame utilities *)

(* no blame attributed for this value - "always correct" *)
let blame_zero : blame = SiteMap.empty

(* blame fully placed on the passed site *)
let blame_one a : blame = SiteMap.singleton a event_one

(* combine the blame from two sources -
   out blames a site iff either of the sources do *)
let blame_merge : blame -> blame -> blame =
  SiteMap.merge merge_event_ops

(* combines the blame from two sources, associating
   the first with the branch `br` being taken true,
   and the second with the branch `br` being taken false,
   prevents needlessly expanding terms *)
let blame_merge_across_branch br : blame -> blame -> blame =
  SiteMap.merge (merge_event_ops_across_branch br)

(* checks whether this blame object contains any phantom return
   - these should never be read or returned *)
let blames_phantom_ret b =
  let check site _ prev =
    prev || (is_phantom_ret site)
  in
  SiteMap.fold check b false


(* for every site blamed, conjuct its event with the passed
   atomic external event `aee` - yielding a new new blame
   conditioned on that event. This is used only for function calls *)
let blame_external_conj aee : blame -> blame =
  SiteMap.map (event_external_conj aee)

(* conjucts the event `e` into the event associated with
   every site of `b`.
   Precondition: e contains no external events
*)
let blame_event_conj b e : blame =
  SiteMap.map (event_conj e) b

(* end blame utilities *)

module LocalKey = struct
  type t = local
  let compare = Stdlib.compare
end
module LocalMap = Map.Make(LocalKey)

(* this is our typing context! associating blame with local variables *)
type context = blame LocalMap.t

exception PhantomRetLookedUpByLocal of local

(* context utilities *)


(*this module will use the functionality from refactor.ml to
  perform necessary simplifications of context elements *)
module Refactor =
struct
  (* external event refactorizer *)

  module AEEDNFOps =
  struct
    type elt = atomic_external_event
    type t = external_event
    let conj_pos = external_event_conj
    let conj_neg (CallEvent(c, a, r, b)) =
      external_event_conj (CallEvent(c, a, r, not b))
    let disj = external_event_disj
    let one = external_event_one
    let zero = external_event_zero
  end

  module EERefactorizer = Refactor.Refactorizer
      (AEEConjunctiveSet)
      (AEEDNFSet)
      (AEEDNFOps)

  let refactorize_external_event : external_event -> external_event
    = EERefactorizer.build

  (* end external event refactorizer *)

  (* event refactorizer *)

  let refactorize_event : event -> event
    = IEMap.map refactorize_external_event

  (* end event refactorizer *)

  (* blame refactorizer *)

  let refactorize_blame : blame -> blame
    = SiteMap.map refactorize_event

  (* end blame refactorizer *)

  (* context refactorizer *)

  let refactorize_context : context -> context
    = LocalMap.map refactorize_blame

  (* end context refactorizer *)

  (* FOLLOWING FUNCTIONS DEAL WITH CONTEXT REDUCTION *)

  (* This ensures that disjunctions of A and B, where A implies B,
     are reduced to just A*)
  let external_event_reduce =
    EERefactorizer.eliminate_subsumption

  (* when we implement an IERefactorizer, this will be used as
     a key component of the subset relation on internal events
     when you do this, choose it carefully
  *)
  let submap m1 m2 =
    BranchMap.fold (fun k v bool ->
        bool && (
          match BranchMap.find_opt k m2 with
          | Some v2 -> v2 = v
          | None -> false)) m1 true

  let event_reduce event =
    let event2 = IEMap.map external_event_reduce event in
    event2

  let blame_reduce blame =
    let blame2 = SiteMap.map event_reduce blame in
    blame2

  let context_reduce context =
    let context2 = LocalMap.map blame_reduce context in
    context2
end

let context_empty : context = LocalMap.empty

(* looks up the blame of variable x in context c if present
   and ensures it doesn't blame a phantom return *)
let context_lookup x c : blame option =
  match LocalMap.find_opt x c with
  | None -> None
  | Some b -> if blames_phantom_ret b then
      raise (PhantomRetLookedUpByLocal x) else
      Some b

(* returns a new context with local var x bound to blame b
   in c *)
let context_assign : local -> blame -> context -> context = LocalMap.add

let context_blames_phantom_ret c =
  LocalMap.fold (fun _ b blames ->
      blames || (blames_phantom_ret b)) c false

let filter_phantom_ret c =
  if (context_blames_phantom_ret c) then None else Some c

let filter_to_ret_sites fdecl =
  let is_ret_local (Local(x)) =
    List.fold_right
      (fun (Ret(_, ret)) x_is_ret -> x_is_ret || x = ret) fdecl.results false
  in
  LocalMap.filter (fun x _ -> is_ret_local x)

let context_assign_zero x c =
  context_assign x blame_zero c

let context_merge : context -> context -> context =
  let merge_func _ =
    double_option_map blame_merge in
  LocalMap.merge merge_func

let context_merge_across_branches br : context -> context -> context =
  let merge_func _ =
    double_option_map (blame_merge_across_branch br) in
  LocalMap.merge merge_func

(* maps variables to events corresponding to the event under
   which that variable is "touched" i.e. assigned to.
   There should be NO EXTERNAL EVENTS included in the values of
   this mapping.
*)
type touch_set = event LocalMap.t

(* computes the touch set for an expression *)
let rec compute_touch_set (e : expr) =
  match e with
  | Cond (_, e_t, e_f, b) -> 
    LocalMap.merge (merge_event_ops_across_branch b)
      (compute_touch_set e_t) (compute_touch_set e_f)
  | Assign (x, _) -> LocalMap.singleton x event_one
  | Seq (e1, e2) ->
    LocalMap.merge merge_event_ops
      (compute_touch_set e1) (compute_touch_set e2)
  | _ -> LocalMap.empty                       


(* returns a new context in which every variable from a passed
   touch set `ts` is associated with a certain blame, conjuncted
   site-wise with the event determined by the touch set.
   This reflects part of the semantics of branch unification.
*)
let assoc_touch_set_with_blame ts b : context =
  let acc x e =
    context_assign x (blame_event_conj b e) 
  in
  LocalMap.fold acc ts context_empty

(* this context merge fully captures the semantics of conditionals:
   each branch's context (`c_t`, `c_f`) is first conjuncted with
   the touch set for that branch's expression (`e_t`, `e_f`),
   associated with the blame for the branching guard (`b_br`), and
   then the two results are merge across the branch `br`
*) 
let context_merge_cond br b_br e_t e_f c_t c_f : context =
  context_merge_across_branches br
    (Refactor.context_reduce
       (context_merge c_t
          (assoc_touch_set_with_blame (compute_touch_set e_t) b_br)))
    (Refactor.context_reduce
       (context_merge c_f
          (assoc_touch_set_with_blame (compute_touch_set e_f) b_br)))


(* end context utilities *)
