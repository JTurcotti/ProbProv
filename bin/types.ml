open Expr

let double_option_bind combine opt1 opt2 =
  match (opt1, opt2) with
  | None, None -> None
  | Some v, None -> Some v
  | None, Some v -> Some v
  | Some v1, Some v2 -> Some (combine v1 v2)
    
type atomic_external_event =
  (* refers to the event of a function's return depending on its arg -
     int must be a distinct value for each call*)
    CallRetEvent of func * arg * ret * int

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

(* the event that "always occurs" *)
let event_one : event =
  IEMap.singleton internal_event_one external_event_one

(* combines two events - result occurs if either of the sources do *)
let event_disj : event -> event -> event =
  let merge_func _ =
    double_option_bind external_event_disj
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
  IEMap.fold build_new_event e event_one

(* returns the conjunction of two events
      Precondition: e2 contains no external events *)
let event_conj e1 e2 : event =
  let e1_with_ie ie =
    let acc_func br dir : event -> event = 
      event_internal_conj (AIE(br, dir)) in
    BranchMap.fold acc_func ie e1 in
  let acc_func ie ee : event -> event =
    if ee != external_event_one then exit(1) else
      event_disj (e1_with_ie ie)
  in
  IEMap.fold acc_func e2 IEMap.empty
  
  
(* performs a merge of event options, doing either the trivial thing
   or applying event_disj if two non-empties are passed
   meant to be used in Map.Make().Merge *)
let merge_event_ops _ =
  double_option_bind event_disj
    
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
           use double_option_bind*)
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
     by calling a function - int must be a distinct value
     for each call *)
  | CallRetSite of func * ret * int
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

let context_empty : context = LocalMap.empty

(* looks up the blame of variable x in context c if present
   and ensures it doesn't blame a phantom return *)
let context_lookup x c =
  match LocalMap.find_opt x c with
  | None -> None
  | Some b -> if blames_phantom_ret b then
      raise (PhantomRetLookedUpByLocal x) else
      Some b

exception PhantomRetAssignedIntoLocal of local

(* returns a new context with local var x bound to blame b
   in c, ensures b doesn't blame a phantom return *)
let context_bind x b c =
  if blames_phantom_ret b then
    raise (PhantomRetAssignedIntoLocal x)
  else 
    LocalMap.add x b c

let context_merge : context -> context -> context =
  let merge_func _ =
    double_option_bind blame_merge in
  LocalMap.merge merge_func

let context_merge_across_branches br : context -> context -> context =
  let merge_func _ =
    double_option_bind (blame_merge_across_branch br) in
  LocalMap.merge merge_func

(* end context utilities *)

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
    context_bind x (blame_event_conj b e) 
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
    (context_merge c_t
       (assoc_touch_set_with_blame (compute_touch_set e_t) b_br))
    (context_merge c_f
       (assoc_touch_set_with_blame (compute_touch_set e_f) b_br))

