open Expr
open Util

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

module AEEConjunctiveSet = Set(struct type t = atomic_external_event end)

(* aee conjunction utilities *)

let aee_one = AEEConjunctiveSet.empty
let aee_add = AEEConjunctiveSet.add
let aee_conj = AEEConjunctiveSet.union

type aee_conjunction = AEEConjunctiveSet.t

(* end aee conjunction utilities *)

module AEEDNFSet = Set(struct type t = aee_conjunction end)

(** an external event is a combination of atomic
    external events in DNF *)
type external_event = AEEDNFSet.t

(* external event utilities *)

(** the external event that always occurs *)
let external_event_one : external_event =
  AEEDNFSet.singleton aee_one

(** the external event that never occurs *)
let external_event_zero : external_event =
  AEEDNFSet.empty

(** conjunct a new atomic external event onto this external event *)
let external_event_conj aee ee : external_event =
  AEEDNFSet.map (aee_add aee) ee

(** disjunt together two external events *)
let rec external_event_disj ee1 ee2 =
  match AEEDNFSet.choose_opt ee1 with
  | None -> ee2
  | Some conj ->
    let ee1 = AEEDNFSet.remove conj ee1 in
    if AEEDNFSet.exists (fun conj2 -> aee_conj conj conj2 = conj) ee2 then
      (* conj subsumed by a clause already in ee2 *)
      external_event_disj ee1 ee2
    else
      external_event_disj ee1
        (AEEDNFSet.add conj
           (AEEDNFSet.filter (fun conj2 -> aee_conj conj conj2 <> conj2)
              ee2))

(* end external event utilities *)

(** an atomic_internal_event is a preference about how a branch is taken *)
type atomic_internal_event = AIE of branch * bool

(** an internal event is statement about branches being taken.
    Not present means "don't care"
    mapped to true means must be taken true
    mapped to false means must be taken false
*) 
type internal_event = bool BranchMap.t

(* internal event utilities *)

(** the internal event that "always occurs"
    -i.e. no branches have to be taken for it to occur *)
let internal_event_one : internal_event = BranchMap.empty

(** internal_event_conj returns the internal event that occurs
    if `ie` occurs and branch `br` is taken `dir`.

    If `ie` already states how `b` must be taken and it contradicts
    the passed `dir`, no event is returned *)
let internal_event_conj (AIE (br, dir)) ie : internal_event option =
  match BranchMap.find_opt br ie with
  | None -> Some (BranchMap.add br dir ie)
  | Some dir' ->
    if dir = dir' then Some ie else None

(** if (ie1 ∨ ie2) reduces to a simpler expression because they differ
    only by a single branch present in both, return the representation
    of that disjunction as a single internal event lacking that single
    branch *)
let internal_events_disj_reduce ie1 ee1 ie2 ee2
  : (internal_event * external_event) option =
  let diff_map = BranchMap.merge (fun _ b1 b2 ->
      match b1, b2 with
      | Some b1, Some b2 -> if b1 = b2 then None else Some 0b11
      | Some _, None -> Some 0b10
      | None, Some _ -> Some 0b01
      | _ -> None) ie1 ie2 in
  if BranchMap.for_all (fun _ presence -> presence = 0b10) diff_map &&
     external_event_disj ee1 ee2 = ee2
  then
    (* first event implies second event *)
    Some (ie2, ee2)
  else
  if BranchMap.for_all (fun _ presence -> presence = 0b01) diff_map &&
     external_event_disj ee1 ee2 = ee1
  then
    (* second event implies first event *)
    Some (ie1, ee1)
  else
  if ee1 <> ee2 || BranchMap.cardinal diff_map <> 1 then None else
    let diff_branch, presence = BranchMap.choose diff_map in
    if presence = 0b11 then Some (BranchMap.remove diff_branch ie1, ee1) else
      None

(* end internal event utilities *)

module IEMap = Map(struct type t = internal_event end)

(** an event is a set of sequences of branches (internal events),
    each associated with an external event.

    The interpretation is that an event "happens" iff, for any KV pair
    (internal, external) present, the internal event corresponds to
    a sequence of branches actually taken, and the external event occurs
    with appropriate probability independent of the internal event *)
type event = external_event IEMap.t

(* event utilities *)

let event_zero : event =
  IEMap.empty

(** the event that "always occurs" *)
let event_one : event =
  IEMap.singleton internal_event_one external_event_one

(* TODO: replace this equality checking of maps and sets with calls to
   compare functions - I have a bad feeling about this*)

let events_find_reduction event1 event2 =
  IEMap.fold (fun ie1 ee1 ->
      IEMap.fold (fun ie2 ee2 opt_out ->
          match opt_out with
          | Some v -> Some v
          | None ->
            match internal_events_disj_reduce ie1 ee1 ie2 ee2 with
            | None -> None
            | Some (ie, ee) -> Some (ie1, ie2, ie, ee)
        ) event2) event1 None

(** combines two events - result occurs if either of the sources do *)
let rec event_disj : event -> event -> event =
  fun e1 e2 ->
  match IEMap.choose_opt e1 with
  | None -> e2
  | Some (ie, ee) ->
    let e1' = IEMap.remove ie e1 in
    match events_find_reduction (IEMap.singleton ie ee) e2 with
    | None -> event_disj e1' (IEMap.add ie ee e2)
    | Some (_, ie2, ie, ee) ->
      event_disj e1' (event_disj (IEMap.singleton ie ee) (IEMap.remove ie2 e2))

(** conjuncts an event with a new atomic external event -
    result occurs if original occurs and atomic external event occurs *)
let event_external_conj aee : event -> event =
  IEMap.map (external_event_conj aee)

(** conjuncts an event with a new atomic internal event -
    result occurs if any case of the original occurs followed
    by the passed internal event *)
let event_internal_conj aie e : event =
  let build_new_event ie ext =
    match internal_event_conj aie ie with
    | Some ie' -> IEMap.add ie' ext
    | None -> id in
  IEMap.fold build_new_event e event_zero

exception BadPrecondition

(** returns the conjunction of two events
      Precondition: e1 contains no external events *)
let event_conj e1 e2 : event =
  let e2_with_ie ie =
    let acc_func br dir : event -> event = 
      event_internal_conj (AIE(br, dir)) in
    BranchMap.fold acc_func ie e2 in
  let acc_func ie ee : event -> event =
    if ee <> external_event_one then raise BadPrecondition else
      event_disj (e2_with_ie ie)
  in
  IEMap.fold acc_func e1 IEMap.empty


(** performs a merge of event options, doing either the trivial thing
    or applying event_disj if two non-empties are passed
    meant to be used in Map.Make().Merge *)
let merge_event_opts _ =
  double_option_map event_disj

let event_branch_conj br dir e =
  event_internal_conj (AIE(br, dir)) e

let branch_event br dir = event_branch_conj br dir event_one

let merge_events_across_branch br _ e1 e2 =
  if e1 = e2 then
    (* if we didn't handle this case separately,
         we'd still have a correct result, but a
         needlessly large and expanded one. This is why we don't
         use double_option_map*)
    e1
  else
    (event_disj
       (event_branch_conj br true e1)
       (event_branch_conj br false e2))

(** performs a merge of event options, first applying
    internal event conjunctions in accordance with the passed branch
    meant to be used in Map.Make().Merge (hence the ignored arg for
    the key being merged at) *)
let merge_event_opts_across_branch br _ op_e1 op_e2 =
  match (op_e1, op_e2) with
  | None, None -> None
  | Some e, None ->
    Some (event_internal_conj (AIE(br, true)) e)
  | None, Some e ->
    Some (event_internal_conj (AIE(br, false)) e)
  | Some e1, Some e2 ->
    Some (merge_events_across_branch br () e1 e2)

(**
   a touch_set computed for the positive (resp. negative)
   direction of a branch π (arg `br`) should have each of its blame
   events e expanded to πe ∨ π̅ (resp. π ∨ π̅e) to include the fact
   that if the branch is taken in the other direction, we have to
   pessimistically assume the touch occurred.
   This function applies that transformation in parallel to the
   passed events for true branch touch and false branch touch.
   It collapses the case of touch in both branches to `event_one`
*)
let merge_touch_event_opts_across_branch br _ opt_e1 opt_e2 =
  match (opt_e1, opt_e2) with
  | None, None ->
    (* var not touched in either branch *)
    None
  | Some e, None ->
    (* var touched only in true branch.
       if true branch taken, use the touch event,
       if false branch taken, pessismistically assume always touched *)
    Some (merge_events_across_branch br () e event_one)
  | None, Some e ->
    (* symmetric to true branch case *)
    Some (merge_events_across_branch br () event_one e)
  | Some _, Some _ ->
    (* most pessimistic case: always have to assume touched *)
    Some event_one

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

(** checks whether the passed site is a phantom return *)
let is_phantom_ret s =
  match s with
  | PhantomRetSite _ -> true
  | _ -> false

module SiteMap = Map(struct type t = site end)

(** a blame provides all the information one could care to know about
    provenance of a value - initially it is a very complex object but
    eventually it will just map LabelSites and ArgSites to [0, 1] numbers
    interpretation is that this blame object indicates a dependence on each site iff site is mapped to some event and that event occurs
*)
type blame = event SiteMap.t

(* blame utilities *)

(** no blame attributed for this value - "always correct" *)
let blame_zero : blame = SiteMap.empty

(** blame fully placed on the passed site *)
let blame_one a : blame = SiteMap.singleton a event_one

(** combine the blame from two sources -
    out blames a site iff either of the sources do *)
let blame_merge : blame -> blame -> blame =
  SiteMap.merge merge_event_opts

(** combines the blame from two sources, associating
    the first with the branch `br` being taken true,
    and the second with the branch `br` being taken false,
    prevents needlessly expanding terms *)
let blame_merge_across_branch br : blame -> blame -> blame =
  SiteMap.merge (merge_event_opts_across_branch br)

(** checks whether this blame object contains any phantom return
    - these should never be read or returned *)
let blames_phantom_ret b =
  let check site _ prev =
    prev || (is_phantom_ret site)
  in
  SiteMap.fold check b false


(** for every site blamed, conjuct its event with the passed
    atomic external event `aee` - yielding a new new blame
    conditioned on that event. This is used only for function calls *)
let blame_external_conj aee : blame -> blame =
  SiteMap.map (event_external_conj aee)

(** conjucts the event `e` into the event associated with
    every site of `b`.
    Precondition: e contains no external events
*)
let blame_event_conj b e : blame =
  SiteMap.map (event_conj e) b

(* end blame utilities *)

module LocalMap = Map(struct type t = local end)

(** this is our typing context! associating blame with local variables *)
type context = blame LocalMap.t

let context_lookup_ret (Ret(_, s)) = LocalMap.find (Local s)

exception PhantomRetLookedUpByLocal of local

(* context utilities *)


(*this module will use the functionality from refactor.ml to
  perform necessary simplifications of context elements *)
module Refactor =
struct
  (* external event refactorizer *)

  module EERefactorizer = Refactor.DoubleSet
      (AEEConjunctiveSet)
      (AEEDNFSet)
      (struct type t = atomic_external_event let neg (CallEvent(c, a, r, b)) = (CallEvent(c, a, r, not b)) end)

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

(** looks up the blame of variable x in context c if present
    and ensures it doesn't blame a phantom return *)
let context_lookup x c : blame option =
  match LocalMap.find_opt x c with
  | None -> None
  | Some b -> if blames_phantom_ret b then
      raise (PhantomRetLookedUpByLocal x) else
      Some b

(** returns a new context with local var x bound to blame b
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

let context_branch_conj branch dir : context -> context =
  LocalMap.map (SiteMap.map (event_branch_conj branch dir))

let context_merge : context -> context -> context =
  let merge_func _ =
    double_option_map blame_merge in
  LocalMap.merge merge_func

(* end context utilities *)
