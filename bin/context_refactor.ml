open Context

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
