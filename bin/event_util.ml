open Util

(**
   This represents a type t that comes with a hash.
   The hash should represent indendence classes:
   two events of type t are independent iff their hashs differ
*)
module type DepHashT =
sig
  type t
  type hash_t
  val hash : t -> hash_t
end

(** type of events t with a negation operator neg *)
module type Neg =
sig
  type t
  val neg : t -> t
end


(** intersects Neg and DepHashT *)
module type NegHashT =
sig
  include Neg
  include DepHashT with type t := t
end

(**
   this is used to model a conjunction of dependent events
   dependence is encoded in the hases of the events - which
   must all be equal. An assert_dep function is provided
   to help enforce this at runtime
*)
module DependentEv(T : DepHashT) =
struct
  module Elt = T
  
  module Set = Set(T)

  type t = Set.t
  type elt = Elt.t

  let singleton x =
    Set.singleton x

  (**
     this verifies that all events are indeed dependent (hash-constant)
     If this check were relaxed, spurious queries across computation layers
     would be made
  *)
  let verify_dep de =
    match Set.choose_opt de with
    | None -> true (*empty event - vacuosly verified *)
    | Some x -> let hash = Elt.hash x in
      Set.for_all (fun x -> Elt.hash x = hash) de

  exception NotDependent

  let assert_dep de =
    if verify_dep de then () else raise NotDependent
end

module DependentDisj (L : DepHashT) (R : DepHashT) =
struct
  module LRDisj =
  struct
    type t = Left of L.t |
             Right of R.t 
                      
    type hash_t = HLeft of L.hash_t |
                HRight of R.hash_t
                            
    let hash = function
      | Left t -> HLeft (L.hash t)
      | Right t -> HRight (R.hash t)
  end

  include LRDisj

  module DependentEvUtils =
  struct
    module DepEvL = DependentEv(L)
    module DepEvR = DependentEv(R)
    module DepEvLR = DependentEv(LRDisj)

    type outer_disj = Left of DepEvL.t | Right of DepEvR.t

    (**
       A dependent event build over a disjunction must resolve to a dependent
       event exclusively over one of the disjuncted modules.

       `resolve` follows from the definition of the hash function for a disjunction:
       elements of the respective modules always have distinct hashes
    *)
    let resolve : DepEvLR.t -> outer_disj = _

    (**
       `split_set` applies `resolve` to separate a set of disjucted dep evs 
    *)
    let split_set : Set(DepEvLR).t -> Set(DepEvL).t * Set(DepEvR).t = _


    (**
       `multiplex` combines providers from left and right dep evs into a
       provider for disjunct
    *)
    let multiplex :
      (DepEvL.t -> 'a) -> (DepEvR.t -> 'a) -> (DepEvLR.t -> 'a) = _
  end
end
                            
