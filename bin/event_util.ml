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

  let singleton = Set.singleton
end

(* though it should be the case that X ∨ X = X, don't try it for this implementation*)
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

    module LRUnion = Union(DepEvL)(DepEvR)

    module LSet = DepEvL.Set
    module RSet = DepEvR.Set
    module LRSet = DepEvLR.Set

    exception DependentEvNotDependent

    (**
       A dependent event build over a disjunction must resolve to a dependent
       event exclusively over one of the disjuncted modules.

       `resolve` follows from the definition of the hash function for a disjunction:
       elements of the respective modules always have distinct hashes
    *)
    let resolve : DepEvLR.t -> LRUnion.t = fun dep_lr ->
      let candidate_left, candidate_right =
        LRSet.fold (fun d (c_left, c_right) ->
            match d with
            | LRDisj.Left t -> (LSet.add t c_left, c_right)
            | LRDisj.Right t -> (c_left, RSet.add t c_right)
          ) dep_lr (LSet.empty, RSet.empty) in
      match (LSet.is_empty candidate_left, RSet.is_empty candidate_right) with
      | true, true -> Left (candidate_left) (*arbitrary_choice *)
      | false, false -> raise DependentEvNotDependent (*badly constructed*)
      | true, false -> Left (candidate_left)
      | false, true -> Right (candidate_right)

    module DepLRSet = Set(DepEvLR)
    module LRUnionSet = Set(LRUnion)
    module LRUnionMap = Map(LRUnion)

    let resolve_set : DepLRSet.t -> LRUnionSet.t =
      fun dep_lr_set ->
      DepLRSet.fold (compose resolve LRUnionSet.add) dep_lr_set LRUnionSet.empty
          

    (* these differ from LSet, RSet, LRSet by being sets of those *)
    module DepLSet = Set(DepEvL)
    module DepRSet = Set(DepEvR)

    (**
       `split_set` applies `resolve` to separate a set of disjucted dep evs 
    *)
    let split_set : DepLRSet.t -> DepLSet.t * DepRSet.t = 
      compose resolve_set LRUnion.splitSet
        
    (**
       `multiplex` combines providers from left and right dep evs into a
       provider for disjunct
    *)
    let multiplex :
      (DepEvL.t -> 'a) -> (DepEvR.t -> 'a) -> (DepEvLR.t -> 'a) =
      fun l_provider r_provider lr_request ->
      match resolve lr_request with
      | Left d -> l_provider d
      | Right d -> r_provider d

    let union_provide_dep : (LRUnion.t -> 'a) -> (DepEvLR.t -> 'a) =
      fun union_provider lr_request ->
      lr_request |> resolve |> union_provider

    let provide_from_union_map : ('a LRUnionMap.t) -> (DepEvLR.t -> 'a) =
      fun mp -> union_provide_dep (fun lr -> LRUnionMap.find lr mp)
  end
end

