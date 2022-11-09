open Util
open Event_util

module type SetLike =
sig
  type elt

  type t

  val fold: (elt -> 'a -> 'a) -> t -> 'a -> 'a

  val mem: elt -> t -> bool

  val remove: elt -> t -> t

  val is_empty: t -> bool

  val empty: t

  val union: t -> t -> t

  val partition: (elt -> bool) -> t -> t * t

  val map: (elt -> elt) -> t -> t

  val filter: (elt -> bool) -> t -> t

  val singleton: elt -> t

  val add: elt -> t -> t

  val cardinal: t -> int

  val choose: t -> elt

  val for_all: (elt -> bool) -> t -> bool

  val exists: (elt -> bool) -> t -> bool

  (* be careful with this - definition should correspond to event implication *)
  val subset: t -> t -> bool

  val map_reduce: (elt -> 'a) -> ('a -> 'a -> 'a) -> 'a -> t -> 'a

  val lift_format:
    (Format.formatter -> elt -> unit) -> string -> string ->
    (Format.formatter -> t -> unit)
end

(*
module type EventLike =
sig
  type t

  type event

  val conj: event -> event -> event
  val disj: event -> event -> event
  val pos: t -> event
  val neg: t -> event
  val one: event

  val destruct :
    conj:(event -> event -> 'a) ->
    disj:(event -> event -> 'a) ->
    pos:(t -> 'a) ->
    neg:(t -> 'a) ->
    one:'a ->
    event -> 'a
end

module type Formatter =
sig
  type t
  val repr : t -> string
end


module EventFormatter
    (Event : EventLike)
    (F: Formatter with type t = Event.t) : Formatter = 
struct
  type t = Event.event
  let rec repr event =
    let conj e1 e2 =
      Printf.sprintf "%s%s" (repr e1) (repr e2) in
    let disj e1 e2 =
      Printf.sprintf "(%s + %s)" (repr e1) (repr e2) in
    let pos = F.repr in
    let neg t = Printf.sprintf "%s%s" (F.repr t) unicode_bar in
    let one = "𝟙" in
    Event.destruct ~conj ~disj ~pos ~neg ~one event
end

module TEvent (T: sig type t end) =
struct
  type t = T.t
  type event =
    | Conj of event * event
    | Disj of event * event
    | Pos of t
    | Neg of t
    | One

  let conj e1 e2 = Conj(e1, e2)
  let disj e1 e2 = Disj(e1, e2)
  let pos e = Pos(e)
  let neg e = Neg(e)
  let one = One
  let destruct ~conj ~disj ~pos ~neg ~one =
    function
    | Conj(e1, e2) -> conj e1 e2
    | Disj(e1, e2) -> disj e1 e2
    | Pos(t) -> pos t
    | Neg(t) -> neg t
    | One -> one
end
*)

(*
   A DoubleSet gives DNF semantics to two nested set modules
   *)
module DoubleSet
    (InnerSet : SetLike)
    (OuterSet : SetLike with type elt = InnerSet.t)
    (Neg : Neg
     with type t = InnerSet.elt) =
struct
  module InnerSet = InnerSet
  module OuterSet = OuterSet

  type elt = InnerSet.elt
  type iset = InnerSet.t
  type oset = OuterSet.t
  type t = oset

  let zero = OuterSet.empty
  let one = OuterSet.singleton (InnerSet.empty)

  let is_zero = OuterSet.is_empty
  let is_one dnf = OuterSet.cardinal dnf = 1 &&
                   InnerSet.is_empty (OuterSet.choose dnf)

  let singleton : elt -> oset = fun e ->
    OuterSet.singleton (InnerSet.singleton e)

  let disj = OuterSet.union
  let conj : oset -> oset -> oset = fun o1 o2 -> (
      let add_i_to_o i o =
        OuterSet.map (InnerSet.union i) o in
      OuterSet.fold (fun i -> OuterSet.union (add_i_to_o i o2)) o1 OuterSet.empty)

  let conj_elt : elt -> oset -> oset = fun e o ->
    conj (singleton e) o

  let neg_elt : elt -> elt = Neg.neg

  let singleton_neg : elt -> oset = compose neg_elt singleton

  let neg : oset -> oset = fun oset ->
    let neg_iset : iset -> oset = fun iset ->
      InnerSet.fold (compose singleton_neg disj) iset zero in
    OuterSet.fold (compose neg_iset conj) oset one

  let repr elt_repr combine_conj combine_disj oset =
    let iset_repr iset =
      if InnerSet.is_empty iset then "1" else
        InnerSet.fold (compose elt_repr (Printf.sprintf combine_conj)) iset "" in
    OuterSet.fold (compose iset_repr (Printf.sprintf combine_disj)) oset ""

  (* this function ensures that no two innersets A, B remain that satisfy
     InnerSet.subset A B - it does this by removing the larger one *)
  let eliminate_subsumption (oset : oset) : oset =
    let not_subsumed iset =
      OuterSet.fold (fun iset2 bool ->
          bool &&
          not (InnerSet.subset iset2 iset))
        (OuterSet.remove iset oset) true in
    OuterSet.filter not_subsumed oset

  (* goal for `slice` is to choose an atomic event a, and return b and c such that
     the passed event can be expressed as (a ∧ b) ∨ c.
     `build`'s job below is then to ask for this slice of some event E, and
     replace E with (a ∧ build(b ∨ c)) ∨ (ā ∧ build(c)) (note the recursive calls).
     (a ∧ (b ∨ c)) ∨ (ā ∧ c) is equivalent to (a ∧ b) ∨ c, but much easier to compute
     because the components of the top disjunction are exclusive.

     open questions:
     -general: is there a better way to do this?
     -maybe independence helps?

  *)
  let slice : oset -> (elt * oset * oset) option = fun oset ->
    let union_all = OuterSet.fold InnerSet.union oset InnerSet.empty in
    let (a_opt, _) =
      InnerSet.fold (fun t (best_t, best_t_cnt) ->
          let t_cnt = OuterSet.fold (fun iset cnt ->
              cnt + if InnerSet.mem t iset then 1 else 0) oset 0 in
          if t_cnt > best_t_cnt then
            (Some t, t_cnt) else
            (best_t, best_t_cnt)
        ) union_all (None, 0) in
    match a_opt with
    | None -> None
    | Some a ->
      let b_fat, c = OuterSet.partition (InnerSet.mem a) oset in
      let b = OuterSet.map (InnerSet.remove a) b_fat in
      Some (a, b, c)

  exception UnexpectedBranchInMakeComputable

  let is_computable (oset: oset) : bool =
    OuterSet.for_all (fun fst ->
        OuterSet.for_all (fun snd ->
            InnerSet.exists (fun i_fst ->
                InnerSet.exists (fun i_snd ->
                    i_fst = (neg_elt i_snd) &&
                    i_snd = (neg_elt i_fst)
                  ) snd
              ) fst
          ) (OuterSet.remove fst oset)
      ) oset

  exception MakeComputableFailed

  (**
     If called on an oset representing an arbitrary DNF, `make_computable`
     will return an event-equivalent DNF in which the conjunctions are
     guaranteed not to pairwise co-occur. We call these "conjunction-coexclusive"
     DNFs
     **)
  let rec make_computable (oset : oset) : oset =
    if is_zero oset then zero else
    if is_one oset then one else
      match slice oset with
      | None -> raise UnexpectedBranchInMakeComputable
      | Some (a, b, c) ->
        let computable = disj
          (conj_elt a
             (* we call eliminate_subsumption here because the mapped removal
                  can introduce new subsumption (e.g. under remove a: a + b ↦ 1 + b)
                  or the union with b after the mapped removal, and it is vital that
                  we recur into as small an object as possible *)
             (make_computable (eliminate_subsumption (disj b c))))
          (conj_elt (neg_elt a)
             (make_computable c)) in
        if is_computable computable then computable else
          (* TODO: remove this once it's been passing for a while *)
          raise MakeComputableFailed
end

type 't derived_t = {el: 't; ind: int; sgn: bool}

module Derived (T : DepHashT) =
struct
  module D =
  struct
    type t = T.t derived_t

    let neg t = {el=t.el; ind=t.ind; sgn=not t.sgn}

    module HashT = struct type t = T.hash_t * int end
    type hash_t = HashT.t
    let hash t = (T.hash t.el, t.ind)

    let lift_format (t_format : Format.formatter -> T.t -> unit) :
      Format.formatter -> t -> unit =
      fun ff {el=el; ind=ind; sgn=sgn} ->
      Format.fprintf ff "%s" (
        (Format.asprintf "⟦%c%a⟧%s" (if sgn then '+' else '-') t_format el
           (Expr_repr.int_subscript_repr ind)))
  end

  include D

  (* we consider dependent events over Derived Ts to access
     their assertion of hash-constancy before erasure
  *)
  module Dep = DependentEv(D)
  module S = Set(T)

  (* this can be called to lower a set of hash-constant derived events to
     a set of the underlying events - assertion of hash-constancy is crucial*)
  let lower_to_set : Dep.t -> S.t = fun de ->
    let () = Dep.assert_dep de in
    Dep.Set.fold (fun d -> S.add d.el) de S.empty
end

type 't dnf_t = 't derived_t s_constr s_constr

module DerivedDoubleSet (T : DepHashT) =
struct
  module D = Derived(T)
  module DNF = DoubleSet (Set(D)) (Set(Set(D))) (D)

  type elt = T.t

  let dnf_lift_format t_format : Format.formatter -> DNF.t -> unit =
    DNF.OuterSet.lift_format
      (DNF.InnerSet.lift_format (D.lift_format t_format) "" "𝟙") " + " "𝟘"


  module DepEv = DependentEv(T)

  module ArithSynth (A : Arithmetic) =
  struct

    (**
       a synthesizer is structurally equivalent to an AST over DepEv's
       it takes a source of A.t values for DepEv "variables", and combines
       them according to A's operations
    *)
    type synthesizer =
      (DepEv.t -> A.t) -> A.t
    type synth = synthesizer


    module DepEvSet = Set(DepEv)
    module DepEvMap = Map(DepEv)

    (** a req_synth combines a synthesizer with its requirements for
        successful computation *)
    type req_synth = DepEvSet.t * synth
                     
    let synth_mult : req_synth -> req_synth -> req_synth =
      fun (r1, s1) (r2, s2) ->
      (DepEvSet.union r1 r2, fun provider ->
          A.mult (s1 provider) (s2 provider))

    let synth_add : req_synth -> req_synth -> req_synth =
      fun (r1, s1) (r2, s2) ->
      (DepEvSet.union r1 r2, fun provider ->
          A.add (s1 provider) (s2 provider))

    let synth_sub : req_synth -> req_synth -> req_synth =
      fun (r1, s1) (r2, s2) ->
      (DepEvSet.union r1 r2, fun provider ->
          A.sub (s1 provider) (s2 provider))



    let synth_one : req_synth = (DepEvSet.empty, fun _ -> A.one)
    let synth_zero : req_synth = (DepEvSet.empty, fun _ -> A.zero)

    let synth_var : DepEv.t -> req_synth = fun d ->
      if DepEv.Set.is_empty d then synth_one else
        (DepEvSet.singleton d, fun provider -> provider d)

    module DHashMap = Map(D.HashT)

    module EvMap = Map(DepEv.Elt)

    (**
       For pos_elems = {A, B, C} and neg_elems = {D, E, F} this
       should return ABC + ABCD̄ + ABCĒ + ABDF̄ - ABCĒF̄ - ABCD̄F̄ - ABCD̄Ē + ABCD̄ĒF̄
       which is the PIE expansion of ABC ∧ ~(DEF)
       *)
    let synth_pie : DepEv.t -> DepEv.t -> req_synth =
      fun pos_elems neg_elems ->
      if not (DepEv.is_empty (DepEv.inter pos_elems neg_elems)) then
        (* event is impossible *)
        synth_zero
      else

        (* precondition: ev not already in signed_conj *)
        let include_neg_event ev signed_conj =
          DepEvMap.fold (fun conj_ev sgn ->
              DepEvMap.add (DepEv.add ev conj_ev) (not sgn)
            ) signed_conj signed_conj in
        
        let pie_expansion = DepEv.fold include_neg_event
            neg_elems (DepEvMap.singleton pos_elems true) in
        
        DepEvMap.map_reduce
          (fun conj_ev sgn ->
             if sgn then (synth_var conj_ev) else
               (synth_sub synth_zero (synth_var conj_ev)))
          synth_add synth_zero pie_expansion
          
    (** `separate` takes a DNF and expresses it as a sum, product, and difference
        of dependent events.
        
        It returns the list of dependent events involved in the computation,
        and a synthesizer corresponding to the computation.
        
        PRECONDITION: This should only be called on conjunction-coexclusive DNFs *)
    let separate : DNF.t -> req_synth = fun dnf ->
      if DNF.is_zero dnf then synth_zero else
      if DNF.is_one dnf then synth_one else
        (* returns a synthesizer for a dependent conjunction *)
        let synth_dep_conj : DNF.iset -> req_synth = fun dep_conj ->
          let pos_conj, neg_conj =
            DNF.InnerSet.partition (fun d -> d.sgn) dep_conj in
          (* now both pos_conj and neg_conj contain sets of derived events
             that are constant over their derivation index and their sign.
             So we can remove that information and lower them just to sets
             of events, guaranteed to be independent and of a single sign
             (that sign is pos for pos_conj and neg for neg_conj *)
          let pos_elems, neg_elems =
            D.lower_to_set pos_conj,
            D.lower_to_set neg_conj in
          (* to compute the probability of this dependent conjunction, we
             need to apply PIE *)
          synth_pie pos_elems neg_elems in

        (* returns a synthesizer for an arbitrary conjunction by splitting
             it into dependent conjunctions *)
        let separate_conj : DNF.iset -> req_synth = fun conj ->
          let hashed_ev = DNF.InnerSet.fold (fun d hashed_ev ->
              let hash = D.hash d in
              DHashMap.update hash (function
                  | None -> Some (DNF.InnerSet.singleton d)
                  | Some s -> Some (DNF.InnerSet.add d s)
                ) hashed_ev
            ) conj DHashMap.empty in
          DHashMap.map_reduce
            (fun _ -> synth_dep_conj) synth_mult synth_one hashed_ev in
        DNF.OuterSet.map_reduce separate_conj synth_add synth_zero dnf

    (**
       THIS IS THE MAIN ENTRY POINT

       Use this to turn DNFs into computable structures over
       dependent events
    *)
    let dnf_to_req_synth : DNF.t -> req_synth = fun dnf ->
      dnf
      |> DNF.eliminate_subsumption (* TODO - test how necessary these really are *)
      |> DNF.make_computable
      |> DNF.eliminate_subsumption
      |> separate
  end
end
