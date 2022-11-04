open Util

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

  (* be careful with this - definition should correspond to event implication *)
  val subset: t -> t -> bool
end

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

module type Neg =
sig
  type t
  val neg : t -> t
end

(*
   A DoubleSet gives DNF semantics to two nested set modules
   *)
module DoubleSet
    (InnerSet : SetLike)
    (OuterSet : SetLike with type elt = InnerSet.t)
    (Neg : Neg
     with type t = InnerSet.elt) =
struct
  type elt = InnerSet.elt
  type iset = InnerSet.t
  type oset = OuterSet.t

  let zero = OuterSet.empty
  let one = OuterSet.singleton (InnerSet.empty)
  
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

  let rec build (oset : oset) : oset =
    if OuterSet.is_empty oset then zero else
      match slice oset with
      | None -> one
      | Some (a, b, c) ->
        disj
          (conj_elt a
             (* we call eliminate_subsumption here because the mapped removal
                can introduce new subsumption (e.g. under remove a: a + b ↦ 1 + b)
                or the union with b after the mapped removal, and it is vital that we
                recur into as small an object as possible *)
             (build (eliminate_subsumption (disj b c))))
          (conj_elt (neg_elt a)
             (build c))
end
