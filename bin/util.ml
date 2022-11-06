let compose f g x = g (f x)    
let id x = x


module type T = sig type t end

module Ord (T : T) = struct
  type t = T.t
  let compare = Stdlib.compare
end

let first = ref true
let check_first _ =
  if !first then (first := false; "") else ", "
let check_first_s s =
  if !first then (first := false; "") else s

type 't s_constr = 't Set.s_constr
type ('k, 'v) m_constr = ('k, 'v) Map.m_constr

module Set (T : T) =
struct
  include Set.Make(Ord(T))

  let map_reduce map reduce unit t =
    match choose_opt t with
    | None -> unit
    | Some el -> fold (compose map reduce) (remove el t) (map el)
                   
  let lift_format format_t infix unit: Format.formatter -> t -> unit =
    fun ff st ->
    if is_empty st then Format.fprintf ff "%s" unit
    else (
      let old = !first in
      first := true;
      iter (fun el ->
          Format.fprintf ff "%s" (check_first_s infix);
          Format.fprintf ff "%a" format_t el) st;
      first := old
    )
end

module Map (T : T) =
struct
  include Map.Make(Ord(T))

  let from_elem_foo elems foo =
    List.fold_right (fun e -> add e (foo e)) elems empty

  let map_reduce map reduce unit t =
    match choose_opt t with
    | None -> unit
    | Some (k, v) -> fold (fun k v -> reduce (map k v)) (remove k t) (map k v)

end

type ('l, 'r) union_t = Left of 'l | Right of 'r

module Union (L : T) (R : T) =
struct
  module T =
  struct
    type t = (L.t, R.t) union_t
  end

  module UMap = Map(T)
  module USet = Set(T)
  module LMap = Map(L)
  module LSet = Set(L)
  module RMap = Map(R)
  module RSet = Set(R)

  let splitSet uset =
    USet.fold (fun e (lset, rset) ->
        match e with
        | Left e -> (LSet.add e lset, rset)
        | Right e -> (lset, RSet.add e rset))
      uset
      (LSet.empty, RSet.empty)

  let joinMap lmap rmap =
    LMap.fold (fun l v umap -> UMap.add (Left l) v umap) lmap
      (RMap.fold (fun r v umap -> UMap.add (Right r) v umap) rmap UMap.empty)

  include T
end

module type Defer =
sig
  type t
  val get : unit -> t
end

(* guarantees that the Src Defer is only called once *)
module IdempotentDefer (Src : Defer) =
struct
  type t = Src.t

  let x_opt : t option ref = ref None

  let get _ =
    match !x_opt with
    | Some x -> x
    | None ->
      let x = Src.get () in
      let () = x_opt := Some x in
      x
end


let unicode_bar = "\u{0305}"
let unicode_bar_cond b = if b then "" else unicode_bar

let unicode_bar_str =
  String.fold_left (fun prefix c -> Format.sprintf "%s%c%s" prefix c unicode_bar) ""
let unicode_bar_str_cond b = if b then id else unicode_bar_str 

module type Arithmetic =
sig
  type t

  val mult : t -> t -> t
  val add : t -> t -> t
  val sub : t -> t -> t
    
  val one : t
  val zero : t
end

module FloatArithmetic =
struct
  type t = float

  let mult a b = a *. b
  let add a b = a +. b
  let sub a b = a -. b
  let one = 1.
  let zero = 0.
end

let rec pow f i =
  if i = 0 then 1. else f *. (pow f (i - 1))
