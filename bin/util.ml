module type T = sig type t end

module Ord (T : T) = struct
  type t = T.t
  let compare = Stdlib.compare
end

module Set (T : T) = 
  Set.Make(Ord(T))

module Map (T : T) = 
  Map.Make(Ord(T))

module Union (Left : T) (Right : T) =
struct
  module T =
  struct
    type t = L of Left.t | R of Right.t
  end

  module UMap = Map(T)
  module USet = Set(T)
  module LMap = Map(Left)
  module LSet = Set(Left)
  module RMap = Map(Right)
  module RSet = Set(Right)

  let splitSet uset =
    USet.fold (fun e (lset, rset) ->
        match e with
        | T.L e -> (LSet.add e lset, rset)
        | T.R e -> (lset, RSet.add e rset))
      uset
      (LSet.empty, RSet.empty)

  let joinMap lmap rmap =
    LMap.fold (fun l v umap -> UMap.add (L l) v umap) lmap
      (RMap.fold (fun r v umap -> UMap.add (R r) v umap) rmap UMap.empty)

  type t = T.t
end
