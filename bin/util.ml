module type T = sig type t end
module Ord (T : T) = struct
  type t = T.t
  let compare = Stdlib.compare
end

module Set (T : T) = 
  Set.Make(Ord(T))
    
module Map (T : T) = 
  Map.Make(Ord(T))

