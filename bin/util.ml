module type T = sig type t end
module Ord (T : T) = struct
  type t = T.t
  let compare = Stdlib.compare
end

module Set (T : T) =
struct 
  include Set.Make(Ord(T))
end
    
module Map (T : T) = 
  Map.Make(Ord(T))

