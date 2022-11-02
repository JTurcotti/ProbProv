open Util

module BlamePrim =
  (**
     This module defines the primitive types
  *)
struct
  open Expr
      
  type blame_source =
    | BlameLabel of label
    | BlameCall of call * ret
    | BlameArg of func * arg

  type blame_target =
    | BlameSrc of func * ret

  type blame_flow = blame_source * blame_target

  type blame_teleflow = blame_target * blame_target

  type direct_blame_source =
    | DBlameLabel of label
    | DBlameArg of func * arg

  type direct_blame_flow = direct_blame_source * blame_target
end


module DependentEv(T : T) =
struct
  module Map = Map(T)

  type t = bool Map.t
end

module Pi = DependentEv(struct type t = Expr.branch end)
module PiMap = Map(Pi)
module PiSet = Set(Pi)
type pi = Pi.t

module Phi = DependentEv(struct type t = Context.atomic_external_event end)
module PhiMap = Map(Phi)
module PhiSet = Set(Phi)
type phi = Phi.t

module Beta = DependentEv(struct type t = BlamePrim.blame_flow end)
module BetaMap = Map(Beta)
module BetaSet = Set(Beta)
type beta = Beta.t

module Epsilon = DependentEv(struct type t = BlamePrim.blame_teleflow end)
module EpsilonMap = Map(Epsilon)
module EpsilonSet = Set(Epsilon)
type epsilon = Epsilon.t

module Omega = DependentEv(struct type t = BlamePrim.direct_blame_flow end)
module OmegaMap = Map(Omega)
module OmegaSet = Set(Omega)
type omega = Omega.t

module PiComputation = 
struct
  type output = pi
  let compute _ = 0.5
end

module PiComputationLayer = Layers.ConstantComputationLayer (Pi) (PiComputation)

module PhiComputation =
struct
end

