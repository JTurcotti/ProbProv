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

module Eta = DependentEv(struct type t = BlamePrim.blame_teleflow end)
module EtaMap = Map(Eta)
module EtaSet = Set(Eta)
type eta = Eta.t

module Omega = DependentEv(struct type t = BlamePrim.direct_blame_flow end)
module OmegaMap = Map(Omega)
module OmegaSet = Set(Omega)
type omega = Omega.t

module PiComputation = 
struct
  module Output = Pi
  let compute _ = 0.5
end

module ProgramAnalyzer (DeferredProg : Defer with type t = Typecheck.typechecked_program) = 
struct
  module GetProg = IdempotentDefer (DeferredProg)
  let get_program _ = GetProg.get()
  
  module PiComputationLayer = Layers.ConstantComputationLayer (Pi) (PiComputation)

  module PhiComputation =
  struct
    module Input = Pi
    module Output = Phi

    module InputSet = Set(Pi)
    module OutputSet = Set(Phi)

    module Eqns = Equations.EqnSystem(Phi)

    let compute : Output.t ->
      Set(Input).t * Set(Output).t *
      (float Map(Input).t -> Equations.EqnSystem(Output).eqn) = ()
  end

  module PhiComputationLayer = Layers.IndirectComputationLayer (Pi) (Phi)
      (PiComputationLayer) (PhiComputation)

  module BetaComputation =
  struct
    module Input = Union(Pi)(Phi)
    module Output = Beta

    module InputSet = Set(Input)

    let compute _ = InputSet.empty, (fun _ -> 0.)
  end

  module PiPhiAggregator =
    Layers.AggregatorLayer (Pi) (Phi)
      (PiComputationLayer) (PhiComputationLayer)
  module BetaComputationLayer =
    Layers.DirectComputationLayer (Union(Pi)(Phi)) (Beta)
      (PiPhiAggregator) (BetaComputation)

  module EtaComputation =
  struct
    module Input = Beta
    module Output = Eta


    let compute : Output.t ->
      Set(Input).t * Set(Output).t *
      (float Map(Input).t -> Equations.EqnSystem(Output).eqn) = ()
  end

  module EtaComputationLayer =
    Layers.IndirectComputationLayer (Beta) (Eta)
      (BetaComputationLayer) (EtaComputation)

  module OmegaComputation =
  struct
    module Input = Eta
    module Output = Omega

    module InputSet = Set(Eta)

    let compute _ = InputSet.empty, (fun _ -> 0.)
  end

  module OmegaComputationLayer =
    Layers.DirectComputationLayer (Eta) (Omega)
      (EtaComputationLayer) (OmegaComputation)

  module Output = struct
    type programOmegas = POmegas of float OmegaMap.t

    let getAllProgOmegas _ =
      let prog = get_program () in
      let fdecl_omegas fdecl = (
        List.fold_right (fun ret omegas ->
            OmegaSet.add (
      ) in
      Expr.(
        FuncMap.fold (fun fdecl ctxt_opt omegas ->
            match ctxt_opt with
            | None -> flows
            | Some _ -> (
                OmegaSet.
              )) prog OmegaSet.empty
      )
          
    let getProgramBlame filter =
      
  end
end
