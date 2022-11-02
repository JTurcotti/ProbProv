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
    | BlameTgt of func * ret

  (* these are the sites the type system identifies - they include flows from a call to a return
     through the body of a function*)
  type blame_flow = blame_source * blame_target

(* these are the flows that we need to figure out using equation solving - the flow from the
   return of one function to the return of another via interprocedural calls *)
  type blame_teleflow = blame_target * blame_target

  type direct_blame_source =
    | DBlameLabel of label
    | DBlameArg of func * arg

  (* these are a restricted version of the blame_flow type above - flows from calls to returns
     are not included because we used computation of the teleflows to eliminate them *)
  type direct_blame_flow = direct_blame_source * blame_target
end


(*
   this is used to model a conjunction of events and their inverse
   in practice, for effeciency, should only be used for dependent events
   *)
module DependentEv(T : T) =
struct
  module Map = Map(T)

  type t = bool Map.t

  let singleton x =
    Map.singleton x true
end

(*
   Pi is the event that a branch is taken
*)
module Pi = DependentEv(struct type t = Expr.branch end)
module PiMap = Map(Pi)
module PiSet = Set(Pi)
type pi = Pi.t
            
(*
    Phi is the event that a function's result depends on its argument
*)
module Phi = DependentEv(struct type t = Context.atomic_external_event end)
module PhiMap = Map(Phi)
module PhiSet = Set(Phi)
type phi = Phi.t

(*
   Beta is the event that an intraprocedural flow occurs
   *)
module Beta = DependentEv(struct type t = BlamePrim.blame_flow end)
module BetaMap = Map(Beta)
module BetaSet = Set(Beta)
type beta = Beta.t
(*
   Eta is the event that a teleflow - from one func ret to another - occurs
   *)
module Eta = DependentEv(struct type t = BlamePrim.blame_teleflow end)
module EtaMap = Map(Eta)
module EtaSet = Set(Eta)
type eta = Eta.t

(*
   Omega is the event that a possibly interprocedural flow occurs
   *)
module Omega = DependentEv(struct type t = BlamePrim.direct_blame_flow end)
module OmegaMap = Map(Omega)
module OmegaSet = Set(Omega)
type omega = Omega.t

(*
   A ProgramAnalyzer should be initialized the the deferred computation of a
   typechecked program. It's submodule Output contains a function getProgramBlame
   that is used to perform the analysis
*)
module ProgramAnalyzer (DeferredProg : Defer with type t = Typecheck.typechecked_program) = 
struct
  module GetProg = IdempotentDefer (DeferredProg)
  let get_program _ = match GetProg.get() with TProgram mp -> mp

  
  module PiComputation = 
  struct
    module Output = Pi
    let compute _ = 0.5
  end
  
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

    (* messy function, aggregates all direct blame flows for a program
       including from args to rets and labels to rets
    *)
    let getAllProgOmegas _ = Expr.(
        let prog = get_program () in
        let fdecl_omegas fdecl =
          let fdecl_labels = expr_labels fdecl.body in
          List.fold_right (fun ret omegas ->
              let tgt = BlamePrim.BlameTgt (fdecl.name, ret) in
              List.fold_right (fun arg omegas ->
                  OmegaSet.add
                    (Omega.singleton (BlamePrim.DBlameArg (fdecl.name, arg), tgt))
                    omegas
                ) fdecl.params
                (LabelSet.fold (fun l omegas ->
                     OmegaSet.add
                       (Omega.singleton (BlamePrim.DBlameLabel l, tgt))
                       omegas
                   ) fdecl_labels omegas)
            ) fdecl.results OmegaSet.empty in
        FuncMap.fold (fun _ (fdecl, ctxt_opt) omegas ->
            match ctxt_opt with
            | None -> omegas
            | Some _ -> (
                OmegaSet.union (fdecl_omegas fdecl) omegas
              )) prog OmegaSet.empty
      )


    (* THIS IS THE ENTRY POINT TO THE ANALYZER
       returns a map from all direct blame flows (i.e. omegas) to probabilities
       optionally can pass a filter to only get for some blame flows
    *)
    let getProgramBlame filter =
      POmegas (OmegaComputationLayer.compute (
        OmegaSet.filter filter (getAllProgOmegas())
      ))
  end
end
