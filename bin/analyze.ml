open Util
open Event_util

module BlamePrim =
(**
   This module defines the primitive types
*)
struct
  open Expr

  type call_event = {ce_func : func; ce_arg : arg; ce_ret : ret}

  type blame_source =
    | BlameLabel of label
    | BlameCall of call * ret
    | BlameArg of func * arg

  type blame_target = {bt_func: func; bt_ret: ret}

  (* these are the sites the type system identifies -
     they include flows from a call to a return
     through the body of a function
     so the label, call, or arg of the source should be present in the
     function of the target*)
  type blame_flow = {bf_src: blame_source; bf_tgt: blame_target}

  (* these are the flows that we need to figure out using equation solving - the flow from the
     return of one function to the return of another via interprocedural calls *)
  type blame_teleflow = {bt_src: blame_target; bt_tgt: blame_target}

  type direct_blame_source =
    | DBlameLabel of label
    | DBlameArg of func * arg

  (* these are a restricted version of the blame_flow type above - flows from calls to returns
     are not included because we used computation of the teleflows to eliminate them *)
  type direct_blame_flow = {dbf_src: direct_blame_source; dbf_tgt: blame_target}
end

open BlamePrim

exception OptionShouldntBeNoneHere
let force_some =

  function
  | Some x -> x
  | None -> raise OptionShouldntBeNoneHere

(*
   A ProgramAnalyzer should be initialized the the deferred computation of a
   typechecked program. It's submodule Output contains a function getProgramBlame
   that is used to perform the analysis
*)
module ProgramAnalyzer (DeferredProg : Defer with type t = Typecheck.typechecked_program) = 
struct
  module GetProg = IdempotentDefer (DeferredProg)
  let get_program _ = match GetProg.get() with TProgram mp -> mp


  (** gives an index of program labels on demand *)
  module LabelsIndex = IdempotentDefer (struct
      type t = Expr.fdecl Expr.LabelMap.t
      let get _ = Typecheck.index_labels (GetProg.get())
    end)

  (** gives an index of program branches on demand *)
  module BranchesIndex = IdempotentDefer (struct
      type t = Expr.fdecl Expr.BranchMap.t
      let get _ = Typecheck.index_branches (GetProg.get())
    end)

  let get_call_event_blame : call_event -> Context.event = fun call_event ->
    let prog = get_program () in
    let _, ctxt_opt = Expr.FuncMap.find call_event.ce_func prog in
    let ctxt = force_some ctxt_opt in
    let blame = Context.context_lookup_ret call_event.ce_ret ctxt in
    Context.SiteMap.find (Context.ArgSite call_event.ce_arg) blame

  (*
   Pi is the event that a branch is taken
*)
  module Pi = DependentEv(struct
      type t = Expr.branch
      type hash_t = Expr.func
      let hash br = (Expr.BranchMap.find br (BranchesIndex.get())).name
    end)
  module PiMap = Map(Pi)
  module PiSet = Set(Pi)
  type pi = Pi.t

(*
    Phi is the event that a function's result depends on its argument
*)
  module Phi = DependentEv(struct
      type t = BlamePrim.call_event
      type hash_t = Expr.func
      let hash ce = ce.ce_func
    end)
  module PhiMap = Map(Phi)
  module PhiSet = Set(Phi)
  type phi = Phi.t

(*
   Beta is the event that an intraprocedural flow occurs
   *)
  module Beta = DependentEv(struct
      type t = BlamePrim.blame_flow
      type hash_t = Expr.func
      let hash bf = bf.bf_tgt.bt_func
    end)
  module BetaMap = Map(Beta)
  module BetaSet = Set(Beta)
  type beta = Beta.t
(*
   Eta is the event that a teleflow - from one func ret to another - occurs
   *)
  module Eta = DependentEv(struct
      type t = BlamePrim.blame_teleflow
      type hash_t = Expr.func
      let hash bt = bt.bt_tgt.bt_func
    end)
  module EtaMap = Map(Eta)
  module EtaSet = Set(Eta)
  type eta = Eta.t

(*
   Omega is the event that a possibly interprocedural flow occurs
   *)
  module Omega = DependentEv(struct
      type t = BlamePrim.direct_blame_flow
      type hash_t = Expr.func
      let hash dbf = dbf.dbf_tgt.bt_func
    end)
  module OmegaMap = Map(Omega)
  module OmegaSet = Set(Omega)
  type omega = Omega.t


  module PiPhi =
  struct
    module T = DependentDisj (Pi.Elt) (Phi.Elt)
    include Refactor.DerivedDoubleSet(T)

    open Context

    let of_aee : atomic_external_event -> DNF.t = _

    let of_aee_conj : aee_conjunction -> DNF.t = _
    
    let of_external_event : external_event -> DNF.t = _

    let of_internal_event : internal_event -> DNF.t = _

    let of_event : event -> DNF.t = _

    include T
  end
  
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

    module EqnS = Equations.EqnSystem(Phi)    

    (* this is what we aim to compute*)
    type plan = PiSet.t *
                PhiSet.t *
                (float PiMap.t -> Equations.EqnSystem(Output).eqn)

    module DNF = PiPhi.DNF
    type dnf = DNF.t

    module PiPhiArithSynth = PiPhi.ArithSynth(EqnS.ExprArith)
                
    let create_plan_from_dnf : dnf -> Phi.t -> plan = fun dnf phi ->
      let disj_request, synthesizer =
        dnf |> DNF.make_computable |> PiPhiArithSynth.separate in
      let pi_request, phi_request =
        PiPhi.DependentEvUtils.split_set disj_request in
      let eqn_plan pi_vals =
        let pi_provider pi =
          EqnS.const_expr (PiMap.find pi pi_vals) in
        let phi_provider phi =
          EqnS.var_expr phi in
        let piphi_provider =
          PiPhi.DependentEvUtils.multiplex pi_provider phi_provider in
        let mult, add, sub = EqnS.mult_expr, EqnS.add_expr, EqnS.sub_expr in
        let eqn_expr = synthesizer piphi_provider in
        EqnS.eqn_of phi eqn_expr in
      (pi_request, phi_request, eqn_plan)

    let compute : Output.t -> plan =
      fun phi -> 

      (* assert that the passed event is actually dependent *)
      let () = Phi.assert_dep phi in

      (* we have a dependent event whose components are call events
         we need to look up the corresponding event in the program, which
         may be a product of blames
      *)
      let dnf = Phi.Set.fold (fun call_event ->
          call_event |> get_call_event_blame |> DNF.of_event |> DNF.conj)
          phi DNF.one in
      
      create_plan_from_dnf dnf
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
