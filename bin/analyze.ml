open Util
open Event_util

(**
   This module defines the primitive types
*)
module BlamePrim =
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

  let get_event_for_func_ret : Expr.func -> Expr.ret -> Context.blame =
    fun func ret ->
    let prog = get_program () in
    let _, ctxt_opt = Expr.FuncMap.find func prog in
    let ctxt = force_some ctxt_opt in
    Context.context_lookup_ret ret ctxt

  let get_call_event_blame : call_event -> Context.event = fun call_event ->
    let blame = get_event_for_func_ret call_event.ce_func call_event.ce_ret in
    Context.SiteMap.find (Context.ArgSite call_event.ce_arg) blame

  let blame_source_as_site : blame_source -> Context.site = Context.(function
      | BlameLabel l -> LabelSite l
      | BlameCall(c, r) -> CallSite(c, r)
      | BlameArg(_, a) -> ArgSite(a)
    )

  let get_intraprocedural_blame : blame_flow -> Context.event = fun blame_flow ->
    let blame = get_event_for_func_ret
        blame_flow.bf_tgt.bt_func blame_flow.bf_tgt.bt_ret in
    Context.SiteMap.find (blame_source_as_site blame_flow.bf_src) blame

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

  module DisjunctiveWorkhorse
      (OriginalElt : DepHashT) (SequelElt: DepHashT) =
  struct
    module Original = DependentEv(OriginalElt)
    module Sequel = DependentEv(SequelElt)
    
    module T = DependentDisj (OriginalElt) (SequelElt)
    include T
    include Refactor.DerivedDoubleSet(T)           


    module OriginalSet = Set(Original)
    module SequelSet = Set(Sequel)

    module OriginalMap = Map(Original)

    module Indirect =
    struct

      module SequelEqnSystem = Equations.EqnSystem(Sequel)

      module ExprArithSynth = ArithSynth(SequelEqnSystem.ExprArith)

      type equation_derivation =
             OriginalSet.t *
             SequelSet.t *
             (float OriginalMap.t -> SequelEqnSystem.eqn)

      let derive_sequel_equation : Sequel.t -> DNF.t -> equation_derivation =
        fun seq dnf_for_seq ->
        let disj_request, synthesizer =
          ExprArithSynth.dnf_to_req_synth dnf_for_seq in
        let orig_request, seq_request =
          DependentEvUtils.split_set disj_request in
        let eqn_derivation orig_vals =
          let orig_provider orig =
            SequelEqnSystem.const_expr (OriginalMap.find orig orig_vals) in
          let seq_provider seq =
            SequelEqnSystem.var_expr seq in
          let orig_seq_disj_provider =
            DependentEvUtils.multiplex orig_provider seq_provider in
          let seq_eqn_expr =
            synthesizer orig_seq_disj_provider in
          SequelEqnSystem.eqn_of seq seq_eqn_expr in
        (orig_request, seq_request, eqn_derivation)
    end
  end

  module PiPhi =
  struct
    include DisjunctiveWorkhorse (Pi.Elt) (Phi.Elt)

    open Context

    exception BadPhi

    let of_aee : atomic_external_event -> DNF.t =
      fun (CallEvent(Call(func, ind), arg, ret, sign)) ->
      if not sign then raise BadPhi else
        let call_event = {
          ce_func=func;
          ce_arg=arg;
          ce_ret=ret
        } in
        let disj_event = T.Right call_event in
        let derived_event = {
          D.el=disj_event;
          D.ind=ind;
          D.sgn=true
        } in
        DNF.singleton derived_event

    let of_aee_conj : aee_conjunction -> DNF.t =
      AEEConjunctiveSet.map_reduce
        of_aee DNF.conj DNF.one

    let of_external_event : external_event -> DNF.t =
      AEEDNFSet.map_reduce
        of_aee_conj DNF.disj DNF.zero

    let of_atomic_internal_event : Expr.branch -> bool -> DNF.t =
      fun branch sgn ->
      let disj_event = T.Left branch in
      let derived_event = {
        D.el=disj_event;
        D.ind=0;
        D.sgn=sgn
      } in
      DNF.singleton derived_event

    let of_internal_event : internal_event -> DNF.t =
      Expr.BranchMap.map_reduce
        of_atomic_internal_event DNF.conj DNF.one

    let of_event : event -> DNF.t =
      IEMap.map_reduce
        (fun ie ee -> DNF.conj (of_internal_event ie) (of_external_event ee))
        DNF.disj DNF.zero
  end

  module PiComputation = 
  struct
    module Output = Pi

    (* this assumes each branch has an independent 1/2 chance of going each way *)
    let compute pi = pow 0.5 (Pi.Set.cardinal pi)
  end

  module PiComputationLayer = Layers.ConstantComputationLayer (Pi) (PiComputation)

  module PhiComputation =
  struct
    module Input = Pi
    module Output = Phi

    module DNF = PiPhi.DNF

    let compute : Output.t -> PiPhi.Indirect.equation_derivation =
      fun phi -> 

      (* assert that the passed event is actually dependent *)
      let () = Phi.assert_dep phi in

      (* we have a dependent event whose components are call events
         we need to look up the corresponding event in the program, which
         may be a product of blames
      *)
      let dnf = Phi.Set.fold (fun call_event ->
          call_event |> get_call_event_blame |> PiPhi.of_event |> DNF.conj)
          phi DNF.one in

      PiPhi.Indirect.derive_sequel_equation phi dnf
  end

  module PhiComputationLayer = Layers.IndirectComputationLayer (Pi) (Phi)
      (PiComputationLayer) (PhiComputation)

  module BetaComputation =
  struct
    module Input = Union(Pi)(Phi)
    module Output = Beta

    module PiPhiSet = Set(Input)
    module PiPhiMap = Map(Input)

    module DNF = PiPhi.DNF

    module PiPhiFloatSynth = PiPhi.ArithSynth(FloatArithmetic)

    let compute : Beta.t -> PiPhiSet.t * (float PiPhiMap.t -> float) =
      fun beta ->

      (* assert that the passed event is actually dependent *)
      let () = Beta.assert_dep beta in

      let dnf = Beta.Set.fold (fun blame_flow ->
          blame_flow |> get_intraprocedural_blame |> PiPhi.of_event |> DNF.conj)
          beta DNF.one in

      let disj_request, synth = PiPhiFloatSynth.dnf_to_req_synth dnf in
      let union_request = PiPhi.DependentEvUtils.resolve_set disj_request in
      let plan : float PiPhiMap.t -> float = fun pi_phi_results ->
        synth (PiPhi.DependentEvUtils.provide_from_union_map pi_phi_results) in
      (union_request, plan)
  end

  module PiPhiAggregator =
    Layers.AggregatorLayer (Pi) (Phi)
      (PiComputationLayer) (PhiComputationLayer)
  module BetaComputationLayer =
    Layers.DirectComputationLayer (Union(Pi)(Phi)) (Beta)
      (PiPhiAggregator) (BetaComputation)

  module BetaEta =
  struct
    module T = DependentDisj (Beta.Elt) (Eta.Elt)
    include Refactor.DerivedDoubleSet(T)

    include T
  end

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
              let tgt = {bt_func=fdecl.name; bt_ret=ret} in
              List.fold_right (fun arg omegas ->
                  OmegaSet.add
                    (Omega.singleton {
                        dbf_src=BlamePrim.DBlameArg (fdecl.name, arg);
                        dbf_tgt=tgt})
                    omegas
                ) fdecl.params
                (LabelSet.fold (fun l omegas ->
                     OmegaSet.add
                       (Omega.singleton {
                           dbf_src=BlamePrim.DBlameLabel l;
                           dbf_tgt=tgt})
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
