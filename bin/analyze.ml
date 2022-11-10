open Util
open Event_util
open Blame_prim

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
  let get_program _ = (GetProg.get()).tfunc_tbl


  (** gives an index of program labels on demand *)
  module LabelsIndex = IdempotentDefer (struct
      type t = Expr.fdecl Expr.LabelMap.t
      let get _ = Typecheck.index_labels (GetProg.get())
    end)

  let lookup_label_fdecl l =
    Expr.LabelMap.find l (LabelsIndex.get())

  (** gives an index of program branches on demand *)
  module BranchesIndex = IdempotentDefer (struct
      type t = Expr.fdecl Expr.BranchMap.t
      let get _ = Typecheck.index_branches (GetProg.get())
    end)

  let lookup_branch_fdecl br =
    Expr.BranchMap.find br (BranchesIndex.get())

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
    match Context.SiteMap.find_opt (blame_source_as_site blame_flow.bf_src) blame with
    | None -> Context.event_zero
    | Some e -> e

  let get_intrafunc_callsites : blame_target -> (Expr.call * Expr.ret) list = fun tgt ->
    let blame = get_event_for_func_ret tgt.bt_func tgt.bt_ret in
    Context.SiteMap.fold (fun site _ mp ->
        match site with
        | Context.CallSite(call, ret) -> ((call, ret) :: mp)
        | _ -> mp
      ) blame []

  module BTSet = Set(struct type t = blame_target end)

  let get_label_reachable_rets : Expr.label -> BTSet.t = fun l ->
    let enclosing_func = lookup_label_fdecl l in
    List.fold_right (fun ret -> BTSet.add {
        bt_func=enclosing_func.name;
        bt_ret=ret
      }) enclosing_func.results BTSet.empty

  (*
   Pi is the event that a branch is taken
*)
  module Pi = DependentEv(struct
      type t = Expr.branch
      type hash_t = Expr.func
      let hash br = (lookup_branch_fdecl br).name
    end)
  module PiMap = Map(Pi)
  module PiSet = Set(Pi)
  type pi = Pi.t

(*
    Phi is the event that a function's result depends on its argument
*)
  module Phi = DependentEv(struct
      type t = Blame_prim.call_event
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
      type t = Blame_prim.blame_flow
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
      type t = Blame_prim.blame_teleflow
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
      type t = Blame_prim.direct_blame_flow
      type hash_t = Expr.func
      let hash dbf = dbf.dbf_tgt.bt_func
    end)
  module OmegaMap = Map(Omega)
  module OmegaSet = Set(Omega)
  type omega = Omega.t


  (**
     The work performed to derive Phi and to derive Beta is very similar
     in that it involves equations over Pi and Phi. Similarly, the work
     performed to derive Eta and Omega is vert similar in that it involves
     equations over Beta and Eta. The former and the latter here naturally
     yield two modules for performing computation, one for PiPhi computation
     and one for BetaEta computation. This functor is intended to provide
     both. For each of PiPhi and BetaEta, one layer is computed directly
     and one computed indirectly. The Direct and Indirect submodules capture
     the respective work for each layer.

     The two types of objects represented
     in DNF formulas for a given DisjunctiveWorkhorse are termed the Sequel
     and the Original. 
     **)
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

    (**
       Indirect captures the semantics of indirection computation.
       For a given point in the sequel module, and a DNF formula over
       original and se
    *)
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
        let eqn_derivation : (float OriginalMap.t -> SequelEqnSystem.eqn) =
          fun orig_vals ->
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

    module Direct =
    struct
      module OriginalSequelUnion = Union (Original) (Sequel)
      module UnionSet = Set(OriginalSequelUnion)
      module UnionMap = Map(OriginalSequelUnion)

      module FloatArithSynth = ArithSynth(FloatArithmetic)

      type float_derivation =
        UnionSet.t *
        (float UnionMap.t -> float)

      let derive_float : DNF.t -> float_derivation = fun dnf ->
        let disj_request, synthesize =
          FloatArithSynth.dnf_to_req_synth dnf in
        let union_request = DependentEvUtils.resolve_set disj_request in
        let derivation : float UnionMap.t -> float =
          fun orig_seq_vals ->
            synthesize (DependentEvUtils.provide_from_union_map orig_seq_vals) in
        (union_request, derivation)
    end
  end

  module PiPhi =
  struct
    include DisjunctiveWorkhorse (Pi.Elt) (Phi.Elt)

    open Context

    exception BadPhi

    let dnf_format : Format.formatter -> DNF.t -> unit =
      dnf_lift_format (disj_lift_format Logger.Pi.fprint_t Logger.Phi.fprint_t)

    let of_aee : atomic_external_event -> DNF.t =
      fun (CallEvent(Call(func, ind), arg, ret, sign)) ->
      if not sign then raise BadPhi else
        let call_event = {
          ce_func=func;
          ce_arg=arg;
          ce_ret=ret
        } in
        let disj_event = T.Right call_event in
        let derived_event : D.t = {
          el=disj_event;
          ind=ind;
          sgn=true
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
      let derived_event : D.t = {
        el=disj_event;
        ind=0;
        sgn=sgn
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
    let compute _ pi = pow 0.5 (Pi.Set.cardinal pi)
  end

  module PiComputationLayer = Layers.ConstantComputationLayer
      (Pi) (PiComputation)
      (Logger.Loggers.PiLogger)
      (Pi)

  module PhiComputation =
  struct
    module Input = Pi
    module Output = Phi

    module DNF = PiPhi.DNF

    let compute : (string -> unit) -> Phi.t -> PiPhi.Indirect.equation_derivation =
      fun log phi -> 

      (* assert that the passed event is actually dependent *)
      let () = Phi.assert_dep phi in

      (* we have a dependent event whose components are call events
         we need to look up the corresponding event in the program, which
         may be a product of blames
      *)
      let dnf = Phi.Set.fold (fun call_event ->
          call_event |> get_call_event_blame |> PiPhi.of_event |> DNF.conj)
          phi DNF.one in

      let () = log (Format.asprintf "Compute(%a) served by DNF: %a"
                      Logger.Loggers.PhiLogger.fprint_t phi
                      PiPhi.dnf_format dnf) in

      PiPhi.Indirect.derive_sequel_equation phi dnf
  end

  module PhiComputationLayer = Layers.IndirectComputationLayer
      (struct let name = "phi_computation" end)
      (Pi) (Phi)
      (PiComputationLayer) (PhiComputation)
      (Logger.Loggers.PhiLogger)
      (Phi)

  module BetaComputation =
  struct
    module Input = Union(Pi)(Phi)
    module Output = Beta

    module PiPhiSet = Set(Input)
    module PiPhiMap = Map(Input)

    module DNF = PiPhi.DNF

    let compute : (string -> unit) -> Beta.t ->
      PiPhiSet.t * (float PiPhiMap.t -> float) =
      fun log beta ->

      (* assert that the passed event is actually dependent *)
      let () = Beta.assert_dep beta in

      let dnf = Beta.Set.fold (fun blame_flow ->
          blame_flow |> get_intraprocedural_blame |> PiPhi.of_event |> DNF.conj)
          beta DNF.one in

      let () = log (Format.asprintf "Compute(%a) served by DNF: %a"
                      Logger.Loggers.BetaLogger.fprint_t beta
                      PiPhi.dnf_format dnf) in

      PiPhi.Direct.derive_float dnf
  end

  module PiPhiAggregator =
    Layers.AggregatorLayer (Pi) (Phi)
      (PiComputationLayer) (PhiComputationLayer)
  module BetaComputationLayer =
    Layers.DirectComputationLayer (Union(Pi)(Phi)) (Beta)
      (PiPhiAggregator) (BetaComputation)
      (Logger.Loggers.BetaLogger)
      (Beta)

  module BetaEta =
  struct
    include DisjunctiveWorkhorse (Beta.Elt) (Eta.Elt)

    let dnf_format : Format.formatter -> DNF.t -> unit =
      dnf_lift_format (disj_lift_format Logger.Beta.fprint_t Logger.Eta.fprint_t)


    let of_beta : int -> blame_flow -> DNF.t =
      fun ind flow ->
      let disj_event = T.Left flow in
      let derived_event : D.t = {
        el=disj_event;
        ind=ind;
        sgn=true
      } in
      DNF.singleton derived_event

    let of_eta : int -> blame_teleflow -> DNF.t =
      fun ind flow ->
      let disj_event = T.Right flow in
      let derived_event : D.t = {
        el=disj_event;
        ind = ind;
        sgn=true
      } in
      DNF.singleton derived_event

    let teleflow_computation : bool -> (int -> (DNF.t -> DNF.t)) ->
      blame_teleflow -> DNF.t =
      (* if refl_unital is true than flows where source equals target are
         taken to be one, otherwise they are computed out *)
      (* ind_transformer is included to make this computation more general.
         for specific computation of teleflow events it is constantly the
         identity function, but for computation of larger flows such as
         full interprocedural events below other values are used *)
      fun refl_unital ind_transformer teleflow ->
      (* this computation bakes in a formula -
         both the correctness of that formula and the correctness of its
         implementation are vital to the correctness of the analysis.
         The most sensitive component is the correct assignment of
         indendence *)
      if refl_unital && teleflow.bt_src = teleflow.bt_tgt then DNF.one else
        List.fold_right (
          fun (Expr.Call(func, ind), ret) ->
            let intermediate_tgt = {
              bt_func=func;
              bt_ret=ret} in
            DNF.disj (ind_transformer ind (
                DNF.conj
                  (of_eta ind {
                      bt_src=teleflow.bt_src;
                      bt_tgt=intermediate_tgt
                    })
                  (of_beta 0 {
                      bf_src=BlameCall(Expr.Call(func, ind), ret);
                      bf_tgt=teleflow.bt_tgt
                    })
              ))) (get_intrafunc_callsites teleflow.bt_tgt) DNF.zero


    (* express a teleflow as a DNF of beta and eta *)
    let teleflow_event : blame_teleflow -> DNF.t =
      teleflow_computation true (fun _ dnf -> dnf)


    (* expresses a direct blame flow (omega) as a DNF of beta and eta *)
    let interprocedural_event : direct_blame_flow -> DNF.t =
      fun direct_flow ->
      let blame_target = direct_flow.dbf_tgt in
      match direct_flow.dbf_src with
      | DBlameArg(f, a) -> (
          (* in the case that we requested a flow from an arg
             to a return in a different function, return zero:
             no such flow *)
          if f <> blame_target.bt_func then DNF.zero else
            (* otherwise this is a simple intraprocedural flow *)
            of_beta 0 {
              bf_src=BlameArg(f, a);
              bf_tgt=blame_target;
            }
        )
      | DBlameLabel l -> (
          let src_func = (lookup_label_fdecl l).name in
          let tgt_func = blame_target.bt_func in
          let intraprocedural_flow =
            if src_func = tgt_func then
              (* we let the derivation index be 0 here to depend on
                 the top-level betas computed in interprocedural flow *)
              of_beta 0 {
                bf_src=BlameLabel l;
                bf_tgt=blame_target
              } else
              (* otherwise there is no relevant strictly intraprocedural flow *)
              DNF.zero in
          let interprocedural_flow = (
            let interprocedural_flow_g : blame_target -> DNF.t =
              fun g_blame_target ->
                let teleflow = {
                  bt_src=g_blame_target;
                  bt_tgt=blame_target
                } in
                teleflow_computation false (fun ind -> DNF.conj (
                    (* arguably, the choice to insert
                       derivation by the index ind here
                       is the most surprising part of the
                       whole formula.

                       That ind will match the clause of the
                       teleflow being computed by teleflow_computation
                       that corresponds to a call through callsite
                       with index ind in the body of our overall
                       target function.

                       The stack will contain a unique set of call when rooted
                       at each of those callsites, so blame events
                       that appear identical but come from stacks rooted
                       at distinct callsites should be independent.
                       We set the beta to be derived by the index of
                       the callsite exactly to achieve that independence *)
                    of_beta ind {
                      bf_src=BlameLabel l;
                      bf_tgt=g_blame_target
                    }
                  )) teleflow in
            BTSet.map_reduce
              interprocedural_flow_g
              DNF.disj DNF.zero
              (get_label_reachable_rets l)
          ) in
          DNF.disj intraprocedural_flow interprocedural_flow
        )
  end

  module EtaComputation =
  struct
    module Input = Beta
    module Output = Eta

    module DNF = BetaEta.DNF

    let compute : (string -> unit) -> Eta.t ->
      BetaEta.Indirect.equation_derivation =
      fun log eta ->

      let () = Eta.assert_dep eta in

      let dnf = Eta.Set.fold (fun blame_teleflow ->
          blame_teleflow |> BetaEta.teleflow_event |> DNF.conj)
          eta DNF.one in

      let () = log (Format.asprintf "Compute(%a) served by DNF: %a"
                      Logger.Loggers.EtaLogger.fprint_t eta
                      BetaEta.dnf_format dnf) in

      BetaEta.Indirect.derive_sequel_equation eta dnf
  end

  module EtaComputationLayer =
    Layers.IndirectComputationLayer
      (struct let name = "eta_computation" end)
      (Beta) (Eta)
      (BetaComputationLayer) (EtaComputation)
      (Logger.Loggers.EtaLogger)
      (Eta)

  module OmegaComputation =
  struct
    module Input = Union(Beta)(Eta)
    module Output = Omega

    module BetaEtaSet = Set(Input)
    module BetaEtaMap = Map(Input)

    module DNF = BetaEta.DNF

    let compute : (string -> unit) -> Omega.t ->
      BetaEtaSet.t * (float BetaEtaMap.t -> float) =
      fun log omega ->

      let () = Omega.assert_dep omega in

      let dnf = Omega.Set.fold (fun direct_blame_flow ->
          direct_blame_flow |> BetaEta.interprocedural_event |> DNF.conj)
          omega DNF.one in

      let () = log (Format.asprintf "Compute(%a) served by DNF: %a"
                      Logger.Loggers.OmegaLogger.fprint_t omega
                      BetaEta.dnf_format dnf) in


      BetaEta.Direct.derive_float dnf
  end

  (* TODO TODO TODO
     This will result in two distinct calls to the Beta layer!
     that's really bad and expensive!
     incorporate memoization
  *)
  module BetaEtaAggregator =
    Layers.AggregatorLayer (Beta) (Eta)
      (BetaComputationLayer) (EtaComputationLayer)
  module OmegaComputationLayer =
    Layers.DirectComputationLayer (Union(Beta)(Eta)) (Omega)
      (BetaEtaAggregator) (OmegaComputation)
      (Logger.Loggers.OmegaLogger)
      (Omega)

  module Output = struct
    (* yes this is a ref which is bad. it gets set to true
       if any omegas outside [0, 1] are detected, indicating
       an internal error *)
    let bad_omega_detected = ref false
    
    type program_omegas = POmegas of float OmegaMap.t

    (* messy function, aggregates all direct blame flows for a program
       including from args to rets and labels to rets
    *)
    let get_all_prog_omegas _ = Expr.(
        let prog = get_program () in
        let all_labels = FuncMap.fold (fun _ (fdecl, ctxt_opt) ->
            match ctxt_opt with
            | None -> id
            | Some _ -> LabelSet.union (expr_labels fdecl.body))
            prog LabelSet.empty in
        let fdecl_omegas fdecl =
          List.fold_right (fun ret omegas ->
              let tgt = {bt_func=fdecl.name; bt_ret=ret} in
              List.fold_right (fun arg omegas ->
                  OmegaSet.add
                    (Omega.singleton {
                        dbf_src=Blame_prim.DBlameArg (fdecl.name, arg);
                        dbf_tgt=tgt})
                    omegas
                ) fdecl.params
                (LabelSet.fold (fun l omegas ->
                     OmegaSet.add
                       (Omega.singleton {
                           dbf_src=Blame_prim.DBlameLabel l;
                           dbf_tgt=tgt})
                       omegas
                   ) all_labels omegas)
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
    let get_program_blame filter =
      POmegas (OmegaComputationLayer.compute (
          OmegaSet.filter
            (fun omega ->
               filter (Omega.choose omega))
            (get_all_prog_omegas())
        ))

    exception NonSingletonOmegaResponse
    exception OmegaResponseCrossFunctionBlame

    open Blame_prim

    type sorted_omegas = ((float DBSMap.t) Expr.RetMap.t) Expr.FuncMap.t

    let sort_omegas : program_omegas -> sorted_omegas =
      fun (POmegas mp) ->
      OmegaMap.fold (fun omega v ->
          if Omega.Set.cardinal omega != 1 then raise NonSingletonOmegaResponse else
            let dbf = Omega.Set.choose omega in
            Expr.FuncMap.update dbf.dbf_tgt.bt_func (
              function
              | None -> Some (
                  Expr.RetMap.singleton
                    dbf.dbf_tgt.bt_ret
                    (DBSMap.singleton dbf.dbf_src v)
                )
              | Some rm -> Some (
                  Expr.RetMap.update dbf.dbf_tgt.bt_ret (
                    function
                    | None -> Some (DBSMap.singleton dbf.dbf_src v)
                    | Some dbsm -> Some (DBSMap.add dbf.dbf_src v dbsm)
                  ) rm
                )
            )
        ) mp Expr.FuncMap.empty

    let format_rgb_char ff (r, g, b) c =
      Format.fprintf ff "\027[1m\027[38;2;%d;%d;%dm%c\027[0m" r g b c

    let format_rgb_float ff (r, g, b) f =
      (* this looks silly but prevents negative zero from being displayed *)
      let f = if f = 0.0 then 0.0 else f in
      Format.fprintf ff "\027[38;2;%d;%d;%dm%f\027[0m" r g b f

    let format_rgb_str ff (r, g, b) s =
      Format.fprintf ff "\027[38;2;%d;%d;%dm%s\027[0m" r g b s
        
    let format_plain_char ff c =
      Format.fprintf ff "%c" c
        
    let scale_heat_color vl =
      if vl < 0.0 || vl > 1.0 then (
        bad_omega_detected := true;
        (0xff, 0xfc, 0x00)
      ) else (
        let r, g, b = 0xff, 0x30, 0x30 in
        let scale i =
          Float.to_int (255. -. vl *. (255. -. (Float.of_int i))) in
        (scale r, scale g, scale b))
        
    let format_by_float ff vl c =
      format_rgb_char ff (scale_heat_color vl) c
        
    let format_float_by_float ff vl =
      format_rgb_float ff (scale_heat_color vl) vl


    let format_program_blame ff omegas =
      let sorted_omegas = sort_omegas omegas in
      let format_dbs ff (func, dbs) =
        match dbs with
        | DBlameLabel (Label i) ->
          Format.fprintf ff "ℓ%s" (Expr_repr.int_subscript_repr i)
        | DBlameArg (Func f_s, Arg(i, a_s)) ->
          if f_s <> func then raise OmegaResponseCrossFunctionBlame else
            Format.fprintf ff "%s:α%s" a_s (Expr_repr.int_subscript_repr i)
      in
      let format_dbs_map ff (func, dbsm) =
        DBSMap.iter (
          fun dbs v ->
            Format.fprintf ff "\n│       ├─⟨%a ↦ %a"
              format_dbs (func, dbs) format_float_by_float v
        ) dbsm
      in
      let format_rm ff (func, rm) =
        Expr.RetMap.iter (
          fun (Expr.Ret (i, s)) dbsm ->
            Format.fprintf ff "├───────┬─result %d '%s':%a\n"
              i s format_dbs_map (func, dbsm)
        ) rm
      in
      Expr.FuncMap.iter (
        fun (Expr.Func func) rm ->
          Format.fprintf ff
            "\nOmegas for function %s:\n%a└───────╼\n"
            func format_rm (func, rm)
      ) sorted_omegas

    module VeryPrettyPrint =
    struct
      let format_program ff input_file
          (tprog : Typecheck.typechecked_program) omegas =

        let format_func_ret func ret dbsm = (
          
          let format_func_ret_dbs ff dbs =
            format_by_float ff (
              match DBSMap.find_opt dbs dbsm with
              | None -> 0.0
              | Some vl -> vl
            ) in

          let format_func_ret_label ff l =
            format_func_ret_dbs ff (DBlameLabel l) in

          let format_func_ret_arg ff (func, arg) =
            format_func_ret_dbs ff (DBlameArg (func, arg)) in

          let format_func_ret_ret ff (func2, ret2) =
              if (func2, ret2) = (func, ret) then            
                format_rgb_char ff (0, 255, 0) else
                format_plain_char ff in

          let format_char i c =
            if c = '\n' then Format.fprintf ff "\n│  " else
            match
              Expr.IntMap.find_opt i tprog.label_tbl,
              Expr.IntMap.find_opt i tprog.arg_tbl,
              Expr.IntMap.find_opt i tprog.ret_tbl
            with
            | Some l, _, _ ->
              (* it's labelled *)
              format_func_ret_label ff l c
            | None, Some fa, _ ->
              (* it's an arg *)
              format_func_ret_arg ff fa c
            | None, None, Some fr ->
              (* it's a ret *)
              format_func_ret_ret ff fr c
            | None, None, None ->
              format_plain_char ff c in
          let char_num = ref 0 in
          let get_char _ = let i = !char_num in char_num := i + 1; i in
          let ic = open_in input_file in
          Format.fprintf ff "\n";
          let () = match func, ret with Func f, Ret(i, s) -> (
              Format.fprintf ff
                "┌─╼ Blame Map for '%s', result %d '%s' \n│  \n│  "
                f i s) in
          let () = try
            while true do
              let c = input_char ic in
              format_char (get_char ()) c
            done;
            with End_of_file -> () in
          Format.fprintf ff
            "\n└───────────────────────╼\n") in
        let sorted_omegas = sort_omegas omegas in
        Expr.FuncMap.iter (
          fun func -> Expr.RetMap.iter (format_func_ret func)) sorted_omegas;
        if !bad_omega_detected then
          format_rgb_str ff
            (scale_heat_color 2.0)
            "\n\027[1mWARNING: Bad omega detected\027[0m\n"
        else ()
    end
  end
end
