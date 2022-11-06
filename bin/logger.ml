open Util
open Expr
open Expr_repr
open Blame_prim

let first = ref true
let check_first _ =
  if !first then (first := false; "") else ", "

module MapAndSetPrinter
    (Inner: sig
       type t val fprint_t : Format.formatter -> t -> unit
     end) =
struct
  module M = Map(Inner)
  module S = Set(Inner)

  let fprint_elt ff : Inner.t -> unit = Inner.fprint_t ff

  let fprint_set ff : S.t -> unit = fun t_set ->
    first := true;
    Format.fprintf ff "{";
    S.iter (fun el ->
        Format.fprintf ff "%s%a" (check_first ()) Inner.fprint_t el) t_set;
    Format.fprintf ff "}"

  let fprint_map ff : float M.t -> unit = fun t_map ->
    first := true;
    Format.fprintf ff "{";
    M.iter (fun el v ->
        Format.fprintf ff "%s%a: %f" (check_first ()) Inner.fprint_t el v) t_map;
    Format.fprintf ff "}"
end

let fprint_label ff : label -> unit = fun (Label i) ->
  Format.fprintf ff "ℓ%s" (int_subscript_repr i)

let fprint_call_ret ff (Call(Func(f_s), c_i), Ret(r_i, _)) =
  Format.fprintf ff "⟨%s%s⟩ᵣ%s" f_s (int_subscript_repr c_i)
    (int_subscript_repr r_i)
let fprint_func_arg ff (Func f_s, Arg(i, _)) =
  Format.fprintf ff "%sₐ%s" f_s (int_subscript_repr i)

let fprint_blame_source ff : blame_source -> unit =
  function
  | BlameLabel l -> fprint_label ff l
  | BlameCall(c, r) -> fprint_call_ret ff (c, r)
  | BlameArg(f, a) -> fprint_func_arg ff (f, a)

let fprint_blame_target ff : blame_target -> unit =
  fun {bt_func=Func(f_s); bt_ret=Ret(r_i, _)} ->
  Format.fprintf ff "%sᵣ%s" f_s (int_subscript_repr r_i)

let fprint_blame_flow ff : blame_flow -> unit =
  fun {bf_src=src; bf_tgt=tgt} ->
  Format.fprintf ff "(%a↦%a)" fprint_blame_source src fprint_blame_target tgt

let fprint_blame_teleflow ff : blame_teleflow -> unit =
  fun {bt_src=src; bt_tgt=tgt} ->
  Format.fprintf ff "(%a↦%a)" fprint_blame_target src fprint_blame_target tgt

let fprint_direct_blame_source ff : direct_blame_source -> unit =
  function
  | DBlameLabel l -> fprint_label ff l
  | DBlameArg (f, a) -> fprint_func_arg ff (f, a)

let fprint_direct_blame_flow ff : direct_blame_flow -> unit =
  fun {dbf_src=src; dbf_tgt=tgt} ->
  Format.fprintf ff "(%a↦%a)"
    fprint_direct_blame_source src
    fprint_blame_target tgt

module Pi = struct
  include Set(struct type t = branch end) 

  let fprint_t ff pi =
    iter (fun (Branch(i)) ->
        Format.fprintf ff "π%s" (int_subscript_repr i)) pi
end

module Phi = struct
  include Set(struct type t = call_event end)

  let fprint_t ff =
    iter (fun {ce_func=Func f_s; ce_arg=Arg(a_i, _); ce_ret=Ret(r_i, _)} ->
        Format.fprintf ff "ϕ⟨%s⟩ₐ%sʳ%s" f_s
          (int_subscript_repr a_i) (int_superscript_repr r_i))
end

module Beta = struct
  include Set(struct type t = blame_flow end)

  let fprint_t ff = iter (fprint_blame_flow ff)
end

module Eta = struct
  include Set(struct type t = blame_teleflow end)

  let fprint_t ff = iter (fprint_blame_teleflow ff)
end


module Omega = struct
  include Set(struct type t = direct_blame_flow end) 

  let fprint_t ff = iter (fprint_direct_blame_flow ff)
end

module type LayerLogger =
sig
  module T : T

  (* logs a string to all log files *)
  val global_log_string : string -> unit

  (* logs a string to just this layer's log file *)
  val log_string : string -> unit

  (* logs a string and point to this layer's log file *)
  val log_point : string -> T.t -> unit

  (* logs a string and map to this layer's log file *)
  val log_map : string -> float Map(T).t -> unit

  (* logs a string and set to this layer's log file *)
  val log_set : string -> Set(T).t -> unit

  val log_request : Set(T).t -> unit
  val log_response : float Map(T).t -> unit
end

module BuildLayerLogger
    (T :
     sig
       type t
       val fprint_t : Format.formatter -> t -> unit
     end)
    (Args:
     sig
       val logger_name : string
       val filename : string
       val global_log_string : string -> unit
     end) =
struct
  module T = T
  include T
  module MSFormat = MapAndSetPrinter(T)

  let init _ =
    let oc = open_out Args.filename in
    let ff = Format.formatter_of_out_channel oc in
    let () = Format.fprintf ff "Initializing Log File\n" in
    close_out oc

  let time_str _ =
    let secs = Unix.gettimeofday () in
    let tm = Unix.gmtime secs in
    let fracsecs = (Format.sprintf "%f" (Float.rem secs 1.0)) in
    let fracsecstrim = String.sub fracsecs 1 (String.length fracsecs - 1) in
    Format.sprintf "(%d:%d:%d%s)"
      tm.tm_hour tm.tm_min tm.tm_sec fracsecstrim

  let global_log_string s = Args.global_log_string (
      Format.sprintf "Global(%s): %s" Args.logger_name s)

  let get_oc _ = 
    open_out_gen [Open_append] 0o666 Args.filename

  let log_string s =
    let oc = get_oc () in
    let ff = Format.formatter_of_out_channel oc in
    Format.fprintf ff "%s:%s: %s@." (time_str ()) Args.logger_name s;
    close_out oc

  let log_point s t =
    let oc = get_oc () in
    let ff = Format.formatter_of_out_channel oc in
    Format.fprintf ff "%s:%s: %s %a@." (time_str ()) Args.logger_name
      s MSFormat.fprint_elt t;
    close_out oc

  let log_set s st =
    let oc = get_oc () in
    let ff = Format.formatter_of_out_channel oc in
    Format.fprintf ff "%s:%s: %s %a@." (time_str ()) Args.logger_name
      s MSFormat.fprint_set st;
    close_out oc

  let log_map s mp =
    let oc = get_oc () in
    let ff = Format.formatter_of_out_channel oc in
    Format.fprintf ff "%s:%s: %s %a@." (time_str ()) Args.logger_name
      s MSFormat.fprint_map mp;
    close_out oc

  let log_request = log_set "Request:"
  let log_response = log_map "Response:"
    

end

module Loggers =
struct
  let dirname = "logs/"
  let pi_log_file = dirname ^ "pi_log_file"
  let phi_log_file = dirname ^ "phi_log_file"
  let beta_log_file = dirname ^ "beta_log_file"
  let eta_log_file = dirname ^ "eta_log_file"
  let omega_log_file = dirname ^ "omega_log_file"

  exception DummyLoggerCalled
  let global_logger = ref (fun _ -> raise DummyLoggerCalled)
  let global_log s = !global_logger s

  module PiLogger = BuildLayerLogger (Pi) (struct
      let logger_name = "Pi"
      let filename = pi_log_file
      let global_log_string = global_log
    end)

  module PhiLogger = BuildLayerLogger (Phi) (struct
      let logger_name = "Phi"
      let filename = phi_log_file
      let global_log_string = global_log
    end)

  module BetaLogger = BuildLayerLogger (Beta) (struct
      let logger_name = "Beta"
      let filename = beta_log_file
      let global_log_string = global_log
    end)

  module EtaLogger = BuildLayerLogger (Eta) (struct
      let logger_name = "Eta"
      let filename = eta_log_file
      let global_log_string = global_log
    end
    )

  module OmegaLogger = BuildLayerLogger (Omega) (struct
      let logger_name = "Omega"
      let filename = omega_log_file
      let global_log_string = global_log
    end)

  let () = global_logger := fun s ->
      PiLogger.log_string s;
      PhiLogger.log_string s;
      BetaLogger.log_string s;
      EtaLogger.log_string s;
      OmegaLogger.log_string s

  let () =
    PiLogger.init();
    PhiLogger.init();
    BetaLogger.init();
    EtaLogger.init();
    OmegaLogger.init();
end
