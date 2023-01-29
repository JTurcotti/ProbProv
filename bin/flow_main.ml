open Util

let program = Io.program
let () = print_endline (Expr_repr.program_string program)
let typechecked_prog = (Typecheck.typecheck_program program)
include Analyze.ProgramAnalyzer (struct
    type t = Typecheck.typechecked_program
    let get _ = typechecked_prog
  end)

let _, (fdecl, _) = Expr.FuncMap.choose typechecked_prog.tfunc_tbl
let src, tgt = match List.hd fdecl.params, List.hd fdecl.results with
  | Arg(_, arg_str), Ret(_, ret_str) -> Expr.(Local(arg_str), Local(ret_str))

open Interference_paths

let all_flows = compute_trace_set fdecl.body
let num_flows = TraceSet.cardinal all_flows

let interference_flows = compute_interference_flows
    fdecl.body src tgt
let num_interference_flows = TraceSet.cardinal interference_flows

let () = Format.fprintf Format.std_formatter
    "\n\nRESULT: %d total flows; %d interference flows\n\n"
    num_flows num_interference_flows

let noninterference_flows = TraceSet.diff all_flows interference_flows

let print_flow flow color =
  Output.SimplePrettyPrint.format_program
    Format.std_formatter
    !Io.IO.input_file
    color
    typechecked_prog.label_tbl
    (trace_labels flow)

let () =
  Format.fprintf Format.std_formatter "Interference flows:\n";
  TraceSet.iter (fun flow -> print_flow flow Colors.gold) interference_flows;
  Format.fprintf Format.std_formatter "\nNoninterference flows:\n";
  TraceSet.iter (fun flow -> print_flow flow Colors.cyan) noninterference_flows
