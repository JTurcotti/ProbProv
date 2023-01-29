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

let interference_flows = Interference_paths.compute_interference_flows
    fdecl.body src tgt

let one_flow = Interference_paths.(match TraceSet.choose_opt interference_flows with
    | None -> Expr.LabelSet.empty
    | Some flow -> trace_labels flow)

let () = Output.SimplePrettyPrint.format_program Format.std_formatter
    !Io.IO.input_file typechecked_prog.label_tbl one_flow
