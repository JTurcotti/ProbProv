let program = Io.program
let () = print_endline (Expr_repr.program_string program)
let typechecked_prog = (Typecheck.typecheck_program program)
include Analyze.ProgramAnalyzer (struct
    type t = Typecheck.typechecked_program
    let get _ = typechecked_prog
  end)

open Interference_paths
open Expr
let () = debug_output := !Io.IO.verbose


let () = Expr.FuncMap.iter (fun _ (fdecl, _) -> (
      let all_flows = compute_trace_set fdecl.body in
      let num_flows = TraceSet.cardinal all_flows in
      List.iter (fun (Arg(arg, arg_str)) ->
          (let src = Expr.(Local(arg_str)) in
           (List.iter (fun (Ret(tgt, tgt_str)) -> (
                  let () =
                    Format.fprintf Format.std_formatter
                      "========================[ Func %s: %s -> %s ]================================"
                      (Expr.func_to_string fdecl.name) arg_str tgt_str
                  in
                  let interference_flows = compute_interference_flows
                      fdecl.body src tgt in
                  let num_interference_flows = TraceSet.cardinal interference_flows in

                  let () = Format.fprintf Format.std_formatter
                      "\n\nRESULT: %d total flows; %d interference flows\n\n"
                      num_flows num_interference_flows in

                  let noninterference_flows = TraceSet.diff all_flows interference_flows in

                  let print_flow flow color =
                    Output.SimplePrettyPrint.format_program
                      Format.std_formatter
                      !Io.IO.input_file
                      color
                      typechecked_prog
                      fdecl
                      (trace_labels flow)
                      (Arg(arg, arg_str)) (Ret(tgt, tgt_str)) in

                  let () =
                    Format.fprintf Format.std_formatter "Interference flows:\n";
                    TraceSet.iter (fun flow -> print_flow flow Colors.gold) interference_flows;
                    Format.fprintf Format.std_formatter "\nNoninterference flows:\n";
                    TraceSet.iter (fun flow -> print_flow flow Colors.cyan) noninterference_flows in
                  ()
                )) fdecl.results)
          )) fdecl.params)
  ) typechecked_prog.tfunc_tbl
