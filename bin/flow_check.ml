let int_color, nonint_color = Colors.gold, Colors.cyan

let program = Io.program
let () = print_endline (Expr_repr.program_string program)
let typechecked_prog = (Typecheck.typecheck_program program)
include Analyze.ProgramAnalyzer (struct
    type t = Typecheck.typechecked_program
    let get _ = typechecked_prog
  end)

open Interference_paths

let () = debug_output := !Io.IO.verbose

open Expr

let trace_matches_branch trace branch dir =
  match Interference_paths.find_branch_in_trace_opt branch trace with
  | Some (_, _, dir') -> dir = dir'
  | _ -> false

let trace_matches_internal_event trace ievent =
  BranchMap.fold (fun branch dir prev ->
      prev && (trace_matches_branch trace branch dir)) ievent true

let trace_matches_event trace event =
  Context.IEMap.fold (fun ievent _ prev ->
      prev || (trace_matches_internal_event trace ievent)
    ) event false

let print_flow flow color =
  Output.SimplePrettyPrint.format_program
    Format.std_formatter
    !Io.IO.input_file
    color
    typechecked_prog.label_tbl
    (trace_labels flow)

let false_pos, false_neg, true_pos, true_neg = ref 0, ref 0, ref 0, ref 0

let check_func _ (fdecl, blame_list) =
  let all_flows = compute_trace_set fdecl.body in
  let check_func_param_result param result = (
    let param_local, result_i = 
      match param, result with
      | Arg(_, param_s), Ret(i, _) -> Local param_s, i in
    let result_blame = List.nth blame_list result_i in
    let param_result_flow_event =
      match Context.SiteMap.find_opt (ArgSite param) result_blame with
      | Some e -> e
      | None -> Context.event_zero in
    let interference_flows =
      compute_interference_flows fdecl.body
        param_local result_i in
    let noninterference_flows =
      TraceSet.diff all_flows interference_flows in
    let () = TraceSet.iter (fun flow ->
        if (trace_matches_event flow param_result_flow_event) then (
          true_pos := !true_pos + 1
        ) else (
          false_neg := !false_neg + 1;
          print_flow flow int_color)
      ) interference_flows in
    let () = TraceSet.iter (fun flow ->
        if (trace_matches_event flow param_result_flow_event) then (
          false_pos := !false_pos + 1;
          print_flow flow nonint_color
        ) else (
          true_neg := !true_neg + 1)
      ) noninterference_flows in
    ()
  ) in
  List.iter (fun param ->
      List.iter (fun result ->
          check_func_param_result param result
        ) fdecl.results
    ) fdecl.params

let () = Expr.FuncMap.iter check_func typechecked_prog.tfunc_tbl

let () = Output.(
    Format.fprintf Format.std_formatter
      "Out of %d (= %a + %a) total flows examined (broken down into %a and %a flows),\n the type system mischaracterized %d (= %a + %a)\n"
      (!true_pos + !true_neg + !false_pos + !false_neg)
      (format_color_int int_color) (!true_pos + !false_neg)
      (format_color_int nonint_color) (!false_pos + !true_neg)
      (format_color_str int_color) "interference"
      (format_color_str nonint_color) "noninterference"
      (!false_pos + !false_neg)
      (format_color_int int_color) (!false_neg)
      (format_color_int nonint_color) (!false_pos)
  )



