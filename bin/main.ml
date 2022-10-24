module IO =
struct
  let usage_msg = "eval -i <input_file> -o <output_file>"
  let input_file = ref ""
  let output_file = ref ""
  let verbose = ref false
  let simple_parse = ref false

  let anon_fun _ =
    raise (Arg.Bad "run takes no anonymous arguments")

  let speclist =
    [("-v", Arg.Set verbose, "Output debug information");
     ("-s", Arg.Set simple_parse, "Simple parse without complex desugarings");
     ("-i", Arg.Set_string input_file, "Set input file name");
     ("-o", Arg.Set_string output_file, "Set output file name")]
end


let program = IO.(try
                 Arg.parse speclist anon_fun usage_msg;
                 let ic = open_in !input_file in
                 (*let oc = open_out !output_file in*)
                 let lexbuf = Lexing.from_channel ic in
                 let program = Parser.main Lexer.token lexbuf in
                 Expr.label_prog program
               with Lexer.FAIL ->
                 exit 1)

let _ = print_endline (Expr_repr.program_string program)
let typechecked_prog = (Typecheck.typecheck_program program)
let _ = print_endline (Context_repr.typechecked_program_repr
                         typechecked_prog)
                         
    



