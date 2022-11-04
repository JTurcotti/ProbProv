open Util

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


(*
let bld = Context.Refactor.EERefactorizer.build
let slc_repr x =
  match Context.Refactor.EERefactorizer.slice x with
  | Some (a, b, c) -> Context_repr.(
      Printf.sprintf "(%s, %s, %s)"
        (aee_repr a)
        (external_event_repr b)
        (external_event_repr c)
    )
  | None -> "None"

let _ = Context.(
    let a = external_event_conj
        (CallEvent(Call(Func("a"), 0), Arg(0, "x"), Ret(0, "x"), true))
        external_event_one in
    let b = external_event_conj
        (CallEvent(Call(Func("b"), 0), Arg(0, "x"), Ret(0, "x"), true))
        external_event_one in
    let ab = external_event_disj a b in
    let _ = print_endline "\n\n\n" in
    let _ = print_endline (slc_repr ab) in
    let out = bld ab in
    print_endline (Context_repr.external_event_repr out)
  )*)

let _ = print_endline Layers.s

(* DEBUGGING
module StrSystem = Equations.EqnSystem(struct type t = string end)

let str_map_repr s = StrSystem.VarMap.fold (fun s d r ->
    Printf.sprintf "%s:%f, %s" s d r) s ""

let _ = print_endline (str_map_repr (StrSystem.(solve (
    add (Eqn ("x", (Mult (Var "y" , Var "y"))))
      (add (Eqn ("y", (Add (Var "x" , Const 0.25))))
         empty)
  ))))
*)

module TestDoubleSet =
struct
type neg_char = char * bool
let nc_neg (c, b) = (c, not b)
let nc_repr (c, b) = Printf.sprintf "%c%s" c (unicode_bar_cond b)
module NC = struct type t = neg_char end
module NCDS = Refactor.DoubleSet (Set(NC)) (Set(Set(NC)))
    (struct type t = neg_char let neg = nc_neg end)

let repr = NCDS.repr nc_repr "%s%s" "%s + %s"

let single c = NCDS.singleton (c, true)
let disj = NCDS.disj
let conj = NCDS.conj
let neg = NCDS.neg
let a, b, c, d, e, f, g, h =
  single 'a', single 'b', single 'c', single 'd', single 'e', single 'f',
  single 'g', single 'h'
let print x = print_endline (repr x) 
let _ = print (disj a b)
let test_ex =
  (disj
     (conj (conj (conj a b) c) d)
     (conj (conj (conj e f) g) h)
  )
let _ = print test_ex
let _ = print (neg test_ex)
end
