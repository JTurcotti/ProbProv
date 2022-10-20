type func = Func of string
let func_to_string (Func s) = s

type local = Local of string
let local_to_string (Local s) = s

type arg = Arg of int * string
type ret = Ret of int * string

type branch = Branch of int
type label = Label of int

type aexp =
  | Var of local * label
  | Const of label
  | Binop of aexp * aexp * label
  | Unop of aexp * label
  | FApp of func * aexp * label

type expr =
  | Skip
  | Cond of aexp * expr * expr * branch
  | Assign of local * aexp
  | Seq of expr * expr
  | Assert of local * aexp
  | AExp of aexp

type fdecl = {
  name: func;
  params: arg list;
  num_params: int;
  results: ret list;
  num_results: int;
  body: expr;
}

module FuncKey = struct
  type t = func
  let compare = Stdlib.compare
end

module FuncMap = Map.Make(FuncKey)
type program = Program of fdecl FuncMap.t

exception LabelErr of string

(* This function takes a raw_program (see raw_expr)
   as parsed from source, and adds associates all of its
   conditionals with branches numbers and some AST nodes
   with label numbers

   TODO: add source locations to raw_expr's, and create a map
   from label numbers to source positions as part of this function
*)
let label_prog raw_prog =
  Raw_expr.(
    match raw_prog with
    | Raw_Program flist ->
      let is_func_name (f : string) =
        let rec is_in_list (t : raw_fdecl list) =
          match t with
          | [] -> false
          | f' :: t' -> f'.raw_name = f || is_in_list t' in
        is_in_list flist
     in
      let branch_counter = ref 0 in
      let label_counter = ref 0 in
      let next_branch _ =
      let () = branch_counter := !branch_counter + 1 in
      Branch(!branch_counter - 1) in
    let next_label _ =
      let () = label_counter := !label_counter + 1 in
      Label(!label_counter - 1) in
    let rec label_aexp raw_aexpr =
      match raw_aexpr with
      | Raw_Var s -> Var(Local(s), next_label())
      | Raw_Const -> Const(next_label())
      | Raw_Binop (a, a') ->
        Binop(label_aexp a, label_aexp a', next_label())
      | Raw_Unop a -> Unop(label_aexp a, next_label())
      | Raw_FApp (s, a) ->
        let () = if not (is_func_name s) then
            raise (LabelErr (s ^ " not a function name")) else () in
        FApp(Func(s), label_aexp a, next_label())
    in
    let rec label_expr raw_expr =
      (match raw_expr with
       | Raw_Skip -> Skip
       | Raw_Cond (a, e_t, e_f) ->
         Cond(label_aexp a, label_expr e_t, label_expr e_f,
              next_branch())
       | Raw_Assign (s, a) ->
         Assign(Local(s), label_aexp a)
       | Raw_Seq (e, e') ->
         Seq(label_expr e, label_expr e')
       | Raw_Assert (s, a) ->
         Assert(Local(s), label_aexp a)
       | Raw_AExp a -> AExp(label_aexp a)) in
    let wrap_fold list transformer =
      let out, _ = List.fold_right (fun s (out, i) ->
          ((transformer i s) :: out, i + 1)) list ([], 0) in out
    in
    let label_fdecl raw_fdecl =
      {
        name = Func(raw_fdecl.raw_name);
        params = wrap_fold raw_fdecl.raw_params (fun i s -> Arg(i, s));
        num_params = List.length raw_fdecl.raw_params;
        results = wrap_fold raw_fdecl.raw_results (fun i s -> Ret(i, s));
        num_results = List.length raw_fdecl.raw_results;
        body = label_expr raw_fdecl.raw_body;
      }
    in
    Program (List.fold_left (fun prog fdecl ->
        FuncMap.add (Func(fdecl.raw_name)) (label_fdecl fdecl) prog
      ) FuncMap.empty flist)
  )


exception WrongLenPassed
  
let int_to_digit_repr dig_reprs i =
  if List.length dig_reprs != 10 then
    raise WrongLenPassed else
    let repr i =
      List.nth dig_reprs i in
    if i = 0 then repr 0 else
      let rec step i = if i = 0 then "" else
          step (i / 10) ^ repr (i mod 10) in
      step i
let int_superscript_repr =
  int_to_digit_repr ["⁰"; "¹"; "²"; "³"; "⁴"; "⁵"; "⁶"; "⁷"; "⁷"; "⁹"]

let branch_to_string (Branch i) =
  "ᵖ" ^ (int_superscript_repr i)

let label_to_string (Label i) =
  int_superscript_repr i
        
let program_string (p : program) =
  match p with
  | Program fdecl_map ->
    let rec aexp_repr aexp =
      match aexp with
      | Var (v, l) ->
        (Printf.sprintf "%s%s" (local_to_string v) (label_to_string l))
      | Const l ->
        (Printf.sprintf "0%s" (label_to_string l))
      | Binop (a1, a2, l) ->
        (Printf.sprintf "(%s ⊕%s %s)"
          (aexp_repr a1) (label_to_string l) (aexp_repr a2))
      | Unop (a, l) ->
        (Printf.sprintf "(⊖%s%s)"
          (label_to_string l) (aexp_repr a))
      | FApp (f, a, l) ->
        (Printf.sprintf "%s%s(%s)"
          (func_to_string f) (label_to_string l) (aexp_repr a))
    in
    let rec expr_repr expr =
      match expr with
      | Skip -> "skip"
      | Cond (a, e_t, e_f, b) ->
        Printf.sprintf "if%s [%s] then {\n%s\n} else {\n%s\n}"
          (branch_to_string b) (aexp_repr a)
          (expr_repr e_t) (expr_repr e_f)
      | Assign (v, a) ->
        Printf.sprintf "%s = %s" (local_to_string v) (aexp_repr a)
      | Seq (e1, e2) ->
        Printf.sprintf "%s\n%s"
          (expr_repr e1) (expr_repr e2)
      | Assert (v, a) ->
        Printf.sprintf "assert %s by %s"
          (local_to_string v) (aexp_repr a)
      | AExp a -> aexp_repr a
    in
    let fdecl_repr fdecl =
      Printf.sprintf "def %s:\n%s"
        (func_to_string fdecl.name)
        (expr_repr fdecl.body)
    in
    let acc_fdecl _ fdecl prior_repr =
      (if prior_repr = "" then "" else prior_repr ^ "\n\n") ^ (fdecl_repr fdecl) in
    FuncMap.fold acc_fdecl fdecl_map ""
  
  
