(* a raw_program is the result of parsing a source file
   it is missing certain key information like labels for lines and branches
   but contains the AST and all identifiers, function names, etc
*)

(* real IMP would have aexp and bexp, we don't care about the difference here *)
type raw_aexp = {data: raw_aexp_data; start_pos: int; end_pos : int}
and raw_aexp_data = 
  | Raw_Var of string
  | Raw_Const
  | Raw_Binop of raw_aexp * raw_aexp
  | Raw_Unop of raw_aexp
  | Raw_FApp of string * (raw_aexp list)

type raw_expr =
  | Raw_Skip
  | Raw_Cond of raw_aexp * raw_expr * raw_expr
  | Raw_Assign of string * raw_aexp
  | Raw_FAssign of (string list) * raw_aexp
  | Raw_Seq of raw_expr * raw_expr
  | Raw_Assert of string * raw_aexp
  | Raw_AExp of raw_aexp
  | Raw_Return of raw_aexp list

type raw_fdecl = {
  raw_name: string;
  raw_params: (string * int * int) list;
  raw_results: (string * int * int) list;
  raw_body: raw_expr;
  raw_pos: (int * int);
}

type raw_program = Raw_Program of raw_fdecl list


(*let validate p =
  match p with
  | Prog flist ->
    let is_func_name (f : string) =
      let rec is_in_list (t : fdecl list) =
        match t with
        | [] -> false
        | f' :: t' -> f'.name = f || is_in_list t' in
      is_in_list flist
    in
    let rec validate_aexp (a : aexp) =
      (match a with
       | Var _ -> true
       | Const -> true
       | Binop (a', a'') -> validate_aexp a' && validate_aexp a''
       | Unop a' -> validate_aexp a'
       | FApp (s, a') -> is_func_name s && validate_aexp a') in
    let rec validate_expr (e : expr) =
      match e with
      | Skip -> true
      | Cond (a, e', e'') -> validate_aexp a && validate_expr e' && validate_expr e''
      | Assign (_, a) -> validate_aexp a
      | Seq (e', e'') -> validate_expr e' && validate_expr e''
      | Assert (_, a) -> validate_aexp a
      | AExp a -> validate_aexp a in
    List.fold_left (fun b fdecl -> b && validate_expr fdecl.body) true flist*)
        
let program_string _ =
  "apple"
