type func = Func of string

type local = Local of string

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
  let compare f1 f2 =
    match (f1, f2) with | (Func name1, Func name2) -> String.compare name1 name2
end

module FuncMap = Map.Make(FuncKey)
type program = Program of fdecl FuncMap.t

exception LabelErr of string

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
      List.fold_left (fun prog fdecl ->
          FuncMap.add (Func(fdecl.raw_name)) (label_fdecl fdecl) prog
        ) FuncMap.empty flist
  )
        
let program_string p =
  (if validate p then "valid " else "invalid ")


