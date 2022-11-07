open Util

type func = Func of string
let func_to_string (Func s) = s

type local = Local of string
let local_to_string (Local s) = s

(* these types contain a bit of redundancy - the int is the number
   of the art/ret and the string is the name *)
type arg = Arg of int * string
type ret = Ret of int * string

module ArgT = struct type t = arg end
module RetT = struct type t = ret end

module ArgMap = Map(ArgT)
module RetMap = Map(RetT)

(* the ints in each of these are unique identifiers *)
type branch = Branch of int
type label = Label of int
type call = Call of func * int


module BranchT = struct type t = branch end
module LabelT = struct type t = label end
module CallT = struct type t = call end

module BranchMap = Map(BranchT)
module BranchSet = Set(BranchT)
module LabelMap = Map(LabelT)
module LabelSet = Set(LabelT)
module CallMap = Map(CallT)
module CallSet = Set(CallT)

type aexp =
  | Var of local * label
  | Const of label
  | Binop of aexp * aexp * label
  | Unop of aexp * label
  | FApp of func * (aexp list) * label * call

type expr =
  | Skip
  | Cond of aexp * expr * expr * branch
  | Assign of local * aexp
  | FAssign of (local list) * aexp
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

module Func = struct
  type t = func
end

module Int = struct
  type t = int
end

module FuncMap = Map(Func)
module IntMap = Map(Int)
type program = {func_tbl: fdecl FuncMap.t;
                label_tbl: label IntMap.t;
                arg_tbl: (func * arg) IntMap.t;
                ret_tbl: (func * ret) IntMap.t}

let lookup_func_opt f prog : fdecl option =
  FuncMap.find_opt f prog.func_tbl

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
      (* each counter begins at 1 to reserve 0 as a special value *)
      (* we use this to ensure each branch gets a distinct index *)
      let branch_counter = ref 1 in
      (* we use this to ensure each line gets a distinct label *)
      let label_counter = ref 1 in
      (* we use this to ensure each call to the same function
         gets a distinct index *)
      let call_counter = ref 1 in
      (* we use this to track the labels that source positions correspond
         to as we assign them *)
      let label_tbl = ref IntMap.empty in
      let arg_tbl = ref IntMap.empty in
      let ret_tbl = ref IntMap.empty in
      let update_tbl s e tbl v =
        for i = s to e - 1 do
          tbl := IntMap.add i v !tbl
        done in
      let inc_counter wrap_i c _ =
        let () = c := !c + 1 in
        wrap_i (!c - 1) in
      let next_branch _ =
        inc_counter (fun i -> Branch i) branch_counter () in
      let next_label s_pos e_pos  =
        let l = inc_counter (fun i -> Label i) label_counter () in
        update_tbl s_pos e_pos label_tbl l; l in
      let next_call f =
        inc_counter (fun i -> Call(f, i)) call_counter () in
      let get_arg i s s_pos e_pos fname =
        let a = Arg(i, s) in
        update_tbl s_pos e_pos arg_tbl (fname, a); a in
      let get_ret i s s_pos e_pos fname =
        let r = Ret(i, s) in
        update_tbl s_pos e_pos ret_tbl (fname, r); r in
      
      let rec label_aexp {data=raw_aexp; start_pos=s_pos; end_pos=e_pos} =
        match raw_aexp with
      | Raw_Var s -> Var(Local(s), next_label s_pos e_pos)
      | Raw_Const -> Const(next_label s_pos e_pos)
      | Raw_Binop (a, a') ->
        Binop(label_aexp a, label_aexp a', next_label s_pos e_pos)
      | Raw_Unop a -> Unop(label_aexp a, next_label s_pos e_pos)
      | Raw_FApp (s, a_list) ->
        let () = if not (is_func_name s) then
            raise (LabelErr (s ^ " not a function name")) else () in
        let f = Func(s) in
        FApp(f, List.map label_aexp a_list,
             next_label s_pos e_pos, next_call f)
    in
    let rec label_expr raw_expr =
      (match raw_expr with
       | Raw_Skip -> Skip
       | Raw_Cond (a, e_t, e_f) ->
         Cond(label_aexp a, label_expr e_t, label_expr e_f,
              next_branch())
       | Raw_Assign (s, a) ->
         Assign(Local(s), label_aexp a)
       | Raw_FAssign (s_list, a) ->
         FAssign(List.map (fun s -> Local(s)) s_list, label_aexp a)
       | Raw_Seq (e, e') ->
         Seq(label_expr e, label_expr e')
       | Raw_Assert (s, a) ->
         Assert(Local(s), label_aexp a)
       | Raw_AExp a -> AExp(label_aexp a)) in
    let wrap_fold list transformer =
      let out, _ = List.fold_right (fun s (out, i) ->
          ((transformer i s) :: out, i - 1)) list ([], List.length list - 1) in out
    in
    let label_fdecl raw_fdecl =
      let fname = Func(raw_fdecl.raw_name) in
      {
        name = fname;
        params = wrap_fold raw_fdecl.raw_params
            (fun i (name, s_pos, e_pos)  -> get_arg i name s_pos e_pos fname);
        num_params = List.length raw_fdecl.raw_params;
        results = wrap_fold raw_fdecl.raw_results
            (fun i (name, s_pos, e_pos) -> get_ret i name s_pos e_pos fname);
        num_results = List.length raw_fdecl.raw_results;
        body = label_expr raw_fdecl.raw_body;
      }
    in
    let func_tbl = List.fold_left (fun prog fdecl ->
        FuncMap.add (Func(fdecl.raw_name)) (label_fdecl fdecl) prog
      ) FuncMap.empty flist in
    {func_tbl=func_tbl;
     label_tbl=(!label_tbl);
     arg_tbl=(!arg_tbl);
     ret_tbl=(!ret_tbl)}
  )

let rec aexpr_labels : aexp -> LabelSet.t =
  function
  | Var (_, l) -> LabelSet.singleton l
  | Const l -> LabelSet.singleton l
  | Binop (a1, a2, l) -> LabelSet.add l (LabelSet.union
                                           (aexpr_labels a1)
                                           (aexpr_labels a2))
  | Unop (a, l) -> LabelSet.add l (aexpr_labels a)
  | FApp (_, a_list, l, _) ->
    LabelSet.add l (List.fold_right (fun a ls ->
        LabelSet.union (aexpr_labels a) ls) a_list LabelSet.empty)

let rec expr_labels : expr -> LabelSet.t =
  function
  | Skip -> LabelSet.empty
  | Cond (a, e1, e2, _) ->
    LabelSet.union (aexpr_labels a) (LabelSet.union
                                       (expr_labels e1)
                                       (expr_labels e2))
  | Assign (_, a) -> aexpr_labels a
  | FAssign (_, a) -> aexpr_labels a
  | Seq (e1, e2) -> LabelSet.union (expr_labels e1) (expr_labels e2)
  | Assert (_, a) -> aexpr_labels a
  | AExp a -> aexpr_labels a
                
let rec expr_branches : expr -> BranchSet.t =
  function
  | Cond (_, e1, e2, b) ->
    BranchSet.add b (
      BranchSet.union
        (expr_branches e1)
        (expr_branches e2))
  | Seq (e1, e2) ->
    BranchSet.union
      (expr_branches e1)
      (expr_branches e2)
  | _ -> BranchSet.empty
