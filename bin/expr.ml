open Util

type func = Func of string
let func_to_string (Func s) = s

type local = Local of string
let local_to_string (Local s) = s

module LocalT = struct type t = local end
module LocalMap = Map(LocalT)
module LocalSet = Set(LocalT)

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
  | Cond of aexp (* the guard *)
            * expr (* true branch *)
            * expr (* false branch *)
            * branch (* branch label *)
            * bool (* true branch ends in return? *)
            * bool (* false branch ends in return? *)
  | Assign of local * aexp
  | FAssign of (local list) * aexp (* multi-assign to a function result *)
  | Seq of expr * expr
  | Assert of local * aexp
  | AExp of aexp
  | Return of aexp list

type fdecl = {
  name: func;
  params: arg list;
  num_params: int;
  results: ret list;
  num_results: int;
  body: expr; (* the meat *)
}

module Func = struct
  type t = func
end

module Int = struct
  type t = int
end

module FuncMap = Map(Func)
module IntMap = Map(Int)
module IntSet = Set(Int)
type program = {func_tbl: fdecl FuncMap.t;
                label_tbl: label IntMap.t;
                arg_tbl: (func * arg) IntMap.t;
                ret_tbl: (func * ret) IntMap.t}

let lookup_func_opt f prog : fdecl option =
  FuncMap.find_opt f prog.func_tbl

let rec expr_ends_with_ret =
  (function
    | Skip | Assign (_, _) | FAssign(_, _) | Assert(_, _) | AExp _ ->
      false
    | Cond (_, _, _, _, t_rets, f_rets) ->
      t_rets && f_rets
    | Seq (_, e) ->
      expr_ends_with_ret e
    | Return _ ->
      true
  )


exception LabelErr of string

exception ReturnPlacementYieldsUnreachableCode
exception FunctionMissingReturn

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
          FApp(f, label_aexps a_list,
               next_label s_pos e_pos, next_call f)
      and label_aexps alist = List.map label_aexp alist
      in
      let rec label_expr =
        (function
          | Raw_Skip -> Skip
          | Raw_Cond (a, e_t, e_f) ->
            let e_t', e_f' = label_expr e_t, label_expr e_f in
            Cond(label_aexp a, e_t', e_f',
                 next_branch(),
                 expr_ends_with_ret e_t',
                 expr_ends_with_ret e_f')
         | Raw_Assign (s, a) ->
           Assign(Local(s), label_aexp a)
         | Raw_FAssign (s_list, a) ->
           FAssign(List.map (fun s -> Local(s)) s_list, label_aexp a)
         | Raw_Seq (e, e') ->
           Seq(label_expr e, label_expr e')
         | Raw_Assert (s, a) ->
           Assert(Local(s), label_aexp a)
         | Raw_AExp a -> AExp(label_aexp a)
         | Raw_Return alist -> Return(label_aexps alist)
        ) in
      (*validate_expr ensures there is no unreachable code in this expression,
          or else raises an exception *)
      let rec validate_expr expr =
        match expr with
        | Seq (e1, e2) -> (
            if expr_ends_with_ret e1 then
              raise ReturnPlacementYieldsUnreachableCode else
              validate_expr e1; validate_expr e2)
        | Cond(_, e_t, e_f, _, _, _) -> (
            validate_expr e_t; validate_expr e_f)
        | _ -> () in
      let validate_func_body body =
        let () =
          validate_expr body;
          if not (expr_ends_with_ret body) then
            raise FunctionMissingReturn else () in
        body in
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
          body = validate_func_body (label_expr raw_fdecl.raw_body);
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

let aexpr_label : aexp -> label =
  function
  | Var (_, l) -> l
  | Const l -> l
  | Binop (_, _, l) -> l
  | Unop (_, l) -> l
  | FApp (_, _, l, _) -> l

let rec expr_labels : expr -> LabelSet.t =
  function
  | Skip -> LabelSet.empty
  | Cond (a, e1, e2, _, _, _) ->
    LabelSet.union (aexpr_labels a) (LabelSet.union
                                       (expr_labels e1)
                                       (expr_labels e2))
  | Assign (_, a) -> aexpr_labels a
  | FAssign (_, a) -> aexpr_labels a
  | Seq (e1, e2) -> LabelSet.union (expr_labels e1) (expr_labels e2)
  | Assert (_, a) -> aexpr_labels a
  | AExp a -> aexpr_labels a
  | Return alist -> List.fold_right
                      (compose aexpr_labels LabelSet.union)
                      alist LabelSet.empty

let rec expr_branches : expr -> BranchSet.t =
  function
  | Cond (_, e1, e2, b, _, _) ->
    BranchSet.add b (
      BranchSet.union
        (expr_branches e1)
        (expr_branches e2))
  | Seq (e1, e2) ->
    BranchSet.union
      (expr_branches e1)
      (expr_branches e2)
  | _ -> BranchSet.empty

let rec aexp_locals : aexp -> LocalSet.t =
  function
  | Var (l, _) -> LocalSet.singleton l
  | Const _ -> LocalSet.empty
  | Binop (a1, a2, _) -> LocalSet.union
                           (aexp_locals a1)
                           (aexp_locals a2)
  | Unop (a, _) -> aexp_locals a
  | FApp (_, al, _, _) ->
    list_map_reduce aexp_locals LocalSet.union LocalSet.empty al
