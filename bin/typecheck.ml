open Context
open Expr
open Util

let singleton_bind l f =
  match l with
  | [x] -> f x
  | _ -> []

let double_singleton_bind l1 l2 f =
  match (l1, l2) with
  | [v1], [v2] -> f v1 v2
  | _ -> []

let double_option_bind f opt1 opt2 =
  match (opt1, opt2) with
  | Some v1, Some v2 -> f v1 v2
  | _ -> None

let triple_option_bind f opt1 opt2 opt3 =
  match (opt1, opt2, opt3) with
  | Some v1, Some v2, Some v3 -> f v1 v2 v3
  | _ -> None


(** Given a function `f` that operates on lists of lengths `n`,
   if `l` is of the form
   [[a1, a2, ..., an]] or [[a1], [a2], ..., [an]]
   then return f ([a1, a2, ..., an])
   otherwise return []
   *)
let equiv_n_singleton_bind n l f =
  match n with
  | 0 -> f([])
  | 1 -> (match l with
      | [[x]] -> f [x]
      | _ -> [])
  | _ -> (
      match l with
      | [l'] ->
        if List.length l' = n then f l' else []
      | _ ->
        if List.length l <> n then [] else
          let l' = List.filter_map (function
              | [x] -> Some x
              | _ -> None) l in
          if List.length l' = n then f l' else []
    )
      
(** the blame placed on a function's results is a function
   of the blame placed on its arguments. For the function declared
   by `fdecl`'s `i`th callsite, this computes the blame on result
   `res` given argument blames `blames` - note that there's a
   component that depends on the input blame (the CallEvent's),
   and a component that does not (the CallSite) - also note
   that the result always depends fully on the label of the function
   identifier itself - `label` *)
let func_blame_r fdecl label call blames res : blame =
  let acc : arg -> blame -> blame =
    (fun (Arg(i, s)) ->
      blame_merge 
        (blame_external_conj
           (CallEvent(call, Arg(i, s), res, true))
           (List.nth blames i))
    )
  in
  List.fold_right acc fdecl.params (
    blame_merge
      (blame_one (LabelSite(label)))
      (blame_one (CallSite(call, res))))


(*
   func_blame returns a list of the blames placed on each
   result of the function call to `fdecl` identified by an
   identifier with the label `label`, callsite `call`, and
   argument blames `blames`
   *)
exception BadAttemptAtFuncBlame of int * int
let func_blame fdecl label call blames : blame list =
  if List.length blames <> fdecl.num_params then
    raise (BadAttemptAtFuncBlame(List.length blames, fdecl.num_params))
  else
    List.map (func_blame_r fdecl label call blames) fdecl.results

exception ArithmeticTypecheckingError of string

(*
   This function attempts to typecheck (i.e. provide a blame for)
   the arithmetic expression aexp. If it fails, [] is returned.
   If it succeeds and the result is a single blame b, [b] is returned.
   In the special case of multi-return functions that return blames
   b1, ..., bn, [b1, ..., bn] is returned
   *)
let rec typecheck_aexp prog ctxt aexp : blame list =
  let lookup x =
    match context_lookup x ctxt with
    | Some v -> [v]
    | None -> raise (ArithmeticTypecheckingError (Format.sprintf "Undefined local variable %s" (local_to_string x))) in
  match aexp with
  | Var (x, l) ->
    (* if the variable can be looked up, add blame for the site `l`
       to what was looked up, otherwise fail with [] *)
    singleton_bind (lookup x) (fun b ->
        [blame_merge b (blame_one (LabelSite l))]
      )
  | Const l ->
    (* provide blame for the site `l` *)
    [blame_one (LabelSite l)]
  | Binop (a1, a2, l) ->
    (* if both subaexps succeed, add blame for the site `l` to the
       merge of the two results, otherwise fail with [] *)
    double_singleton_bind
      (typecheck_aexp prog ctxt a1) (typecheck_aexp prog ctxt a2)
      (fun b1 b2 ->
         [blame_merge
            (blame_one (LabelSite l))
            (blame_merge b1 b2)])
  | Unop (a, l) ->
    (* if subaexp succeeds, add blame for the site `l`, otherwise
       fail with [] *)
    singleton_bind (typecheck_aexp prog ctxt a) (fun b ->
        [blame_merge b (blame_one (LabelSite l))])
  | FApp (f, a_list, l, c) ->
    (* slightly more subtle - see function func_blame for logic
       if the list of arguments don't all succeed, or if there
       are the wrong number of them, fails with []
    *)
    match lookup_func_opt f prog with
    | None -> raise (ArithmeticTypecheckingError (Format.sprintf "Undefined function %s" (func_to_string f)))
    | Some fdecl -> (
        let blame_list = List.map (typecheck_aexp prog ctxt) a_list in
        equiv_n_singleton_bind
          fdecl.num_params blame_list (func_blame fdecl l c)
      )

(** use this instead of typecheck_aexp when a single blame
   (i.e. not a multi-result function) is expected *)
let typecheck_aexp_single prog ctxt aexp : blame option =
  match (typecheck_aexp prog ctxt aexp) with
  | [b] -> Some b
  | _ -> None

(** pc_type represents a stack of branches that influenced the current
    pc, along with the blame value for the aexp guarding those branches *)
type pc_type = (branch * bool * blame) list

(** typechecking aims to output blames for assertions and returns,
    so track those in an output_blames struct *)
type output_blames = {
  ret_blames: blame list;
  assert_blames: blame AssertionMap.t}

let empty_output i = {
  ret_blames=List.init i (fun _ -> blame_zero);
  assert_blames=AssertionMap.empty
}

let add_assertion_blame output_blames a blame =
  {output_blames with
   assert_blames=
     AssertionMap.add a blame output_blames.assert_blames}

exception BadAssertMerge of assertion
let merge_assertion_blames = AssertionMap.merge
    (fun a b1 b2 -> match b1, b2 with
       | Some blame, None
       | None, Some blame -> Some blame
       (* the same assertion shouldn't be declared in two places *)
       | _ -> raise (BadAssertMerge a))

let add_return_blame output_blames ret_blames =
  {output_blames with
   ret_blames=List.map2 blame_merge output_blames.ret_blames ret_blames}

exception BadRetMerge of int * int
let merge_output_blames
    {ret_blames=r1; assert_blames=a1}
    {ret_blames=r2; assert_blames=a2} =
  let len1, len2 = List.length r1, List.length r2 in
  if len1 <> len2 then raise (BadRetMerge(len1, len2)) else
    {ret_blames=List.rev_map2 blame_merge r1 r2;
     assert_blames=merge_assertion_blames a1 a2}
    
(** flow_ctxt represents the typechecking context for tracking
    trough flow through non-terminal expressions (ones that don't end
    with a return). It includes a blame context, a pc influence stack,
    and a current return  blame for any returns that could have occurred
    so far *)
type flow_ctxt = {local_blames: context;
                  pc: pc_type;
                  output: output_blames}

(** this represents passing a context through a branch -
    adding it to the pc stack and conjuncting all local
    blames with the branch event *)
let flow_ctxt_branch_conj flow_ctxt branch dir blame =
  {flow_ctxt with
   local_blames=context_branch_conj branch dir flow_ctxt.local_blames;
   pc=(branch, dir, blame) :: flow_ctxt.pc}

exception TypecheckingLogicError of string

(**
   take a pc stack containing the branch `br`, and remove all elements
   up to and including `br`
*)
let rec pc_strip_to_branch br =
  function
  | [] -> raise (TypecheckingLogicError "branch not found in pc")
  | (br', _, _) :: tail ->
    if br' = br then tail else pc_strip_to_branch br tail

(** this is the result of typechecking an expresssion:
    if non-terminal, a flow_ctxt; if a terminal, raw blames corresponding
    to the return values; or an error *)
type typecheck_result =
  | NonTerminal of flow_ctxt
  | Terminal of output_blames
  | Error of string

let merge_typecheck_results_across_branch br res1 res2 : typecheck_result =
  try
    match res1, res2 with
    (* propagate errors *)
    | Error e1, Error e2 ->
      Error (Printf.sprintf "%s; %s" e1 e2)
    | Error e, _ | _, Error e -> Error e
    | NonTerminal ctxt_t, NonTerminal ctxt_f ->
      let pc_t, pc_f = pc_strip_to_branch br ctxt_t.pc,
                       pc_strip_to_branch br ctxt_f.pc in
      if pc_t <> pc_f then
        raise (TypecheckingLogicError "residual pc should be equal across branches")
      else
        NonTerminal {
          local_blames =
            context_merge ctxt_t.local_blames ctxt_f.local_blames;
          pc = pc_t;
          output = merge_output_blames ctxt_t.output ctxt_f.output
        }
    | NonTerminal ctxt_t, Terminal out_f ->
      NonTerminal {ctxt_t with
                  output=merge_output_blames ctxt_t.output out_f}
    | Terminal out_t, NonTerminal ctxt_f ->
      NonTerminal {ctxt_f with
                  output=merge_output_blames out_t ctxt_f.output}
    | Terminal out_t, Terminal out_f ->
      Terminal (merge_output_blames out_t out_f)
  with
  | BadRetMerge(len1, len2) ->
    Error (Printf.sprintf
             "returns across branch %s contained %d and %d values"
             (Expr_repr.branch_to_string br) len1 len2)
  | BadAssertMerge a ->
    Error (Printf.sprintf
             "assertion %s occured twice across branch %s"
             (Expr_repr.assertion_to_string a)
             (Expr_repr.branch_to_string br))

let taint_with_pc pc blame : blame =
  let rec accumulate_taint pc guard blame =
    match pc with
    | [] -> blame
    | (br, dir, br_blame) :: pc_tail ->
      let br_pos, br_neg = branch_event br dir, branch_event br (not dir) in
      let new_guard = event_conj br_pos guard in
      let implicit_event = event_disj new_guard br_neg in
      let new_blame = blame_merge
          (blame_event_conj blame br_pos)
          (blame_event_conj br_blame implicit_event) in
      accumulate_taint pc_tail new_guard new_blame in
  accumulate_taint pc event_one blame

(**
   This is the main typechecking workhorse - performs typechecking of
   expressions!
*)
let rec typecheck_expr prog flow_ctxt : expr -> typecheck_result =
  let typecheck_expr = typecheck_expr prog in
  let typecheck_nonterminal flow_ctxt expr action =
    match typecheck_expr flow_ctxt expr with
    | NonTerminal ctxt -> action ctxt
    | Terminal _ -> Error "Unreachable code"
    | Error e -> Error e in
  let typecheck_aexp = typecheck_aexp prog flow_ctxt.local_blames in
  function
  | Skip | AExp _ -> (* noops *) NonTerminal flow_ctxt
  | Assign (x, a) -> (
      match (typecheck_aexp a) with
      | [a_blame] ->
        (* unary expression, as expected, so perform assignment and continue *)
        let tainted_blame = taint_with_pc flow_ctxt.pc a_blame in
        NonTerminal {flow_ctxt with
                     local_blames =
                       context_assign
                         x tainted_blame flow_ctxt.local_blames}
      | [] ->
        (* aexp typechecking failed *)
        Error (Format.sprintf
                 "aexp in '%s = %s' did not typecheck"
                 (local_to_string x)
                 (Expr_repr.aexp_repr a))
      | _ ->
        (* aexp was multi-valued *)
        Error (Format.sprintf
                 "aexp in '%s = %s' is multi-valued"
                 (local_to_string x)
                 (Expr_repr.aexp_repr a))
    )
  | FAssign (x_list, a) -> (
      let a_blames = typecheck_aexp a in
      let x_len, a_len = List.length x_list, List.length a_blames in
      if x_len <> a_len then
        Error (Format.sprintf
                 "aexp '%s' in assignment expected to be %d-valued but was %d-valued"
                 (Expr_repr.aexp_repr a) x_len a_len)
      else
        NonTerminal {flow_ctxt with
                     local_blames =
                       List.fold_right2 context_assign x_list a_blames
                         flow_ctxt.local_blames}
    )
  | Seq (e1, e2) -> (
      typecheck_nonterminal flow_ctxt e1 (fun flow_ctxt ->
          typecheck_expr flow_ctxt e2)
    )
  | Assert (x, _, a) -> (
      match context_lookup x flow_ctxt.local_blames with
      | None -> Error (Format.sprintf
                         "local '%s' in assertion not defined"
                         (local_to_string x))
      | Some blame -> NonTerminal {
          flow_ctxt with
          (* after the assertion, this value is known to be correct *)
          local_blames=context_assign_zero x flow_ctxt.local_blames;
          (* record the blame for the asserted value *)
          output=add_assertion_blame flow_ctxt.output a blame}
    )
  | Return a_list -> (
      let a_blames = List.fold_right
          (compose typecheck_aexp List.append) a_list [] in
      let tainted_blames = List.map (taint_with_pc flow_ctxt.pc) a_blames in
      let curr_ret_len, a_len =
        List.length flow_ctxt.output.ret_blames,
        List.length a_blames in
      if curr_ret_len = a_len then
        Terminal (add_return_blame flow_ctxt.output tainted_blames)
      else
        Error (Format.sprintf
                 "'return %s' provided %d values but prior return provided %d"
                 (Expr_repr.aexp_reprs a_list) a_len curr_ret_len)
    )
  | Cond(a, e_t, e_f, br) -> (
      match typecheck_aexp a with
      | [a_blame] ->
        merge_typecheck_results_across_branch br
          (typecheck_expr
             (flow_ctxt_branch_conj flow_ctxt br true a_blame)
             e_t)
          (typecheck_expr
             (flow_ctxt_branch_conj flow_ctxt br false a_blame)
             e_f)
      | _ -> Error (Format.sprintf "aexp '%s' in branch %s is multi-valued"
                      (Expr_repr.aexp_repr a)
                      (Expr_repr.branch_to_string br))
    )

let fdecl_starting_ctxt fdecl : flow_ctxt =
  {local_blames=
     List.fold_right
       (fun (Arg(i, s)) -> 
          context_assign (Local(s)) (blame_one (ArgSite(Arg(i, s)))))
       fdecl.params context_empty;
   pc=[];
   output=empty_output (List.length fdecl.results)}

exception IllTypedFunction of string

let typecheck_fdecl prog fdecl : output_blames =
  match typecheck_expr prog (fdecl_starting_ctxt fdecl) fdecl.body with
  | Terminal out -> out
  | NonTerminal _ ->
    raise (IllTypedFunction (Format.sprintf
                               "Function %s is missing a return statement"
                               (func_to_string fdecl.name)))
  | Error e ->
    raise (IllTypedFunction (Format.sprintf
                               "Function %s is ill-typed: %s"
                               (func_to_string fdecl.name) e))

(**
   provides a complete typechecked program. Functions are mapped to
   their declarations and a `context` if they were successfully typechecked.
   The remaining maps provide source-file-byte-indexed information about
   what is represented by each byte for pretty printing
   *)
type typechecked_program = {tfunc_tbl: (fdecl * blame list) FuncMap.t;
                            assertion_blames: blame AssertionMap.t;
                            label_tbl: label IntMap.t;
                            arg_tbl: (func * arg) IntMap.t;
                            ret_tbl: (func * ret) IntMap.t}

let typecheck_program prog : typechecked_program =
  FuncMap.fold (fun fname fdecl tprog ->
      let {ret_blames=ret_blames; assert_blames=assert_blames} =
        typecheck_fdecl prog fdecl in
      {tprog with
       tfunc_tbl=FuncMap.add fname (fdecl, ret_blames) tprog.tfunc_tbl;
       assertion_blames=merge_assertion_blames assert_blames tprog.assertion_blames}
    ) prog.func_tbl 
    {tfunc_tbl=FuncMap.empty;
     assertion_blames=AssertionMap.empty;
     label_tbl=prog.label_tbl;
     arg_tbl=prog.arg_tbl;
     ret_tbl=prog.ret_tbl}

(**
   this exists to abstract the process of indexing information about
   association of objects (e.g. branches labels) with enclosing functions
*)
module Indexer (T : T)
    (ExprExtract : sig val expr_extract : expr -> Set(T).t end) =
struct
  exception Unexpected
  
  module M = Map(T)
  module S = Set(T)
  let index : typechecked_program -> fdecl Map(T).t =
    fun tprogram ->
    FuncMap.fold (
      fun _ (fdecl, _) ->
        M.union
          (fun _ _ _ -> raise Unexpected) (* unioned maps should be disjoint *)
          (M.from_elem_foo
             (S.elements (ExprExtract.expr_extract fdecl.body))
             (fun _ -> fdecl))
    ) tprogram.tfunc_tbl M.empty
end

module LabelIndexer = Indexer(LabelT)
    (struct let expr_extract = expr_labels end)
let index_labels = LabelIndexer.index

module BranchIndexer = Indexer(BranchT)
    (struct let expr_extract = expr_branches end)
let index_branches = BranchIndexer.index
    
