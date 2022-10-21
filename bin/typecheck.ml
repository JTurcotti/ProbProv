open Context
open Expr

let singleton_bind l f =
  match l with
  | [x] -> f x
  | _ -> []

let double_singleton_bind l1 l2 f =
  match (l1, l2) with
  | [v1], [v2] -> f v1 v2
  | _ -> []

let double_option_bind opt1 opt2 f =
  match (opt1, opt2) with
  | Some v1, Some v2 -> f v1 v2
  | _ -> None

let triple_option_bind opt1 opt2 opt3 f =
  match (opt1, opt2, opt3) with
  | Some v1, Some v2, Some v3 -> f v1 v2 v3
  | _ -> None


(* Given a function `f` that operates on lists of lengths `n`,
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
        if List.length l != n then [] else
          let l' = List.filter_map (function
              | [x] -> Some x
              | _ -> None) l in
          if List.length l' = n then f l' else []
    )
      
(* the blame placed on a function's results is a function
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
           (CallEvent(call, Arg(i, s), res))
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
  if List.length blames != fdecl.num_params then
    raise (BadAttemptAtFuncBlame(List.length blames, fdecl.num_params))
  else
    List.map (func_blame_r fdecl label call blames) fdecl.results


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
    | None -> [] in
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
    | None -> []
    | Some fdecl -> (
        let blame_list = List.map (typecheck_aexp prog ctxt) a_list in
        equiv_n_singleton_bind
          fdecl.num_params blame_list (func_blame fdecl l c)
      )

(* use this instead of typecheck_aexp when a single blame
   (i.e. not a multi-result function) is expected *)
let typecheck_aexp_single prog ctxt aexp : blame option =
  match (typecheck_aexp prog ctxt aexp) with
  | [b] -> Some b
  | _ -> None

exception BadMultiAssign of int * int
let rec typecheck_expr prog expr ctxt: context option =
  match expr with
  | Skip ->
    (* noop *)
    Some ctxt
  | Cond (a, e1, e2, branch) ->
    (* a conditional checks each branch separately,
       along with the guarding aexp `a`,
       then combines them using the logic from
       context_merge_cond. Return None if typechecking
       fails for the subaexp or either subexpr*)
    triple_option_bind
      (typecheck_aexp_single prog ctxt a)
      (typecheck_expr prog e1 ctxt)
      (typecheck_expr prog e2 ctxt)
      (fun blame_branch ctxt1 ctxt2 ->
         Some (context_merge_cond
                 branch blame_branch e1 e2 ctxt1 ctxt2))
  | Assign (v, a) ->
    (* an assignment checks the arithmetic expression,
       if it typechecks to a blame then we assign that
       blame into the context at `v`, otherwise we
       return None *)
    (Option.bind (typecheck_aexp_single prog ctxt a)
       (fun blame -> Some (context_assign v blame ctxt)))
  | FAssign (v_list, a) ->
    (* fail gracefully if typechecking aexp a fails,
       throw an exception if the number of variables on the LHS is wrong,
       otherwise perform each assignment *)
    let blame_list = typecheck_aexp prog ctxt a in
    if blame_list = [] then None else
    if List.length v_list != List.length blame_list then
      raise(BadMultiAssign(List.length v_list, List.length blame_list))
    else
      Some (List.fold_right2 context_assign v_list blame_list ctxt)
  | Seq (e1, e2) ->
    (* compose the checking of each subexpr as expected *)
    Option.bind (typecheck_expr prog e1 ctxt) (typecheck_expr prog e2)
  | Assert (v, _) ->
    (* assertions render a value correct - i.e. blame-free *)
    Some (context_assign_zero v ctxt)
  | AExp _ -> Some ctxt
    (* noop *)
    
let typecheck_program _ : context option = None
      
