open Types
open Expr

let double_option_bind opt1 opt2 f =
  match (opt1, opt2) with
  | Some v1, Some v2 -> f v1 v2
  | _ -> None
    

let rec typecheck_aexp aexp ctxt : blame option =
  match aexp with
  | Var (x, l) ->
    Option.bind (context_lookup x ctxt) (fun b ->
        Some (blame_merge b (blame_one (LabelSite l)))
      )
  | Const l ->
    Some (blame_one (LabelSite l))
  | Binop (a1, a2, l) ->
    double_option_bind
      (typecheck_aexp a1 ctxt) (typecheck_aexp a2 ctxt)
      (fun b1 b2 ->
         Some (blame_merge
                 (blame_one (LabelSite l))
                 (blame_merge b1 b2)))
  | Unop (a, l) ->
    Option.bind (typecheck_aexp a ctxt) (fun b ->
        Some (blame_merge b (blame_one (LabelSite l))))
  | FApp (f, a, l) ->
    Option.bind (typecheck_aexp a ctxt) (fun b ->
        




let typecheck_program _ : context option = None
