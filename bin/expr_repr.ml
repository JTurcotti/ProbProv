open Expr

exception WrongLenPassed

let int_to_digit_repr dig_reprs i =
  if List.length dig_reprs <> 10 then
    raise WrongLenPassed else
    let repr i =
      List.nth dig_reprs i in
    if i = 0 then repr 0 else
      let rec step i = if i = 0 then "" else
          step (i / 10) ^ repr (i mod 10) in
      step i
let int_superscript_repr =
  int_to_digit_repr ["⁰"; "¹"; "²"; "³"; "⁴"; "⁵"; "⁶"; "⁷"; "⁸"; "⁹"]
let int_subscript_repr =
  int_to_digit_repr ["₀"; "₁"; "₂"; "₃"; "₄"; "₅"; "₆"; "₇"; "₈"; "₉"]

let branch_to_string (Branch i) =
  Printf.sprintf "ᴮ%s" (int_superscript_repr i)

let call_to_string (Call (_, i)) =
  Printf.sprintf "%s" (int_subscript_repr i)

let label_to_string (Label i) =
  Printf.sprintf "ᴸ%s" (int_superscript_repr i)

let assertion_to_string (Assertion i) =
  Printf.sprintf "%s" (int_subscript_repr i)

let list_to_string to_str =
  function
  | [] -> ""
  | x :: l ->
    List.fold_left (fun s y -> s ^ ", " ^ to_str y) (to_str x) l
      
let rec aexp_repr aexp : string =
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
  | FApp (f, a_list, l, c) ->
    (Printf.sprintf "%s%s%s(%s)"
       (func_to_string f) (call_to_string c) (label_to_string l)
       (aexp_reprs a_list))
and aexp_reprs alist = list_to_string aexp_repr alist
    
let program_string (p : program) : string =
  let rec ntabs tabs =
    if tabs = 0 then ""
    else Printf.sprintf "\t%s" (ntabs (tabs - 1))
  in
  let rec expr_repr expr tabs =
    (fun (add_tabs, s) -> if add_tabs
      then (ntabs tabs) ^ s else s)
      (match expr with
       | Skip ->
         true,
         "skip"
       | Cond (a, e_t, e_f, b) ->
         true,
         Printf.sprintf "if%s [%s] then {\n%s\n%s} else {\n%s\n%s}"
           (branch_to_string b) (aexp_repr a)
           (expr_repr e_t (tabs + 1)) (ntabs tabs)
           (expr_repr e_f (tabs + 1)) (ntabs tabs)
       | Assign (v, a) ->
         true,
         Printf.sprintf "%s = %s" (local_to_string v) (aexp_repr a)
       | FAssign (v_list, a) ->
         true,
         Printf.sprintf "%s = %s"
           (list_to_string local_to_string v_list) (aexp_repr a)
       | Seq (e1, e2) ->
         false,
         Printf.sprintf "%s\n%s"
           (expr_repr e1 tabs) (expr_repr e2 tabs)
       | Assert (v, aexp, a) ->
         true,
         Printf.sprintf "assert%s %s by %s"
           (assertion_to_string a) (local_to_string v) (aexp_repr aexp)
       | AExp a ->
         true,
         aexp_repr a
       | Return alist ->
         true,
         Printf.sprintf "return %s" (aexp_reprs alist)
      )
  in
  let fdecl_repr fdecl =
    Printf.sprintf "def %s:\n%s"
      (func_to_string fdecl.name)
       (expr_repr fdecl.body 1)
  in
  let acc_fdecl _ fdecl prior_repr =
    (if prior_repr = "" then "" else prior_repr ^ "\n\n") ^ (fdecl_repr fdecl) in
  FuncMap.fold acc_fdecl p.func_tbl ""


