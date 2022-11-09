open Util

let solve_fail_threshold = 0.0001
exception SolverFailed

let start_token = "<BEGIN SOLS>"
let mid_token = "<END SOLS; BEGIN VALS>"
let end_token = "<END VALS>"
let sol_fmt = "<x(%d)=[%f]>\\n"
let val_fmt = "<eq(%d)@[%f]>\\n"

exception CustomFmtMismatch

let delim_str_to_float delim s =
  match String.split_on_char delim s with
  | [_; tail] ->
    let len = String.length tail in
    if len <= 4 then raise CustomFmtMismatch else
      let float_part = String.sub tail 1 (len - 3) in
      Float.of_string float_part
  | _ -> raise CustomFmtMismatch 
         
let sol_fmt_to_float = delim_str_to_float '='
let val_fmt_to_float = delim_str_to_float '@'
    

let matlab_prog_fmt n_vars eqns_repr =
  Printf.sprintf {|n = %d;
x0 = 0.5 * ones(1, n);
F = @(x) [%s];
[sols, vals] = fsolve(F, x0, optimoptions("fsolve", "Display","none"));
fprintf('%s\n');
for i = 1:length(sols)
   fprintf('%s', i, sols(i));
end;
fprintf('%s\n');
for i = 1:length(vals)
   fprintf('%s', i, vals(i));
end;
fprintf('%s');|}

    n_vars eqns_repr start_token sol_fmt mid_token val_fmt end_token

let dirname = "computation/"
let output_scriptname name = "ocaml_matlab_eqn__" ^ name
let output_filename name = Printf.sprintf "%s%s.m" dirname (output_scriptname name)
let result_filename name = dirname ^ "ocaml_matlab_eqn_out__" ^ name

let matlab_runcmd name = Printf.sprintf
    {|matlab -nojvm -batch "cd %s; %s" > %s|}
    dirname (output_scriptname name) (result_filename name)

(*
An EqnSolver allows you to build up a system of equations over
   variables of some parameterized type, and solve for float values
   of them
*)
module type EqnSolver =
sig
  type var
  type 't varMap
  type expr
  type eqn

  type system

  val const_expr : float -> expr
  val var_expr : var -> expr
  val mult_expr : expr -> expr -> expr
  val add_expr : expr -> expr -> expr
  val sub_expr : expr -> expr -> expr

  val eqn_of : var -> expr -> eqn

  val empty : system
  val add : eqn -> system -> system

  val solve : system -> float varMap
end 

type 'var expr_constr =
    | Const of float
    | Var of 'var
    | Mult of 'var expr_constr list
    | Add of 'var expr_constr list
    | Sub of 'var expr_constr * 'var expr_constr
    
type ('var, 'expr) eqn_constr =
  | Eqn of 'var * 'expr

module EqnSystem (Variable : T) = 
struct
  type var = Variable.t

  module VarSet = Set(Variable)
  type varSet = VarSet.t

  module VarMap = Map(Variable)
  type 't varMap = 't VarMap.t
    
  type expr = var expr_constr

  let const_expr f = Const(f)
  let var_expr v = Var(v)
  let mult_expr e1 e2 =
    (* encode some basic laws of arithmetic *)
    match e1, e2 with
    | Mult e1l, Mult e2l -> Mult (List.append e1l e2l)
    | Mult _, Const 0.0
    | Const 0.0, Mult _ -> Const 0.0
    | Mult el, Const 1.0
    | Const 1.0, Mult el -> Mult el
    | Mult el, e
    | e, Mult el -> Mult (e :: el)
    | Const(f1), Const(f2) -> Const(f1 *. f2)
    | e1, e2 -> Mult [e1; e2]
  let add_expr e1 e2 =
    (* encode some basic laws of arithmetic *)
    match e1, e2 with
    | Add e1l, Add e2l -> Add (List.append e1l e2l)
    | Const 0.0, Add el
    | Add el, Const 0.0 -> Add el
    | Add el, e 
    | e, Add el -> Add (e :: el)
    | Const(f1), Const(f2) -> Const(f1 +. f2)
    | e1, e2 -> Add [e1; e2]

  let sub_expr e1 e2 =
    match e1, e2 with
    | Const(f1), Const(f2) -> Const(f1 -. f2)
    | e1, e2 -> Sub(e1, e2)

  (** ExprArith represents arithmetic over expressions *)
  module ExprArith =
  struct
    type t = expr

    let mult = mult_expr
    let add = add_expr
    let sub = sub_expr

    let one = const_expr 1.
    let zero = const_expr 0.
  end

  type eqn = (var, expr) eqn_constr

  module EqnSet = Set(struct type t = eqn end)
  type eqnSet = EqnSet.t

  let eqn_of v e = Eqn(v, e)

  type system =
    | Sys of varSet * eqnSet

  let vars_of_eqn =
    let rec vars_of_expr =
      function
      | Const _ -> VarSet.empty
      | Var v -> VarSet.singleton v
      | Mult(el) 
      | Add(el) -> list_map_reduce vars_of_expr VarSet.union VarSet.empty el
      | Sub(e1, e2) -> VarSet.union (vars_of_expr e1) (vars_of_expr e2) in
    function
    | Eqn(v, e) -> VarSet.add v (vars_of_expr e)

  let empty = Sys (VarSet.empty, EqnSet.empty)
  let add eqn (Sys (vars, eqns)) =
    Sys(VarSet.union (vars_of_eqn eqn) vars,
        EqnSet.add eqn eqns)

  (* given a list of matlab equations referring to variables
     x(1), x(2), ..., x(n_vars), solve it with matlab and store
     the result to the file result_filename.
     name is a name for the task, and log logs the command run by the task
  *)
  let exec_matlab_solve
      (n_vars : int) (eqns_repr : string) (name : string) (log : string -> unit) : int =
    let matlab_prog_text = matlab_prog_fmt n_vars eqns_repr in
    let oc = open_out (output_filename name) in
    let () = Printf.fprintf oc "%s" matlab_prog_text in
    let () = close_out oc in
    let cmd = matlab_runcmd name in
    log cmd;
    Sys.command cmd
      
  (* read a matlab output file as a list of floats,
     can throw Sys_error  *)
  let read_matlab_result i_var (name : string) : float varMap =
    let ic = open_in (result_filename name) in
    (*skip over everything through start line *)
    let input_or_syserr s = try input_line ic with
        End_of_file -> raise (Sys_error s) in
    let () = while input_or_syserr "start token not found" <> start_token do () done in
    let rec acc_sols i =
      let line = input_or_syserr "mid token not found" in
      if line = mid_token then
        VarMap.empty
      else
        VarMap.add (i_var i) (sol_fmt_to_float line) (acc_sols (i + 1)) in
    let sols = acc_sols 1 in
    let rec acc_vals _ =
      let line = input_or_syserr "end token not found" in
    if line = end_token then
      0.
    else
      max (val_fmt_to_float line) (acc_vals ()) in
    let max_val = acc_vals () in
  if max_val > solve_fail_threshold then
    raise SolverFailed
  else
    sols
      
  exception SolveFailure of string
  exception BadSystem of string

  (** given a system set up with the equations eqns and the variables vars
      (though theoretically vars could be computed from eqns), solve it!
      takes a name to associate with the intermediate files of the
      computation for debugging's sake.
  *)
  let solve (Sys(vars, eqns)) (name : string) (log : string -> unit) : float varMap = 
    let n_vars = VarSet.cardinal vars in
    let () = if not (n_vars > 0) then raise
          (BadSystem (name ^ " system needs at least 1 variable")) else () in
    let vars_list = VarSet.elements vars in
        let vars_index, _ = List.fold_left (fun (mp, i) var ->
        (* NOTE: MATLAB arrays start at 1 *)
        (VarMap.add var i mp , i + 1)) (VarMap.empty, 1) vars_list in
    let var_i v = VarMap.find v vars_index in
    let i_var i = List.nth vars_list (i - 1) in 
    let rec expr_repr = function
      | Const f -> Printf.sprintf "%f" f
      | Var v -> Printf.sprintf "x(%d)" (var_i v)
      | Mult(el) ->
        Printf.sprintf "(%s)" (list_map_reduce_nonempty expr_repr
                                 (Printf.sprintf "%s * %s") el)
      | Add(el) ->
        Printf.sprintf "(%s)" (list_map_reduce_nonempty expr_repr
                                 (Printf.sprintf "%s + %s") el)
      | Sub(e1, e2) ->
        Printf.sprintf "(%s - %s)" (expr_repr e1) (expr_repr e2) in
    let eqn_repr = function
      | Eqn(v, e) -> Printf.sprintf "x(%d) - (%s)" (var_i v) (expr_repr e) in
    let eqns_repr = EqnSet.fold (fun eqn repr ->
        Printf.sprintf "%s, %s" (eqn_repr eqn) repr) eqns "" in
    try
      let out_code = exec_matlab_solve n_vars eqns_repr name log in
      let () = if out_code <> 0 then
          raise (Sys_error (Printf.sprintf "%s matlab call failed (%d)"
                              name out_code)) else ()  in
      read_matlab_result i_var name
    with Sys_error s ->
      raise (SolveFailure s)
end

