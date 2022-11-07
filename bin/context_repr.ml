open Context
open Expr
open Expr_repr
open Util
  
let aee_repr (CallEvent(Call(Func(s), i_f), Arg(i_a, _), Ret(i_r, _), b)) =
  Printf.sprintf "ϕ%s⟨%s%s⟩ₐ%sʳ%s"
    (unicode_bar_cond b)
    s
    (int_subscript_repr i_f)
    (int_subscript_repr i_a)
    (int_superscript_repr i_r)

let aee_conj_repr aee_conj =
  if AEEConjunctiveSet.is_empty aee_conj then
    "1"
  else
    AEEConjunctiveSet.fold
      (fun aee s -> (aee_repr aee) ^ s) aee_conj ""

let external_event_repr ext_ev =
  if AEEDNFSet.is_empty ext_ev then "0" else
    let fst = AEEDNFSet.choose ext_ev in
    AEEDNFSet.fold
      (fun aee_conj ->
         Printf.sprintf "%s + %s" (aee_conj_repr aee_conj))
      (AEEDNFSet.remove fst ext_ev) (aee_conj_repr fst)

let aie_repr (AIE(Branch(i), dir)) =
  Printf.sprintf "π%s%s" (unicode_bar_cond dir) (int_subscript_repr i)
    

let internal_event_repr int_ev =
  if BranchMap.is_empty int_ev then
    "1"
  else
    BranchMap.fold
      (fun b dir s -> (aie_repr (AIE(b, dir)) ^ s)) int_ev ""

let map_repr
    is_empty choose remove fold
    zero_repr k_repr v_repr k_combine_v_str kv_combine_str map =
  let kv_repr k v =
    Printf.sprintf k_combine_v_str (k_repr k) (v_repr v) in
  if is_empty map then zero_repr else
    let (fst_k, fst_v) = choose map in
    fold (fun k v -> Printf.sprintf kv_combine_str (kv_repr k v))
      (remove fst_k map) (kv_repr fst_k fst_v)

let event_repr =
  map_repr
    IEMap.is_empty IEMap.choose IEMap.remove IEMap.fold
    "0" internal_event_repr external_event_repr "%s*[%s]" "%s ∨ %s" 

let site_repr = function
  | LabelSite(Label(i)) -> 
    Printf.sprintf "L%s" (int_subscript_repr i)
  | CallSite (Call (Func f_s, f_i), Ret (r_i, _)) -> 
    Printf.sprintf "Β⟨%s%s⟩ʳ%s"
      f_s (int_subscript_repr f_i) (int_superscript_repr r_i)
  | ArgSite (Arg (i, s)) -> 
    Printf.sprintf "α%s⟨%s⟩" (int_subscript_repr i) s
  | PhantomRetSite (Ret (i, s)) ->
    Printf.sprintf "ρ%s⟨%s⟩" (int_subscript_repr i) s

let blame_repr =
  map_repr
    SiteMap.is_empty SiteMap.choose SiteMap.remove SiteMap.fold
    "0" site_repr event_repr "\t%s ↦ %s" "%s\n%s"

let local_repr (Local s) = s

let context_repr_prim local_repr =
  map_repr
    LocalMap.is_empty LocalMap.choose LocalMap.remove LocalMap.fold
    "∅" local_repr blame_repr "%s ↦ {\n%s}" "%s\n%s"

let context_repr = context_repr_prim local_repr

let context_repr_fdecl_out fdecl =
  let lookup_local s =
    List.fold_left (function
        | Some r -> fun _ -> Some r
        | None -> fun (Ret(i, s2)) ->
          if s = s2 then Some (Ret(i, s)) else None)
      None fdecl.results in
  let local_repr (Local s) =
    match lookup_local s with
    | Some (Ret(i, s)) -> Printf.sprintf "ρ%s⟨%s⟩"
                            (int_subscript_repr i) s
    | None -> s
  in
  context_repr_prim local_repr  

let func_repr (Func s) = s

open Typecheck
  
let typechecked_program_repr tprogram = 
  let result_repr (fdecl, c_opt) =
    match c_opt with
      | None -> "FAIL"
      | Some c -> "\n" ^ context_repr_fdecl_out fdecl c in
  map_repr
    FuncMap.is_empty FuncMap.choose FuncMap.remove FuncMap.fold
    "" func_repr result_repr "function %s: %s" "%s\n\n%s"
    tprogram.tfunc_tbl
    

(* for testing use: *)
let blame_ex = blame_repr (blame_event_conj (blame_one (LabelSite(Label(10)))) (event_disj
                                                                                  (event_internal_conj (AIE(Branch(5), false)) event_one)
                                                                                  (event_internal_conj (AIE(Branch(6), true)) event_one)))
    
