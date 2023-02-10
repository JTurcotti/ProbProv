open Util

let program = Io.program

let () = print_endline (Expr_repr.program_string program)
let typechecked_prog = (Typecheck.typecheck_program program)
let () = print_endline (Context_repr.typechecked_program_repr
                          typechecked_prog.tfunc_tbl)

include Analyze.ProgramAnalyzer (struct
    type t = Typecheck.typechecked_program
    let get _ = typechecked_prog
  end)

open Blame_prim

(* choose which omega to output *)
let filter {dbf_src=_; dbf_tgt={bt_func=Func(f_s); bt_ret=_}} =
  match (!Io.IO.target_assertions, !Io.IO.restrict_to_func) with
  | (_, "") -> true
  | (_, s) -> f_s = s


let analyze_and_output _ = 
  (* compute the omegas *)
  let start_t = Unix.gettimeofday () in
  let computed_omegas = Output.get_program_blame filter in
  let elapsed_t = Unix.gettimeofday () -. start_t in

  (* pretty print the functions with blames *)
  let () = Output.VeryPrettyPrint.format_program Format.std_formatter
      !Io.IO.input_file typechecked_prog computed_omegas in

  (* pretty print the raw omegas *)
  let () = Format.fprintf Format.std_formatter
      "%a" Output.format_program_blame computed_omegas in
  computed_omegas, elapsed_t

exception Unexpected of string

  
let () = if !Io.IO.compare_mode then
    let () = Refactor.independent_mode := true in
    let POmegas indep_omegas, indep_t = analyze_and_output () in
    let () = Refactor.independent_mode := false in
    let POmegas dep_omegas, dep_t = analyze_and_output () in
    let merged_omegas = OmegaMap.merge
        (fun _ o1 o2 -> match o1, o2 with
           | Some f1, Some f2 ->
             Some (Float.abs (f1 -. f2))
           | _ -> raise (Unexpected "Returned omega maps differed in domain"))
        indep_omegas dep_omegas in
    let geo_merged_omegas = OmegaMap.merge
        (fun _ o1 o2 -> match o1, o2 with
           | Some f1, Some f2 ->
             if f1 +. f2 < 0.0001 then Some 0.0 else
               Some ((Float.abs (f1 -. f2)) /. f2)
           | _ -> raise (Unexpected "Returned omega maps differed in domain"))
        indep_omegas dep_omegas in
    let nonzero = OmegaMap.merge
        (fun _ o1 o2 -> match o1, o2 with
           | Some f1, Some f2 ->
             if f1 +. f2 < 0.00001 then None else
               Some (Float.abs (f1 -. f2))
           | _ -> raise (Unexpected "Returned omega maps differed in domain"))
        indep_omegas dep_omegas in
    let geo_nonzero = OmegaMap.merge
        (fun _ o1 o2 -> match o1, o2 with
           | Some f1, Some f2 ->
             if f1 +. f2 < 0.00001 then None else
               Some ((Float.abs (f1 -. f2)) /. f2)
           | _ -> raise (Unexpected "Returned omega maps differed in domain"))
        indep_omegas dep_omegas in
    let n = Float.of_int (OmegaMap.cardinal merged_omegas) in
    let max_err = OmegaMap.fold
        (fun _ f1 f2 -> if f1 > f2 then f1 else f2)
        merged_omegas Float.neg_infinity in
    let max_geo_err = OmegaMap.fold
        (fun _ f1 f2 -> if f1 > f2 then f1 else f2)
        geo_merged_omegas Float.neg_infinity in
    let mean_err = (OmegaMap.fold
                      (fun _ -> Float.add)
                      merged_omegas 0.0) /. n in
    let mean_geo_err = (OmegaMap.fold
                      (fun _ -> Float.add)
                      geo_merged_omegas 0.0) /. n in
    let rms_err = Float.sqrt ((OmegaMap.fold
                                 (fun _ f -> Float.add (f *. f))
                                 merged_omegas 0.0) /. n) in
    let n_nz = Float.of_int (OmegaMap.cardinal nonzero) in
    let mean_err_nz = (OmegaMap.fold
                      (fun _ -> Float.add)
                      nonzero 0.0) /. n_nz in
    let mean_geo_err_nz = (OmegaMap.fold
                      (fun _ -> Float.add)
                      geo_nonzero 0.0) /. n_nz in
    let rms_err_nz = Float.sqrt ((OmegaMap.fold
                                 (fun _ f -> Float.add (f *. f))
                                 nonzero 0.0) /. n_nz) in

    Format.printf "\n\nComparison results over %d omegas (%d nonzero):\nIndependent Events time: %f secs\nDependent Events time: %f secs\nMax Error: %f\nMax Relative Error: %f\nMean Error: %f\nMean Relative Error: %f\nRoot Mean Squared Error: %f\nMean Error (nonzero values): %f\nMean Relative Error (nonzero values): %f\nRoot Mean Squared Error (nonzero values): %f\n"
      (int_of_float n)(int_of_float n_nz)
      indep_t dep_t
      max_err max_geo_err mean_err mean_geo_err rms_err
      mean_err_nz mean_geo_err_nz rms_err_nz
  else
    let () = Refactor.independent_mode := !Io.IO.independent_mode in
    let _ = analyze_and_output () in ()
          


(*
let bld = Context.Refactor.EERefactorizer.build
let slc_repr x =
  match Context.Refactor.EERefactorizer.slice x with
  | Some (a, b, c) -> Context_repr.(
      Printf.sprintf "(%s, %s, %s)"
        (aee_repr a)
        (external_event_repr b)
        (external_event_repr c)
    )
  | None -> "None"

let _ = Context.(
    let a = external_event_conj
        (CallEvent(Call(Func("a"), 0), Arg(0, "x"), Ret(0, "x"), true))
        external_event_one in
    let b = external_event_conj
        (CallEvent(Call(Func("b"), 0), Arg(0, "x"), Ret(0, "x"), true))
        external_event_one in
    let ab = external_event_disj a b in
    let _ = print_endline "\n\n\n" in
    let _ = print_endline (slc_repr ab) in
    let out = bld ab in
    print_endline (Context_repr.external_event_repr out)
  )*)

(* DEBUGGING
   module StrSystem = Equations.EqnSystem(struct type t = string end)

   let str_map_repr s = StrSystem.VarMap.fold (fun s d r ->
    Printf.sprintf "%s:%f, %s" s d r) s ""

   let _ = print_endline (str_map_repr (StrSystem.(solve (
    add (Eqn ("x", (Mult (Var "y" , Var "y"))))
      (add (Eqn ("y", (Add (Var "x" , Const 0.25))))
         empty)
   ))))
*)

module TestDoubleSet =
struct
  let run_tests = false

  type neg_char = char * bool
  let nc_neg (c, b) = (c, not b)
  let nc_repr (c, b) = Printf.sprintf "%c%s" c (unicode_bar_cond b)
  module NC = struct type t = neg_char end
  module NCDS = Refactor.DoubleSet (Set(NC)) (Set(Set(NC)))
      (struct type t = neg_char let neg = nc_neg end)

  let repr = NCDS.repr nc_repr "%s%s" "%s + %s"

  let single c = NCDS.singleton (c, true)
  let disj = NCDS.disj
  let conj = NCDS.conj
  let neg = NCDS.neg

  let () =
    if not run_tests then () else (
      let a, b, c, d, e, f, g, h =
        single 'a', single 'b', single 'c', single 'd', single 'e', single 'f',
        single 'g', single 'h' in
      let print x = print_endline (repr x) in
      let _ = print (disj a b) in
      let test_ex =
        (disj
           (conj (conj (conj a b) c) d)
           (conj (conj (conj e f) g) h)
        ) in
      let _ = print test_ex in
      let _ = print (neg test_ex) in
      ()
    )
end

module TestPIE =
struct
  (* TODO: Test PIE more *)
  let run_tests = false
  
  module String = 
  struct
    type t = string
    type hash_t = unit
    let hash _ = ()
  end

  module StrDDS = Refactor.DerivedDoubleSet(String)
  let fmt = Format.asprintf "{%a}" (StrDDS.DepEv.Set.lift_format
                                   (fun ff -> Format.fprintf ff "%s") ", " "0")
  module DNF = StrDDS.DNF

  let of_str s = DNF.singleton {el=s; ind=0; sgn=true}
  let of_str_neg s = DNF.singleton {el=s; ind=0; sgn=false}

  module StrArith = 
  struct
    type t = string
    let mult = Format.sprintf "(%s * %s)"
    let add = Format.sprintf "(%s + %s)"
    let sub = Format.sprintf "(%s - %s)"
    let one = "1"
    let zero = "0"
  end

  module StrArithSynth = StrDDS.ArithSynth(StrArith)

  let print_compute_ex ex = 
    let req, synth = StrArithSynth.dnf_to_req_synth ex in
    let req_repr : string =
      Format.asprintf "{%a}"
        (StrArithSynth.DepEvSet.lift_format
           (fun ff e -> Format.fprintf ff "%s" (fmt e)) ", " "0") req in 
    let synth_repr : string = synth fmt in
    Format.printf "\n%s -> [%s]\n" req_repr synth_repr

  let () = if not run_tests then () else 
      let () = print_compute_ex (DNF.disj
                                   (DNF.conj (of_str "a") (of_str "b"))
                                   (DNF.conj (of_str_neg "a") (of_str "b"))) in
      let () = print_compute_ex (DNF.disj
                                   (DNF.conj (of_str "a") (of_str "b"))
                                   (of_str_neg "a")) in
      let () = print_compute_ex (DNF.disj
                                   (DNF.conj (of_str "a") (of_str "b"))
                                   (of_str "a")) in
      let () = print_compute_ex (DNF.conj (of_str "a") (of_str_neg "b")) in
      let () = print_compute_ex (DNF.conj (of_str "a") (of_str "b")) in
      ()
end
