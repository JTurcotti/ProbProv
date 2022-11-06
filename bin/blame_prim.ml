(**
   This module defines the primitive types for interprocedural program analysis
*)
open Expr
open Util

type call_event = {ce_func : func; ce_arg : arg; ce_ret : ret}

type blame_source =
  | BlameLabel of label
  | BlameCall of call * ret
  | BlameArg of func * arg

type blame_target = {bt_func: func; bt_ret: ret}

(* these are the sites the type system identifies -
   they include flows from a call to a return
   through the body of a function
   so the label, call, or arg of the source should be present in the
   function of the target*)
type blame_flow = {bf_src: blame_source; bf_tgt: blame_target}

(* these are the flows that we need to figure out using equation solving - the flow from the
   return of one function to the return of another via interprocedural calls *)
type blame_teleflow = {bt_src: blame_target; bt_tgt: blame_target}

type direct_blame_source =
  | DBlameLabel of label
  | DBlameArg of func * arg

(* these are a restricted version of the blame_flow type above - flows from calls to returns
   are not included because we used computation of the teleflows to eliminate them *)
type direct_blame_flow = {dbf_src: direct_blame_source; dbf_tgt: blame_target}


module DBSMap = Map(struct type t = direct_blame_source end)
