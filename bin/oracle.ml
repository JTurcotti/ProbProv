type 't deriv =
  | Primal of 't
  | Derivative of 't * int

let deriv_map f d =
  match d with
  | Primal t -> Primal (f t)
  | Derivative(t, d) -> Derivative(f t, d)

let deriv_strip d =
  match d with
  | Primal t -> t
  | Derivative(t, _) -> t

module type EventLike

module type MiniProbOracle =
sig
  type t
  type oraclet
    
  type dependence_hash

  (*
     returns a dependence_hash of t's guaranteed to be distinct between two
     t's only if the two are independent
     *)
  val query_dependence_hash : t -> dependence_hash
    
  (* returns the probability of a conjunction of t's occuring
   precondition: same dependence_hash for each *)
  val query_dependent_group : t list -> oraclet * float
end 

module type ProbOracle =
sig
  type t
    
  type oraclet

  val query : t deriv list -> oraclet * float
end

module BuildProbOracle 
    (Mini : MiniProbOracle) :
  (ProbOracle
   with type t = Mini.t
   with type oraclet = Mini.oraclet) =
struct
  type t = Mini.t
  type oraclet = Mini.oraclet
                   
  module DepHashMap = Map.Make(struct
      type t = Mini.dependence_hash deriv
      let compare = Stdlib.compare end)
      
  let query oraclet events =
    let hashed_events =
      List.fold_right (fun atomic_event hashed_events ->
          let hash = deriv_map Mini.query_dependence_hash atomic_event in
          let stripped = deriv_strip atomic_event in
          DepHashMap.update hash (function
              | None -> Some [stripped]
              | Some l -> Some (stripped :: l)) hashed_events) events DepHashMap.empty in
    DepHashMap.fold (fun _ events (oraclet, prob) ->
        let oraclet', events_prob = Mini.query_dependent_group oraclet events in
        (oraclet', prob *. events_prob)) hashed_events (oraclet, 1.0)
end

exception BadHashing

(* this ProbOracle for atomic internal events assumes
   each branch has an independent prob 1/2 of being taken*)
module AIEHalfOracle : ProbOracle with type t = Context.atomic_internal_event =
  BuildProbOracle (struct
    type t = Context.atomic_internal_event
    type oraclet = unit
    type dependence_hash = int
    let query_dependence_hash (Context.AIE (Branch i, _)) = i
    let query_dependent_group _ aies = (),
      match aies with
      | [_] -> 0.5
      (* only two events that could be here would be mutually exclusive
         so their conjunct prob is 0*)
      | [_; _] -> 0.
      | _ -> raise BadHashing
  end)




  
    
