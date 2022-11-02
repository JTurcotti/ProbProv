open Util

(* A computation layer can serve a request of type outputSet,
   responding with the same set's keys each mapped to floats *)
module type ComputationLayer =
sig
  type outputSet
  type 't outputMap
  val compute : outputSet -> float outputMap
end

(* a constant computation layer contains constant values
   for any output that could be requested - it responds to
   sets with a map whose domain matches the set and whose
   values are the ones stored internally *)
module type ConstantComputation =
sig
  type output
  val compute : output -> float
end

module ConstantComputationLayer
    (Output : T)
    (Action : ConstantComputation
     with type output = Output.t) :
  ComputationLayer 
  with type outputSet = Set(Output).t
  with type 't outputMap = 't Map(Output).t = 
struct
  module OutputSet = Set(Output)
  module OutputMap = Map(Output)
  
  type outputSet = OutputSet.t
  type 't outputMap = 't OutputMap.t
      
  let compute output_request =
    OutputSet.fold (fun output_point output_result ->
        OutputMap.add output_point (Action.compute output_point)
          output_result) output_request OutputMap.empty
end

module type DirectComputation =
sig
  type output
  type inputSet
  type 't inputMap
  val compute : output -> inputSet * (float inputMap -> float)
end

(* a direct computation layer takes input from another layer, and is able
   to directly compute its own output values from the output values of that
   layer

   It it parameterized by the predecessor layer, and by
   the direct computation function, which is expected to take
   an object of the type of the output of this layer
   and return a set of input points needed, as well as a "plan" for
   computing a float associated with that output point as a
   function of all the input points it requested
*)
module DirectComputationLayer
    (Input : T)
    (Output : T)
    (PredLayer : ComputationLayer 
     with type outputSet = Set(Input).t
     with type 't outputMap = 't Map(Input).t)
    (Action : DirectComputation
     with type output = Output.t
     with type inputSet = Set(Input).t
     with type 't inputMap = 't Map(Input).t) :
  ComputationLayer 
  with type outputSet = Set(Output).t
  with type 't outputMap = 't Map(Output).t = 
struct
  module OutputSet = Set(Output)
  module InputSet = Set(Input)
  module OutputMap = Map(Output)
  module InputMap = Map(Input)
      
  type outputSet = OutputSet.t
  type 't outputMap = 't OutputMap.t

  (*
     compute here calls Action.compute on each input point,
     accumulating the input requests as well as the plans for
     output results given response to the input requests.
     Once all input requests are accumulated they are passed
     to the pred layer and its responses are fed to the plans
     to obtain the final results.
     *)
  let compute (output_request : outputSet) =
    (* accumulate the needed inputs, and the desired outputs
       in terms of those inputs *)
    let input_request, output_plan =
      OutputSet.fold (fun output_point (input_request, output_plan) ->
          let req_inputs, plan = Action.compute output_point in
          (InputSet.union input_request req_inputs,
           OutputMap.add output_point plan output_plan))
        output_request (InputSet.empty, OutputMap.empty) in

    (* ask the pred layer to compute the needed inputs *)
    let input_result = PredLayer.compute input_request in

    (* compute the concrete values of the needed outputs
       now that the inputs have arrived *)
    OutputMap.map (fun plan -> plan input_result) output_plan
end


module type IndirectComputation =
sig
  type output
  type outputSet
  type outputEqn
                       
  type inputSet
  type 't inputMap
      
  val compute : output -> inputSet * outputSet *
                          (float inputMap -> outputEqn)
end

module IndirectComputationLayer
    (Input : T)
    (Output : T)
    (PredLayer : ComputationLayer 
     with type outputSet = Set(Input).t
     with type 't outputMap = 't Map(Input).t)
    (Action : IndirectComputation
     with type output = Output.t
     with type outputSet = Set(Output).t
     with type outputEqn = Equations.EqnSystem(Output).eqn
     with type inputSet = Set(Input).t
     with type 't inputMap = 't Map(Input).t) :
    ComputationLayer 
    with type outputSet = Set(Output).t
    with type 't outputMap = 't Map(Output).t =
struct
  module OutputSet = Set(Output)
  module InputSet = Set(Input)
  module OutputMap = Map(Output)
  module InputMap = Map(Input)
      
  type outputSet = OutputSet.t
  type inputSet = InputSet.t
  type 't inputMap = 't InputMap.t
  type 't outputMap = 't OutputMap.t

  module EqnSolver = Equations.EqnSystem(Output)
  type eqn = EqnSolver.eqn

  type deferred_eqn_list = (float inputMap -> eqn) list
  
  (* compute for an indirect computation is the most complex yet
     each output request generates a set of input requests, but also
     potentially more output requests.
     Also, even when all input requests have been filled by the pred layer,
     we are not able to compute output values, but just a system of equations
     for the output values. This system is then passed to an EqnSolver to
     compute the output values
  *)
  let compute (output_request : outputSet) : float outputMap =
    (* given that we have already determined the need for
       output points `prior_out_req`, input points `prior_in_req`, and
       equations `prior_eqns`, update those values to reflect the new
       output requests in `output_request`.
    *)
    let rec process_output_request
        output_request prior_out_req prior_in_req prior_eqns
      : (outputSet * inputSet * deferred_eqn_list) =
      if OutputSet.is_empty output_request then
        (prior_out_req, prior_in_req, prior_eqns)
      else
        let cum_out_reqs, cum_in_reqs, cum_eqns =
          OutputSet.fold (fun out_req (prior_out_req, prior_in_req, prior_eqns) ->
              let new_in_req, new_out_req, deferred_eqn = Action.compute out_req in
              (OutputSet.union new_out_req prior_out_req,
               InputSet.union new_in_req prior_in_req,
               deferred_eqn :: prior_eqns))
            output_request
            (prior_out_req, prior_in_req, prior_eqns) in
        process_output_request
          (OutputSet.diff cum_out_reqs prior_out_req) cum_out_reqs cum_in_reqs cum_eqns in
    let _, input_request, deferred_eqns =
      process_output_request output_request OutputSet.empty InputSet.empty [] in

    (* ask the pred layer for the needed inputs *)
    let input_result = PredLayer.compute input_request in
    let eqns = List.fold_right (fun deferred_eqn eqns ->
        EqnSolver.add (deferred_eqn input_result) eqns)
        deferred_eqns EqnSolver.empty in

    (* solve the system *)
    let eqn_solve_result = EqnSolver.solve eqns in

    (* return a mapping containing only the originally requested outputs *)
    OutputMap.filter (fun output_req _ ->
        OutputSet.mem output_req output_request) eqn_solve_result
end

let s = "a"
