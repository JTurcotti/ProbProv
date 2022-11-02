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
    let input_request, output_plan =
      OutputSet.fold (fun output_point (input_request, output_plan) ->
          let req_inputs, plan = Action.compute output_point in
          (InputSet.union input_request req_inputs,
           OutputMap.add output_point plan output_plan))
        output_request (InputSet.empty, OutputMap.empty) in
    let input_result = PredLayer.compute input_request in
    OutputMap.map (fun plan -> plan input_result) output_plan
end


module type IndirectComputationLayer =
sig
  type output
  type inputSet
  type outputSet
  type outputEqn
    
  val compute : output -> inputSet * outputSet *
                          ((inputSet -> float) -> outputEqn)
end
