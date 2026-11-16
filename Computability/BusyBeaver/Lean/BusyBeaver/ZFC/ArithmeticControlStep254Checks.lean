import BusyBeaver.ZFC.ArithmeticControlStep254
import Lean.Util.FoldConsts

set_option autoImplicit false

namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlStep254Checks

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticControlStep254

section Model

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

example (state : V) (hs : state ≠ 0) :
    liveValue (controlValue state) (fileCodeValue state) = state :=
  live_decode state hs

example : 𝚺₁-Function₁[V] stepValue via stepDef := step_defined
example : 𝚫₁-Function₁[V] stepValue via stepDef.graphDelta := step_defined_delta
example (state : V) : ∃! out : V, stepDef.val.Evalb ![out, state] := step_total state

end Model

#print axioms live_decode
#print axioms step_defined_delta
#print axioms step_total
#print axioms ArithmeticPredecessorWitness.pred_add_one

open Lean Elab Command in
run_cmd
  let env ← getEnv
  let decode := `SetTheory.BusyBeaver.ZFC.ArithmeticControlStep254.live_decode
  let row := `SetTheory.BusyBeaver.ZFC.ArithmeticRow254.pred_add_one
  let shared := `SetTheory.BusyBeaver.ZFC.ArithmeticPredecessorWitness.pred_add_one
  for (caller, callee) in [(decode, row), (row, shared)] do
    let some value := (env.find? caller).bind (·.value? (allowOpaque := true)) |
      throwError "Missing proof {caller}"
    unless value.getUsedConstants.contains callee do
      throwError "Expected {caller} to use {callee}"

end SetTheory.BusyBeaver.ZFC.ArithmeticControlStep254Checks
