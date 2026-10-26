import DiophantineConsistency.ArithmeticMachineStep215
import DiophantineConsistency.ArithmeticMachineGraph215Checks

namespace DiophantineConsistency.ArithmeticMachineStep215Checks
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open ArithmeticMachinePerm252 ArithmeticMachineStep215
open ArithmeticMachineStepPerm252 (encodeConfig decode_encode)
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
set_option Elab.async false
set_option maxHeartbeats 4000000

example {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] (input : V) :
    ∃! out, stepDef.val.Evalb ![out,input] := step_total input
example (code : ℕ) : stepValue code = nativeStep code := stepValue_nat code

example (l r : ℕ) : nativeStep (encodeConfig ⟨0,l,r⟩) = encodeConfig ⟨0,l,r⟩ := by
  unfold nativeStep
  rw [decode_encode, numericStep_halted _ _ rfl]
example (l r : ℕ) : nativeStep (encodeConfig ⟨216,l,r⟩) = encodeConfig ⟨216,l,r⟩ := by
  unfold nativeStep
  rw [decode_encode, numericStep_invalid _ _ (by change 215 < 216; decide)]

/-- Actual decimal action125 enters halt with its final write and right move. -/
theorem halt_step (l r : ℕ) :
    numericStep DecimalMachine215.machine ⟨63,l,2*r+1⟩ = ⟨0,2*l+1,r⟩ := by
  have ht := ArithmeticMachineGraph215Checks.halt_action
  simp [numericStep, actionAt, ht, applyAction, stateCode]
  omega

/-- Separate left/erase control preserves the opposite tape update. -/
example (l r : ℕ) :
    applyAction ({ write := false, move := .left, next := none } : Action 215)
      ⟨63,l,2*r+1⟩ = ⟨0,l/2,l%2+4*r⟩ := by
  simp [applyAction, stateCode]
  omega

#print axioms step_defined
#print axioms step_total
#print axioms stepValue_nat_encoded
#print axioms stepValue_nat
#print axioms stepDef_nat
#print axioms halt_step
end DiophantineConsistency.ArithmeticMachineStep215Checks
