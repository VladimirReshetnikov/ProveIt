import BusyBeaver.ZFC.ArithmeticMachineStepRotation240
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open ArithmeticMachinePerm252
open ArithmeticMachineGraphPerm252 (lookupNat)
open ArithmeticMachineStepPerm252 (encodeConfig)
open ArithmeticMachineStepRotation240

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineStepRotation240.step_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineStepRotation240.step_total
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineStepRotation240.lookup_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineStepRotation240.lookup_invalid
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineStepRotation240.stepValue_nat_encoded
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineStepRotation240.stepValue_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineStepRotation240.stepDef_nat

section Internal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
example (e : Fin 2 → V) : stepDef.val.Evalb e ↔ e 0 = stepValue (e 1) :=
  step_defined.df e
example (input : V) : ∃! out, stepDef.val.Evalb ![out,input] := step_total input
end Internal

example (bit : Nat) : lookupNat ArithmeticMachineGraphRotation240.literalRows 0 0 bit = 0 :=
  lookup_zero bit
example (q bit : Nat) (hq : 240 < q) :
    lookupNat ArithmeticMachineGraphRotation240.literalRows 0 q bit = 0 := lookup_invalid q bit hq
example (u : NumericConfig) :
    stepValue (encodeConfig u) = encodeConfig (numericStep machineRotation240 u) :=
  stepValue_nat_encoded u
example (code : Nat) : stepValue code = nativeStep code := stepValue_nat code
example (out input : Nat) : stepDef.val.Evalb ![out,input] ↔ out = nativeStep input :=
  stepDef_nat out input

-- Inactive configurations preserve both tape halves, including invalid positive states.
example (l r : Nat) : stepValue (encodeConfig ⟨0,l,r⟩) = encodeConfig ⟨0,l,r⟩ := by
  rw [stepValue_nat_encoded, numericStep_halted machineRotation240 _ rfl]
example (q l r : Nat) (hq : 240 < q) :
    stepValue (encodeConfig ⟨q,l,r⟩) = encodeConfig ⟨q,l,r⟩ := by
  rw [stepValue_nat_encoded, numericStep_invalid machineRotation240 _ hq]

-- Canonical state68 is old77. Its terminal action writes one and moves right.
example (l r : Nat) :
    stepValue (encodeConfig ⟨69,l,2*r+1⟩) = encodeConfig ⟨0,2*l+1,r⟩ := by
  rw [stepValue_nat_encoded]
  have ht : machineRotation240.transition (68 : Fin 240) true = ⟨true, .right, none⟩ :=
    machineRotation240_halt_action
  have hr : (2*r+1)/2 = r := by omega
  simp [numericStep, actionAt, ht, applyAction, stateCode, hr]
