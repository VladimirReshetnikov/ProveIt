import BusyBeaver.ZFC.ArithmeticMachineStepPerm252
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open ArithmeticMachinePerm252 ArithmeticMachineGraphPerm252 ArithmeticMachineStepPerm252
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineStepPerm252.bounded_output_pair
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineStepPerm252.apply_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineStepPerm252.generic_step_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineStepPerm252.step_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineStepPerm252.step_total
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineStepPerm252.decode_encode
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineStepPerm252.encode_decode
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineStepPerm252.lookupNat_absent
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineStepPerm252.lookupNat_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineStepPerm252.lookupNat_invalid
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineStepPerm252.actionNumber_decode
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineStepPerm252.actionNumber_positive
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineStepPerm252.foundation_sub_projection_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineStepPerm252.applyValue_nat_formula
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineStepPerm252.applyValue_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineStepPerm252.native_read_bit
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineStepPerm252.stepValue_nat_encoded
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineStepPerm252.stepValue_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineStepPerm252.stepDef_nat
section Generic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
example (e : Fin 4 → V) : applyDef.val.Evalb e ↔ e 0 = applyValue (e 1) (e 2) (e 3) := apply_defined.df e
example (e : Fin 2 → V) : stepDef.val.Evalb e ↔ e 0 = stepValue (e 1) := step_defined.df e
example (input : V) : ∃! out, stepDef.val.Evalb ![out,input] := step_total input
example (lookup : V → V → V) (graph : 𝚺₀.Semisentence 3)
    (hgraph : 𝚺₀-Function₂[V] lookup via graph)
    (hbound : ∀ q bit, lookup q bit ≤ ORingStructure.numeral 1012) (e : Fin 2 → V) :
    (genericStepDef graph).val.Evalb e ↔ e 0 = genericStepValue lookup (e 1) :=
  (generic_step_defined lookup graph hgraph hbound).df e
example (out q l r : V) :
    (ArithmeticCantor.cantor l r ≤ out ∧ out = ArithmeticCantor.cantor q (ArithmeticCantor.cantor l r)) ↔
    out = ArithmeticCantor.cantor q (ArithmeticCantor.cantor l r) := bounded_output_pair _ _ _ _
end Generic
example (u : NumericConfig) : decodeConfig (encodeConfig u) = u := decode_encode u
example (c : Nat) : encodeConfig (decodeConfig c) = c := encode_decode c
example (rows : List (Nat × Nat)) (start q bit : Nat) (h : q ≤ start ∨ start + rows.length < q) : lookupNat rows start q bit = 0 := lookupNat_absent _ _ _ _ h
example (bit : Nat) : lookupNat literalRows 0 0 bit = 0 := lookupNat_zero bit
example (q bit : Nat) (hq : 252 < q) : lookupNat literalRows 0 q bit = 0 := lookupNat_invalid q bit hq
example {n : Nat} (a : Action n) : Nat.div (actionNumber a - 1) 4 = stateCode a.next := (actionNumber_decode a).1
example {n : Nat} (a : Action n) : Nat.mod (Nat.div (actionNumber a - 1) 2) 2 = (if a.move = .right then 1 else 0) := (actionNumber_decode a).2.1
example {n : Nat} (a : Action n) : Nat.mod (actionNumber a - 1) 2 = a.write.toNat := (actionNumber_decode a).2.2
example {n : Nat} (a : Action n) : 0 < actionNumber a := actionNumber_positive a
example (a b : Nat) : @Sub.sub Nat Arithmetic.instSub_foundation a b = a-b := foundation_sub_projection_nat a b
example {n : Nat} (a : Action n) (u : NumericConfig) : applyValue (actionNumber a) u.left u.right = encodeConfig (applyAction a u) := applyValue_nat a u
example (r : Nat) : (decide (r % 2 = 1)).toNat = r % 2 := native_read_bit r
example (u : NumericConfig) : stepValue (encodeConfig u) = encodeConfig (numericStep machinePerm252 u) := stepValue_nat_encoded u
example (c : Nat) : stepValue c = nativeStep c := stepValue_nat c
example (out input : Nat) : stepDef.val.Evalb ![out,input] ↔ out = nativeStep input := stepDef_nat out input
-- Halted and invalid states keep their WHOLE coded tape.
example (l r : Nat) : stepValue (encodeConfig ⟨0,l,r⟩) = encodeConfig ⟨0,l,r⟩ := by
  rw [stepValue_nat_encoded, numericStep_halted machinePerm252 _ rfl]
example (q l r : Nat) (hq : 252 < q) : stepValue (encodeConfig ⟨q,l,r⟩) = encodeConfig ⟨q,l,r⟩ := by
  rw [stepValue_nat_encoded, numericStep_invalid machinePerm252 _ hq]
-- The actual final write and right shift survive configuration coding.
example (l r : Nat) : stepValue (encodeConfig ⟨76,l,2*r+1⟩) = encodeConfig ⟨0,2*l+1,r⟩ := by
  rw [stepValue_nat_encoded, perm252_halt_edge]
example (l r : Nat) : stepDef.val.Evalb ![encodeConfig ⟨0,2*l+1,r⟩,encodeConfig ⟨76,l,2*r+1⟩] := by
  simp only [step_defined.iff]
  change encodeConfig ⟨0,2*l+1,r⟩ = stepValue (encodeConfig ⟨76,l,2*r+1⟩)
  rw [stepValue_nat_encoded, perm252_halt_edge]
example : encodeConfig ⟨1,0,0⟩ = 1 := by decide
example : nativeStep 1 = 406 := by decide
example : stepValue (1 : Nat) = 406 := by rw [stepValue_nat]; decide
example : stepValue (0 : Nat) = 0 := by rw [stepValue_nat]; decide
example : decodeConfig 0 = ⟨0,0,0⟩ := by decide
example : stepDef.val.Evalb ![406,1] := by rw [stepDef_nat]; decide
example : ¬ stepDef.val.Evalb ![0,1] := by rw [stepDef_nat]; decide
