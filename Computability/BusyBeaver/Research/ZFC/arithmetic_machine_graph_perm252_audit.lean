import BusyBeaver.ZFC.ArithmeticMachineGraphPerm252
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open ArithmeticMachinePerm252 ArithmeticMachineGraphPerm252
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineGraphPerm252.lookup_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineGraphPerm252.lookup_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineGraphPerm252.numeral_mono
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineGraphPerm252.lookupValue_bound
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineGraphPerm252.actionLookup_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineGraphPerm252.literalRows_length
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineGraphPerm252.literalRows_positive_bounded
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineGraphPerm252.actionLookup_bound
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineGraphPerm252.literal_lookup_actual
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineGraphPerm252.actionLookup_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineGraphPerm252.halt_action_number
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineGraphPerm252.first_action_number
section Generic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
example (rows : List (Nat × Nat)) (start : Nat) (e : Fin 3 → V) :
    (lookupDef rows start).val.Evalb e ↔ e 0 = lookupValue rows start (e 1) (e 2) :=
  (lookup_defined rows start).df e
example (e : Fin 3 → V) : actionLookupDef.val.Evalb e ↔ e 0 = actionLookup (e 1) (e 2) :=
  actionLookup_defined.df e
example (rows : List (Nat × Nat)) (start : Nat) (q bit : V) (bound : Nat)
    (h : ∀ row ∈ rows, row.1 ≤ bound ∧ row.2 ≤ bound) :
    lookupValue rows start q bit ≤ ORingStructure.numeral bound := lookupValue_bound _ _ _ _ _ h
example (q bit : V) : actionLookup q bit ≤ ORingStructure.numeral 1012 := actionLookup_bound q bit
example : (ORingStructure.numeral 4 : V) ≤ ORingStructure.numeral 1012 := numeral_mono (by decide)
example (q bit : V) : ∃! r, actionLookupDef.val.Evalb ![r,q,bit] := by simp
end Generic
example (rows : List (Nat × Nat)) (start q bit : Nat) : lookupValue rows start q bit = lookupNat rows start q bit := lookup_nat _ _ _ _
example : literalRows.length = 252 := literalRows_length
example (row : Nat × Nat) (h : row ∈ literalRows) : 0 < row.1 ∧ row.1 ≤ 1012 ∧ 0 < row.2 ∧ row.2 ≤ 1012 := literalRows_positive_bounded row h
example (q : Fin 252) (bit : Bool) : lookupNat literalRows 0 (q.val+1) bit.toNat = actionNumber (machinePerm252.transition q bit) := literal_lookup_actual q bit
example (q bit : Nat) : actionLookup q bit = lookupNat literalRows 0 q bit := actionLookup_nat q bit
example : lookupNat literalRows 0 0 0 = 0 := by decide
example : lookupNat literalRows 0 253 1 = 0 := by decide
example : lookupNat literalRows 0 1 0 = 115 := by decide
example : lookupNat literalRows 0 76 1 = 4 := by decide
example : actionNumber (machinePerm252.transition (75 : Fin 252) true) = 4 := halt_action_number
example : actionNumber (machinePerm252.transition (0 : Fin 252) false) = 115 := first_action_number
