import BusyBeaver.ZFC.ArithmeticMachineGraphPrefix246

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open ArithmeticMachineGraphPerm252 ArithmeticMachineGraphPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineGraphPrefix246.actionLookup_graph
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineGraphPrefix246.literalRows_length
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineGraphPrefix246.literalRows_positive_bounded
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineGraphPrefix246.actionLookup_bound
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineGraphPrefix246.literal_lookup_actual
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineGraphPrefix246.actionLookup_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineGraphPrefix246.halt_action_number
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineGraphPrefix246.first_action_number

example {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] (out q bit : V) :
    ArithmeticMachineGraphPrefix246.actionLookupDef.val.Evalb ![out, q, bit] ↔
      out = ArithmeticMachineGraphPrefix246.actionLookup q bit :=
  ArithmeticMachineGraphPrefix246.actionLookup_graph out q bit
example : ArithmeticMachineGraphPrefix246.literalRows.length = 246 :=
  ArithmeticMachineGraphPrefix246.literalRows_length
example : ∀ row ∈ ArithmeticMachineGraphPrefix246.literalRows,
    0 < row.1 ∧ row.1 ≤ 1012 ∧ 0 < row.2 ∧ row.2 ≤ 1012 :=
  ArithmeticMachineGraphPrefix246.literalRows_positive_bounded
example {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] (q bit : V) :
    ArithmeticMachineGraphPrefix246.actionLookup q bit ≤ ORingStructure.numeral 1012 :=
  ArithmeticMachineGraphPrefix246.actionLookup_bound q bit
example (q : Fin 246) (bit : Bool) :
    lookupNat ArithmeticMachineGraphPrefix246.literalRows 0 (q.val + 1) bit.toNat =
      actionNumber (machinePrefix246.transition q bit) :=
  ArithmeticMachineGraphPrefix246.literal_lookup_actual q bit
example (q bit : Nat) : ArithmeticMachineGraphPrefix246.actionLookup q bit =
    lookupNat ArithmeticMachineGraphPrefix246.literalRows 0 q bit :=
  ArithmeticMachineGraphPrefix246.actionLookup_nat q bit
example : actionNumber (machinePrefix246.transition (oldStatePrefix246 77) true) = 4 :=
  ArithmeticMachineGraphPrefix246.halt_action_number
example : actionNumber (machinePrefix246.transition (0 : Fin 246) false) = 408 :=
  ArithmeticMachineGraphPrefix246.first_action_number
