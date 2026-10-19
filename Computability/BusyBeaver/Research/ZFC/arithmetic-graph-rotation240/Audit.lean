import BusyBeaver.ZFC.ArithmeticMachineGraphRotation240

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open ArithmeticMachineGraphPerm252 ArithmeticMachineGraphRotation240

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineGraphRotation240.actionLookup_graph
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineGraphRotation240.literalRows_length
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineGraphRotation240.literalRows_positive_bounded
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineGraphRotation240.actionLookup_bound
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineGraphRotation240.literal_lookup_actual
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineGraphRotation240.actionLookup_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineGraphRotation240.halt_action_number
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineGraphRotation240.first_action_number

example {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] (out q bit : V) :
    ArithmeticMachineGraphRotation240.actionLookupDef.val.Evalb ![out, q, bit] ↔
      out = ArithmeticMachineGraphRotation240.actionLookup q bit :=
  ArithmeticMachineGraphRotation240.actionLookup_graph out q bit
example : ArithmeticMachineGraphRotation240.literalRows.length = 240 :=
  ArithmeticMachineGraphRotation240.literalRows_length
example : ∀ row ∈ ArithmeticMachineGraphRotation240.literalRows,
    0 < row.1 ∧ row.1 ≤ 1012 ∧ 0 < row.2 ∧ row.2 ≤ 1012 :=
  ArithmeticMachineGraphRotation240.literalRows_positive_bounded
example {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] (q bit : V) :
    ArithmeticMachineGraphRotation240.actionLookup q bit ≤ ORingStructure.numeral 1012 :=
  ArithmeticMachineGraphRotation240.actionLookup_bound q bit
example (q : Fin 240) (bit : Bool) :
    lookupNat ArithmeticMachineGraphRotation240.literalRows 0 (q.val + 1) bit.toNat =
      actionNumber (machineRotation240.transition q bit) :=
  ArithmeticMachineGraphRotation240.literal_lookup_actual q bit
example (q bit : Nat) : ArithmeticMachineGraphRotation240.actionLookup q bit =
    lookupNat ArithmeticMachineGraphRotation240.literalRows 0 q bit :=
  ArithmeticMachineGraphRotation240.actionLookup_nat q bit
example : actionNumber (machineRotation240.transition (oldStateRotation240 77) true) = 4 :=
  ArithmeticMachineGraphRotation240.halt_action_number
example : actionNumber (machineRotation240.transition (0 : Fin 240) false) = 392 :=
  ArithmeticMachineGraphRotation240.first_action_number
