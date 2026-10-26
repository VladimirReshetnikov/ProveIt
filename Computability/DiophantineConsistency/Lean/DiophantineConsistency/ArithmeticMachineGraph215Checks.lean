import DiophantineConsistency.ArithmeticMachineGraph215

namespace DiophantineConsistency.ArithmeticMachineGraph215Checks
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open ArithmeticMachinePerm252 ArithmeticMachineGraph215
open ArithmeticMachineGraphPerm252 (lookupNat actionNumber)
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1024

example : literalRows.length = 215 := literalRows_length
example (q : Fin 215) (b : Bool) :
    lookupNat literalRows 0 (q.val + 1) b.toNat =
      actionNumber (DecimalMachine215.machine.transition q b) := literal_lookup_actual q b

/-- The actual halt edge is a positive action: it still writes and moves. -/
theorem halt_action : DecimalMachine215.machine.transition (62 : Fin 215) true =
    { write := true, move := .right, next := none } := by decide +kernel

example : actionNumber (DecimalMachine215.machine.transition (62 : Fin 215) true) = 4 := by
  rw [halt_action]; rfl
example : actionNumber ({ write := false, move := .left, next := none } : Action 215) = 1 := rfl
example : actionNumber ({ write := true, move := .right, next := some 214 } : Action 215) = 864 := rfl

example {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] (q b : V) :
    ∃! out, actionLookupDef.val.Evalb ![out,q,b] := by simp

#print axioms lookup_ofFn
#print axioms literal_lookup_actual
#print axioms literalRows_positive_bounded
#print axioms actionLookup_defined
#print axioms actionLookup_bound
#print axioms halt_action
end DiophantineConsistency.ArithmeticMachineGraph215Checks
