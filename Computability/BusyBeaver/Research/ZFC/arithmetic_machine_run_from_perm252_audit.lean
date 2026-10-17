import BusyBeaver.ZFC.ArithmeticMachineRunFromPerm252
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticMachineGraphPerm252 ArithmeticMachineStepPerm252
open ArithmeticMachineRunFromPerm252
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunFromPerm252.lookupValue_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunFromPerm252.lookupValue_numeral
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunFromPerm252.actionLookup_numeral
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunFromPerm252.actionLookup_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunFromPerm252.step_halted
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunFromPerm252.runFrom_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunFromPerm252.runFrom_defined_delta
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunFromPerm252.runFrom_definable
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunFromPerm252.runFrom_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunFromPerm252.runFrom_succ
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunFromPerm252.runFrom_one
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunFromPerm252.runFrom_add
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunFromPerm252.runFrom_first
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunFromPerm252.runFrom_halted
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunFromPerm252.runFrom_halt_state
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunFromPerm252.runFrom_blank
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunFromPerm252.runFrom_total
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunFromPerm252.runFrom_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunFromPerm252.runFromDef_nat

example (rows : List (Nat × Nat)) (start : Nat) (bit : V) : lookupValue rows start 0 bit = 0 := lookupValue_zero rows start bit
example (bit : V) : actionLookup 0 bit = 0 := actionLookup_zero bit
example (config : V) (hh : first config = 0) : stepValue config = config := step_halted config hh
example (initial : V) : runFrom 0 initial = initial := runFrom_zero initial
example (time initial : V) : runFrom (time+1) initial = stepValue (runFrom time initial) := runFrom_succ time initial
example (initial : V) : runFrom 1 initial = stepValue initial := runFrom_one initial
example (t u initial : V) : runFrom (t+u) initial = runFrom u (runFrom t initial) := runFrom_add t u initial
example (time initial : V) : runFrom (time+1) initial = runFrom time (stepValue initial) := runFrom_first time initial
example (time config : V) (hh : first config = 0) : runFrom time config = config := runFrom_halted time config hh
example (time config : V) (hh : first config = 0) : first (runFrom time config) = 0 := runFrom_halt_state time config hh
example (time : V) : runFrom time 1 = ArithmeticMachineRunPerm252.run time := runFrom_blank time
example (time initial : V) : ∃! out, runFromDef.val.Evalb ![out,time,initial] := runFrom_total time initial
example (time initial : Nat) : runFrom time initial = nativeRunFrom time initial := runFrom_nat time initial
example (out time initial : Nat) : runFromDef.val.Evalb ![out,time,initial] ↔ out = nativeRunFrom time initial := runFromDef_nat out time initial
example (time left right : V) : runFrom time (cantor 0 (cantor left right)) = cantor 0 (cantor left right) := runFrom_halted time _ (by simp)
example (time : V) : runFrom time 0 = 0 := runFrom_halted time 0 (by
  simpa [cantor, triangle] using first_cantor (0 : V) 0)
example (time : V) : first (runFrom time 1) = first (ArithmeticMachineRunPerm252.run time) := congrArg first (runFrom_blank time)
example (t u left right : V) : runFrom (t+u) (cantor 0 (cantor left right)) = cantor 0 (cantor left right) := runFrom_halted (t+u) _ (by simp)
example (rows : List (Nat × Nat)) (start q bit : Nat) : lookupValue rows start (ORingStructure.numeral q : V) (ORingStructure.numeral bit) = ORingStructure.numeral (lookupNat rows start q bit) := lookupValue_numeral rows start q bit
example (q bit : Nat) : actionLookup (ORingStructure.numeral q : V) (ORingStructure.numeral bit) = ORingStructure.numeral (lookupNat literalRows 0 q bit) := actionLookup_numeral q bit
