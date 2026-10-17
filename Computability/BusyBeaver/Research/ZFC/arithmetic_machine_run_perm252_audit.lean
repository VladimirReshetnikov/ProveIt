import BusyBeaver.ZFC.ArithmeticMachineRunPerm252
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open ArithmeticMachinePerm252 ArithmeticMachineStepPerm252 ArithmeticMachineRunPerm252
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunPerm252.run_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunPerm252.run_defined_delta
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunPerm252.run_definable
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunPerm252.run_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunPerm252.run_succ
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunPerm252.run_total
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunPerm252.run_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunPerm252.runDef_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunPerm252.run_state_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunPerm252.run_halt_iff
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunPerm252.haltingSentence_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunPerm252.totalitySentence_true
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunPerm252.isigma1_proves_totality
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunPerm252.peano_proves_totality
section Generic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (e : Fin 2 → V) : runDef.val.Evalb e ↔ e 0 = run (e 1) := run_defined.df e
example (e : Fin 2 → V) : runDeltaDef.val.Evalb e ↔ e 0 = run (e 1) := run_defined_delta.df e
example : run (0 : V) = 1 := run_zero
example (time : V) : run (time+1) = stepValue (run time) := run_succ time
example (time : V) : ∃! out, runDef.val.Evalb ![out,time] := run_total time
example : totalitySentence.Evalb (M := V) ![] := totalitySentence_true
example (e : Fin 1 → V) : zeroDef.val.Evalb e ↔ e 0 = 1 := by simp [zeroDef]
example (e : Fin 3 → V) : succDef.val.Evalb e ↔ e 0 = stepValue (e 1) := by simp [succDef]
end Generic
example (time : Nat) : run time = encodeConfig (numericRun machinePerm252 time) := run_nat time
example (out time : Nat) : runDef.val.Evalb ![out,time] ↔ out = encodeConfig (numericRun machinePerm252 time) := runDef_nat out time
example (time : Nat) : ArithmeticCantor.first (run time) = (numericRun machinePerm252 time).state := run_state_nat time
example (time : Nat) : ArithmeticCantor.first (run time) = 0 ↔ (machinePerm252.run time).state = none := run_halt_iff time
example : haltingSentence.val.Evalb (M := Nat) ![] ↔ ∃t,(machinePerm252.run t).state = none := haltingSentence_nat
example : 𝗜𝚺₁ ⊢ totalitySentence := isigma1_proves_totality
example : Peano ⊢ totalitySentence := peano_proves_totality
example : run (0 : Nat) = 1 := run_zero
example : run (1 : Nat) = 406 := by rw [run_nat]; rfl
example : run (2 : Nat) = 820 := by rw [run_nat]; rfl
example : ArithmeticCantor.first (run (0 : Nat)) = 1 := by rw [run_state_nat]; rfl
example : ArithmeticCantor.first (run (1 : Nat)) = 28 := by rw [run_state_nat]; rfl
example : runDef.val.Evalb (M := Nat) ![406,1] := by rw [runDef_nat]; rfl
example : ¬ runDef.val.Evalb (M := Nat) ![0,1] := by rw [runDef_nat]; decide
example : ¬ ArithmeticCantor.first (run (0 : Nat)) = 0 := by rw [run_halt_iff]; decide
example : ¬ ArithmeticCantor.first (run (1 : Nat)) = 0 := by rw [run_halt_iff]; decide
example (t : Nat) : ArithmeticCantor.first (run t) = 0 → ∃ k,(machinePerm252.run k).state = none := fun h => ⟨t,(run_halt_iff t).mp h⟩
