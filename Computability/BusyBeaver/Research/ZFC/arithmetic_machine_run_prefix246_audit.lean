import BusyBeaver.ZFC.ArithmeticMachineRunPrefix246
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open ArithmeticMachinePerm252
open ArithmeticMachineStepPerm252 (encodeConfig)
open ArithmeticMachineStepPrefix246 (stepValue)
open ArithmeticMachineRunPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunPrefix246.run_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunPrefix246.run_defined_delta
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunPrefix246.run_definable
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunPrefix246.run_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunPrefix246.run_succ
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunPrefix246.run_total
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunPrefix246.run_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunPrefix246.runDef_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunPrefix246.run_state_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunPrefix246.run_halt_iff
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunPrefix246.haltingSentence_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunPrefix246.totalitySentence_true
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunPrefix246.isigma1_proves_totality
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunPrefix246.peano_proves_totality

section Internal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (e : Fin 2 → V) : runDef.val.Evalb e ↔ e 0 = run (e 1) := run_defined.df e
example (e : Fin 2 → V) : runDeltaDef.val.Evalb e ↔ e 0 = run (e 1) := run_defined_delta.df e
example : 𝚺₁-Function₁[V] run := run_definable
example : run (0 : V) = 1 := run_zero
example (time : V) : run (time+1) = stepValue (run time) := run_succ time
example (time : V) : ∃! out, runDef.val.Evalb ![out,time] := run_total time
example : totalitySentence.Evalb (M := V) ![] := totalitySentence_true
example (e : Fin 1 → V) : zeroDef.val.Evalb e ↔ e 0 = 1 := by simp [zeroDef]
example (e : Fin 3 → V) : succDef.val.Evalb e ↔ e 0 = stepValue (e 1) := by simp [succDef]
end Internal

example (time : Nat) : run time = encodeConfig (numericRun machinePrefix246 time) := run_nat time
example (out time : Nat) :
    runDef.val.Evalb ![out,time] ↔ out = encodeConfig (numericRun machinePrefix246 time) :=
  runDef_nat out time
example (time : Nat) :
    ArithmeticCantor.first (run time) = (numericRun machinePrefix246 time).state :=
  run_state_nat time
example (time : Nat) :
    ArithmeticCantor.first (run time) = 0 ↔ (machinePrefix246.run time).state = none :=
  run_halt_iff time
example : haltingSentence.val.Evalb (M := Nat) ![] ↔
    ∃ time, (machinePrefix246.run time).state = none := haltingSentence_nat
example : 𝗜𝚺₁ ⊢ totalitySentence := isigma1_proves_totality
example : Peano ⊢ totalitySentence := peano_proves_totality
