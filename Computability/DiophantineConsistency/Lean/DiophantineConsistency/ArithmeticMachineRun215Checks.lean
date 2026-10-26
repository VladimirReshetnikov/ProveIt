import DiophantineConsistency.ArithmeticMachineRun215

namespace DiophantineConsistency.ArithmeticMachineRun215Checks
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticMachineRun215
set_option Elab.async false
set_option maxHeartbeats 4000000

example {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (time : V) :
    ∃! out, runDef.val.Evalb ![out,time] := run_total time
example (time : ℕ) :
    ArithmeticCantor.first (run time) = 0 ↔
      (DecimalMachine215.machine.run time).state = none := run_halt_iff time
example : run (0 : ℕ) = 1 := run_zero
example : haltingSentence.val.Evalb (M := ℕ) ![] ↔
    ∃ time, (DecimalMachine215.machine.run time).state = none := haltingSentence_nat
example : 𝗜𝚺₁ ⊢ totalitySentence := isigma1_proves_totality
example : Peano ⊢ totalitySentence := peano_proves_totality

#print axioms run_defined
#print axioms run_defined_delta
#print axioms run_total
#print axioms run_nat
#print axioms run_represents
#print axioms run_halt_iff
#print axioms haltingSentence_nat
#print axioms totalitySentence_true
#print axioms isigma1_proves_totality
#print axioms peano_proves_totality
end DiophantineConsistency.ArithmeticMachineRun215Checks
