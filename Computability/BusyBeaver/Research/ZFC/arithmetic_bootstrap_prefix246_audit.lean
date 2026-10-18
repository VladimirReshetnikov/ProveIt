import BusyBeaver.ZFC.ArithmeticBootstrapPrefix246
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open ArithmeticMachineRunPrefix246 ArithmeticBootstrapPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticBootstrapPrefix246.standard_boot
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticBootstrapPrefix246.run_cast
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticBootstrapPrefix246.internal_boot
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticBootstrapPrefix246.runEquationSentence_eval
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticBootstrapPrefix246.bootstrapSentence_true
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticBootstrapPrefix246.isigma1_proves_bootstrap
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticBootstrapPrefix246.peano_proves_bootstrap

example : run (410735 : Nat) = bootCode := standard_boot
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
private lemma audit_run_graph (out time : V) : runDef.val.Evalb ![out,time] ↔ out = run time := by
  simp
example (time : Nat) : run (time : V) = ((run time : Nat) : V) := run_cast time
example : run (410735 : V) = (bootCode : V) := internal_boot
example (out time : Nat) :
    (runEquationSentence out time).val.Evalb (M := V) ![] ↔
      (out : V) = run (time : V) := runEquationSentence_eval out time
example : bootstrapSentence.val.Evalb (M := V) ![] := bootstrapSentence_true
example : 𝗜𝚺₁ ⊢ bootstrapSentence.val := isigma1_proves_bootstrap
example : Peano ⊢ bootstrapSentence.val := peano_proves_bootstrap
example : runDef.val.Evalb (M := V) ![(bootCode : V),410735] :=
  (audit_run_graph _ _).mpr (internal_boot (V := V)).symm
example (out : V) : runDef.val.Evalb ![out,410735] ↔ out = (bootCode : V) := by
  rw [audit_run_graph, internal_boot]
