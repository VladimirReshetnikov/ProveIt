import BusyBeaver.ZFC.ArithmeticBootstrapRotation240
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open ArithmeticMachineRunRotation240 ArithmeticBootstrapRotation240

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticBootstrapRotation240.standard_boot
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticBootstrapRotation240.run_cast
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticBootstrapRotation240.internal_boot
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticBootstrapRotation240.runEquationSentence_eval
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticBootstrapRotation240.bootstrapSentence_true
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticBootstrapRotation240.isigma1_proves_bootstrap
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticBootstrapRotation240.peano_proves_bootstrap

example : run (409691 : Nat) = bootCode := standard_boot
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
private lemma audit_run_graph (out time : V) : runDef.val.Evalb ![out,time] ↔ out = run time := by
  simp
example (time : Nat) : run (time : V) = ((run time : Nat) : V) := run_cast time
example : run (409691 : V) = (bootCode : V) := internal_boot
example (out time : Nat) :
    (runEquationSentence out time).val.Evalb (M := V) ![] ↔
      (out : V) = run (time : V) := runEquationSentence_eval out time
example : bootstrapSentence.val.Evalb (M := V) ![] := bootstrapSentence_true
example : 𝗜𝚺₁ ⊢ bootstrapSentence.val := isigma1_proves_bootstrap
example : Peano ⊢ bootstrapSentence.val := peano_proves_bootstrap
example : runDef.val.Evalb (M := V) ![(bootCode : V),409691] :=
  (audit_run_graph _ _).mpr (internal_boot (V := V)).symm
example (out : V) : runDef.val.Evalb ![out,409691] ↔ out = (bootCode : V) := by
  rw [audit_run_graph, internal_boot]
