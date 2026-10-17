import BusyBeaver.ZFC.ArithmeticBootstrapPerm252
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open FiniteZipper ArithmeticMachinePerm252 ArithmeticMachineStepPerm252
open ArithmeticMachineRunPerm252 ArithmeticBootstrapPerm252
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticBootstrapPerm252.bitsCode_zero_of_blank
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticBootstrapPerm252.bitsCode_ext
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticBootstrapPerm252.encodeZip_unique
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticBootstrapPerm252.numericRun_of_zipRep
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticBootstrapPerm252.standard_boot
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticBootstrapPerm252.run_cast
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticBootstrapPerm252.internal_boot
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticBootstrapPerm252.runEquationSentence_eval
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticBootstrapPerm252.bootstrapSentence_true
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticBootstrapPerm252.isigma1_proves_bootstrap
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticBootstrapPerm252.peano_proves_bootstrap
example (xs : List Bool) (h : ∀ i, xs.getD i false = false) : bitsCode xs = 0 := bitsCode_zero_of_blank xs h
example (xs ys : List Bool) (h : ∀ i, xs.getD i false = ys.getD i false) : bitsCode xs = bitsCode ys := bitsCode_ext xs ys h
example {n : Nat} {c : Config n} {z z' : ZipConfig n} (h : ZipRep c z) (h' : ZipRep c z') : encodeZip z = encodeZip z' := encodeZip_unique h h'
example {n : Nat} (M : Machine n) (t : Nat) (z : ZipConfig n) (h : ZipRep (M.run t) z) : numericRun M t = encodeZip z := numericRun_of_zipRep M t z h
example : run (82552 : Nat) = bootCode := standard_boot
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
private lemma audit_run_graph (out time : V) : runDef.val.Evalb ![out,time] ↔ out = run time := by simp
example (t : Nat) : run (t : V) = ((run t : Nat) : V) := run_cast t
example : run (82552 : V) = (bootCode : V) := internal_boot
example : bootstrapSentence.val.Evalb (M := V) ![] := bootstrapSentence_true
example : 𝗜𝚺₁ ⊢ bootstrapSentence.val := isigma1_proves_bootstrap
example : Peano ⊢ bootstrapSentence.val := peano_proves_bootstrap
example : runDef.val.Evalb (M := V) ![(bootCode : V),82552] := (audit_run_graph _ _).mpr (internal_boot (V := V)).symm
example (out : V) : runDef.val.Evalb ![out,82552] ↔ out = (bootCode : V) := by rw [audit_run_graph, internal_boot]

example (out time : Nat) : (runEquationSentence out time).val.Evalb (M := V) ![] ↔ (out : V) = run (time : V) := runEquationSentence_eval out time
