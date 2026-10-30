import DiophantineConsistency.ArithmeticEnumSoundnessPerm222
import DiophantineConsistency.ArithmeticRuntime215

/-! Closed arithmetic proofs for the actual C222 checker and literal decimal215
blank machine. Type0 retains the accepted forward compiler's universe scope.
Source-ZFC, polynomial witness equivalence and HA transfer are separate. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticCheckerMachine215
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC ArithmeticCantor

/-- The existing fixed halting graph, interpreted at arbitrary internal times. -/
theorem haltingSentence_iff {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    ArithmeticMachineRun215.haltingSentence.val.Evalb (M:=V) ![] ↔
      ∃ time : V, first (ArithmeticMachineRun215.run time)=0 := by
  simp [ArithmeticMachineRun215.haltingSentence,eq_comm]

section Models
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Both witnesses range over this same arithmetic model, with no calibration premise. -/
theorem refutation_iff_blank_halts :
    (∃ proof : V, ArithmeticHistory222.checkDef.val.Evalb ![proof,1]) ↔
      ∃ time : V, first (ArithmeticMachineRun215.run time)=0 :=
  ArithmeticEnumSoundnessPerm222.refutation_iff_zero_work_halts.trans
    ArithmeticRuntime215.enum_blank_halts_iff

theorem refutation_iff_haltingSentence :
    (∃ proof : V, ArithmeticHistory222.checkDef.val.Evalb ![proof,1]) ↔
      ArithmeticMachineRun215.haltingSentence.val.Evalb (M:=V) ![] :=
  refutation_iff_blank_halts.trans haltingSentence_iff.symm
end Models

/-- An arithmetic sentence, not a Sigma1 classification of the whole equivalence. -/
def checkerMachineSentence : ArithmeticSentence :=
  “(∃ code, !ArithmeticHistory222.checkDef code 1) ↔
    !ArithmeticMachineRun215.haltingSentence”

theorem checkerMachineSentence_true {V : Type} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] : checkerMachineSentence.Evalb (M:=V) ![] := by
  simpa [checkerMachineSentence] using (refutation_iff_haltingSentence (V:=V))

/-- Completeness uses every Type0 IΣ1 model, not truth only in Nat. -/
theorem isigma1_proves_checker_machine : 𝗜𝚺₁ ⊢ checkerMachineSentence := by
  apply LO.FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  simpa [models_iff] using (checkerMachineSentence_true (V:=M))

theorem peano_proves_checker_machine : Peano ⊢ checkerMachineSentence :=
  Entailment.weakening (inferInstance : 𝗜𝚺₁ ⪯ Peano) isigma1_proves_checker_machine

end DiophantineConsistency.ArithmeticCheckerMachine215
