module
public import M6PA.Endpoint
public import M6PA.RefutationHalting
public import M6PA.Calibration.InternalActualRefutationConsistency
public import M6PA.Model.ExactHaltingFormula
public import M6.ConjugacyReverse
@[expose] public section
namespace M6.Arithmetic.PA.FinalEndpoint
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic

/-- Ordinary PA's own derivation of exact-machine nonhalting implying its
standard syntactic consistency sentence. No scheduler premise is admitted. -/
theorem pa_proves_nonhalting_consistency :
    theory ⊢ ExactHaltingFormula.nonhaltingSentence 🡒 M6.PA.consistencySentence := by
  have hc : theory ⊢ InternalActualRefutation.noActualRefutationSentence 🡒
      M6.PA.consistencySentence := by
    simpa only [InternalActualRefutation.noActualRefutationSentence,
      M6.PA.InternalActualRefutation.noActualRefutationSentence] using
      M6.PA.InternalActualRefutation.pa_proves_no_actual_refutation_consistency
  exact C_trans ExactHaltingFormula.pa_proves_exact_to_auxiliary
    (C_trans InternalActualRefutation.pa_proves_nonhalting_no_actual_refutation hc)

theorem nonhalting_unprovable (hcons : M6.PA.Consistent) :
    theory ⊬ ExactHaltingFormula.nonhaltingSentence :=
  M6.PA.unprovable_of_internal_consistency_implication _ hcons
    pa_proves_nonhalting_consistency

theorem nonhalting_true (hcons : M6.PA.Consistent) :
    Nat ⊧/![] ExactHaltingFormula.nonhaltingSentence := by
  apply ExactHaltingFormula.sentence_iff_physical_nonhalting.mpr
  intro hh
  exact M6.PA.literal_nonhalting hcons
    (M6.Conjugacy.halts_reflection (by decide) hh)

/-- Exact209/418-row, one-sided result under ordinary full-induction PA
consistency. This does not state two-sided independence or Lean consistency. -/
theorem literal_final_endpoint (hcons : M6.PA.Consistent) :
    M6.Literal.workingLabels.length=209 ∧
    M6.Literal.workingLabels.length*2=418 ∧
    (∀ q b,M6.Literal.machine q b≠none → q∈M6.Literal.workingLabels) ∧
    (¬ M6.Zip.Halts M6.Literal.machine M6.Startup.blank) ∧
    ExactHaltingFormula.rows.length=418 ∧
    (Nat ⊧/![] ExactHaltingFormula.nonhaltingSentence) ∧
    (theory ⊬ ExactHaltingFormula.nonhaltingSentence) :=
  ⟨M6.Literal.working_count,M6.Literal.row_count,
    fun _ _ h => M6.Bounds.domain h,M6.PA.literal_nonhalting hcons,
    ExactHaltingFormula.rows_count,nonhalting_true hcons,nonhalting_unprovable hcons⟩
#print axioms pa_proves_nonhalting_consistency
#print axioms nonhalting_unprovable
#print axioms nonhalting_true
#print axioms literal_final_endpoint
end M6.Arithmetic.PA.FinalEndpoint
