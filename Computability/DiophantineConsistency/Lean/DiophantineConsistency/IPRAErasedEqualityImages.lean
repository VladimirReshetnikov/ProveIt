import DiophantineConsistency.IPRAErasedDefiningImages
import DiophantineConsistency.IPRAOrderErasureRew

/-! Preliminary erasure images of native equality and successor-nonzero axioms. -/
set_option autoImplicit false
namespace DiophantineConsistency.IPRAErasedEqualityImages
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder
open IPRAOrderErasure IPRAOrderErasureRew IPRAErasedDefiningImages

theorem erase_eqRefl :
    erase IPRANativeTheory.eqReflI = IPRAEqualityOnlyReference.eqRefl := by
  simp only [IPRANativeTheory.eqReflI, IPRAEqualityOnlyReference.eqRefl,
    erase_allClosure, erase]
  congr 1
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun k => Fin.elim0 k) j
    rfl

theorem erase_eqLeft {n : ℕ} (φ : Semisentenceᵢ PRALanguage.language (n+1)) :
    erase (IPRANativeTheory.eqLeft φ) = IPRAEqualityOnlyReference.eqLeft (erase φ) := by
  unfold IPRANativeTheory.eqLeft IPRAEqualityOnlyReference.eqLeft
  rw [erase_rew, eraseRew_subst]
  congr 2
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem erase_eqRight {n : ℕ} (φ : Semisentenceᵢ PRALanguage.language (n+1)) :
    erase (IPRANativeTheory.eqRight φ) = IPRAEqualityOnlyReference.eqRight (erase φ) := by
  unfold IPRANativeTheory.eqRight IPRAEqualityOnlyReference.eqRight
  rw [erase_rew, eraseRew_subst]
  congr 2
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem erase_eqSubstitution {n : ℕ} (φ : Semisentenceᵢ PRALanguage.language (n+1)) :
    erase (IPRANativeTheory.eqSubstitutionI φ) =
      IPRAEqualityOnlyReference.eqSubstitution (erase φ) := by
  simp only [IPRANativeTheory.eqSubstitutionI, IPRAEqualityOnlyReference.eqSubstitution,
    erase_allClosure, erase, erase_eqLeft, erase_eqRight]
  congr 2
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun k => Fin.elim0 k) j
    rfl

theorem equality_images {σ : Sentenceᵢ PRALanguage.language}
    (h : IPRANativeTheory.EqualityAxiomI σ) :
    IPRAEqualityOnlyReference.ReferenceAxiom (erase σ) := by
  cases h with
  | refl =>
    simpa only [erase_eqRefl] using
      IPRAEqualityOnlyReference.ReferenceAxiom.equality IPRAEqualityOnlyReference.EqualityAxiom.refl
  | substitution φ =>
    simpa only [erase_eqSubstitution] using
      IPRAEqualityOnlyReference.ReferenceAxiom.equality
        (IPRAEqualityOnlyReference.EqualityAxiom.substitution (erase φ))

theorem erase_successorNonzero :
    erase IPRANativeTheory.succNonzeroI = IPRAEqualityOnlyReference.successorNonzero := by
  simp only [IPRANativeTheory.succNonzeroI, IPRAEqualityOnlyReference.successorNonzero,
    erase_allClosure, Semiformulaᵢ.neg_def, erase]
  congr 3
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun k => Fin.elim0 k) j
    simp [PRATheory.applyCode, IPRAEqualityOnlyReference.applyCode,
      Semiterm.lMap_func, termsToReference]
    funext k
    exact Fin.elim0 k

end DiophantineConsistency.IPRAErasedEqualityImages
