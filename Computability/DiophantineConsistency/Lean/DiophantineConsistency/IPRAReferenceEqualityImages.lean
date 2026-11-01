import DiophantineConsistency.IPRAReferenceImages
import DiophantineConsistency.IPRAReferenceRew

/-! Preliminary equality and successor-nonzero reference axiom images. -/
set_option autoImplicit false
namespace DiophantineConsistency.IPRAReferenceEqualityImages
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder
open IPRAOrderErasure IPRAReferenceRew IPRAReferenceImages

theorem embed_eqRefl :
    embed IPRAEqualityOnlyReference.eqRefl = IPRANativeTheory.eqReflI := by
  simp only [IPRAEqualityOnlyReference.eqRefl, IPRANativeTheory.eqReflI,
    embed_allClosure, embed]
  congr 1
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun k => Fin.elim0 k) j
    rfl

theorem embed_eqLeft {n : ℕ} (φ : Semisentenceᵢ IPRAEqualityOnlyReference.language (n+1)) :
    embed (IPRAEqualityOnlyReference.eqLeft φ) = IPRANativeTheory.eqLeft (embed φ) := by
  unfold IPRAEqualityOnlyReference.eqLeft IPRANativeTheory.eqLeft
  rw [embed_rew, embedRew_subst]
  congr 2
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem embed_eqRight {n : ℕ} (φ : Semisentenceᵢ IPRAEqualityOnlyReference.language (n+1)) :
    embed (IPRAEqualityOnlyReference.eqRight φ) = IPRANativeTheory.eqRight (embed φ) := by
  unfold IPRAEqualityOnlyReference.eqRight IPRANativeTheory.eqRight
  rw [embed_rew, embedRew_subst]
  congr 2
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem embed_eqSubstitution {n : ℕ}
    (φ : Semisentenceᵢ IPRAEqualityOnlyReference.language (n+1)) :
    embed (IPRAEqualityOnlyReference.eqSubstitution φ) =
      IPRANativeTheory.eqSubstitutionI (embed φ) := by
  simp only [IPRAEqualityOnlyReference.eqSubstitution, IPRANativeTheory.eqSubstitutionI,
    embed_allClosure, embed, embed_eqLeft, embed_eqRight]
  congr 2
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun k => Fin.elim0 k) j
    rfl

theorem equality_images {σ : Sentenceᵢ IPRAEqualityOnlyReference.language}
    (h : IPRAEqualityOnlyReference.EqualityAxiom σ) :
    IPRANativeTheory.NativeAxiom (embed σ) := by
  cases h with
  | refl =>
    simpa only [embed_eqRefl] using
      IPRANativeTheory.NativeAxiom.equality IPRANativeTheory.EqualityAxiomI.refl
  | substitution φ =>
    simpa only [embed_eqSubstitution] using
      IPRANativeTheory.NativeAxiom.equality (IPRANativeTheory.EqualityAxiomI.substitution (embed φ))

theorem embed_successorNonzero :
    embed IPRAEqualityOnlyReference.successorNonzero = IPRANativeTheory.succNonzeroI := by
  simp only [IPRAEqualityOnlyReference.successorNonzero, IPRANativeTheory.succNonzeroI,
    embed_allClosure, Semiformulaᵢ.neg_def, embed]
  congr 3
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun k => Fin.elim0 k) j
    simp [IPRAEqualityOnlyReference.applyCode, PRATheory.applyCode, Semiterm.lMap_func, toNative]
    funext k
    exact Fin.elim0 k

end DiophantineConsistency.IPRAReferenceEqualityImages
