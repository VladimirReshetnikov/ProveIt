import DiophantineConsistency.IPRAErasedEqualityImages

/-! Exploratory syntactic erasure of native addition-step induction. -/
set_option autoImplicit false
namespace DiophantineConsistency.IPRAErasedInductionShape
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder
open IPRAOrderErasure IPRAOrderErasureRew IPRAErasedDefiningImages

def stepTerm (n : ℕ) : IPRAEqualityOnlyReference.TermN (n+1) :=
  .func PRALanguage.addCode ![#0, .func PRALanguage.oneCode Fin.elim0]

def atStep {n : ℕ} (φ : Semisentenceᵢ IPRAEqualityOnlyReference.language (n+1)) :
    Semisentenceᵢ IPRAEqualityOnlyReference.language (n+1) :=
  Rew.subst (Fin.cases (stepTerm n) (fun i => #i.succ)) ▹ φ

def inductionAxiom {n : ℕ} (φ : Semisentenceᵢ IPRAEqualityOnlyReference.language (n+1)) :
    Sentenceᵢ IPRAEqualityOnlyReference.language :=
  ∀⁰* (IPRAEqualityOnlyReference.atZero φ 🡒 (∀⁰ (φ 🡒 atStep φ)) 🡒 ∀⁰ φ)

theorem erase_atZero {n : ℕ} (φ : Semisentenceᵢ PRALanguage.language (n+1)) :
    erase (IPRANativeInduction.atZero φ) = IPRAEqualityOnlyReference.atZero (erase φ) := by
  unfold IPRANativeInduction.atZero IPRAEqualityOnlyReference.atZero
  rw [erase_rew, eraseRew_subst]
  congr 2
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [IPRANativeInduction.zeroTerm, IPRAEqualityOnlyReference.applyCode,
      Semiterm.lMap_func, termsToReference]
    funext k
    exact Fin.elim0 k
  · rfl

theorem erase_atStep {n : ℕ} (φ : Semisentenceᵢ PRALanguage.language (n+1)) :
    erase (IPRANativeInduction.atStep φ) = atStep (erase φ) := by
  unfold IPRANativeInduction.atStep atStep
  rw [erase_rew, eraseRew_subst]
  congr 2
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cases_zero, IPRANativeInduction.stepTerm, stepTerm,
      Semiterm.lMap_func, termsToReference, Function.comp_def]
    congr 1
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · rfl
    · refine Fin.cases ?_ (fun k => Fin.elim0 k) k
      simp [Semiterm.lMap_func]
      funext k
      exact Fin.elim0 k
  · rfl

theorem erase_inductionAxiom {n : ℕ} (φ : Semisentenceᵢ PRALanguage.language (n+1)) :
    erase (IPRANativeInduction.inductionAxiom φ) = inductionAxiom (erase φ) := by
  simp only [IPRANativeInduction.inductionAxiom, IPRANativeInduction.inductionBody,
    inductionAxiom, erase_allClosure, erase, erase_atZero, erase_atStep]
  rfl

end DiophantineConsistency.IPRAErasedInductionShape
