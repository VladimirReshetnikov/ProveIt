import DiophantineConsistency.IPRAOrderErasure
import DiophantineConsistency.IPRANativeTheory

/-! Preliminary erasure images of native PR defining equations. -/
set_option autoImplicit false
namespace DiophantineConsistency.IPRAErasedDefiningImages
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder
open PRAFiniteFunctionCodes IPRAOrderErasure

theorem erase_allClosure {ξ : Type} {n : ℕ}
    (φ : Semiformulaᵢ PRALanguage.language ξ n) :
    erase (∀⁰* φ) = ∀⁰* erase φ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [allClosure_succ]
    exact ih _

theorem erase_equalClosure {n : ℕ} (a b : PRATheory.TermN n) :
    erase (IPRANativeTheory.equalClosureI a b) =
      IPRAEqualityOnlyReference.equalClosure
        (Semiterm.lMap termsToReference a) (Semiterm.lMap termsToReference b) := by
  simp only [IPRANativeTheory.equalClosureI, IPRAEqualityOnlyReference.equalClosure,
    erase_allClosure, erase]
  congr 1
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun k => Fin.elim0 k) j
    rfl

theorem map_finCases {ξ : Type} {n m : ℕ}
    (a : Semiterm PRALanguage.language ξ n)
    (v : Fin m → Semiterm PRALanguage.language ξ n) :
    (fun i => Semiterm.lMap termsToReference (Fin.cases a v i)) =
      Fin.cases (Semiterm.lMap termsToReference a) (fun i => Semiterm.lMap termsToReference (v i)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem erase_zeroEquation (n : ℕ) :
    erase (IPRANativeTheory.zeroEquationI n) = IPRAEqualityOnlyReference.zeroEquation n := by
  simp only [IPRANativeTheory.zeroEquationI, IPRAEqualityOnlyReference.zeroEquation,
    erase_equalClosure, PRATheory.applyCode, IPRAEqualityOnlyReference.applyCode,
    Semiterm.lMap_func, termsToReference]
  congr 2
  funext i
  exact Fin.elim0 i

theorem erase_projectionEquation {n : ℕ} (i : Fin n) :
    erase (IPRANativeTheory.projectionEquationI i) = IPRAEqualityOnlyReference.projectionEquation i := by
  simp [IPRANativeTheory.projectionEquationI, IPRAEqualityOnlyReference.projectionEquation,
    erase_equalClosure, PRATheory.applyCode, IPRAEqualityOnlyReference.applyCode,
    PRATheory.vars, Semiterm.lMap_func, termsToReference, Function.comp_def]
  rfl

theorem erase_compositionEquation {m n : ℕ} (f : Code m) (g : Codes n m) :
    erase (IPRANativeTheory.compositionEquationI f g) =
      IPRAEqualityOnlyReference.compositionEquation f g := by
  simp [IPRANativeTheory.compositionEquationI, IPRAEqualityOnlyReference.compositionEquation,
    erase_equalClosure, PRATheory.applyCode, IPRAEqualityOnlyReference.applyCode,
    PRATheory.vars, Semiterm.lMap_func, termsToReference, Function.comp_def]
  rfl

theorem erase_recursionBaseEquation {n : ℕ} (f : Code n) (g : Code (n+2)) :
    erase (IPRANativeTheory.recursionBaseEquationI f g) =
      IPRAEqualityOnlyReference.recursionBaseEquation f g := by
  simp [IPRANativeTheory.recursionBaseEquationI, IPRAEqualityOnlyReference.recursionBaseEquation,
    erase_equalClosure, PRATheory.applyCode, IPRAEqualityOnlyReference.applyCode,
    PRATheory.vars, Semiterm.lMap_func, Function.comp_def, map_finCases]
  congr 3
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cases_zero]
    congr 1
    funext j
    exact Fin.elim0 j
  · rfl

theorem erase_recursionStepEquation {n : ℕ} (f : Code n) (g : Code (n+2)) :
    erase (IPRANativeTheory.recursionStepEquationI f g) =
      IPRAEqualityOnlyReference.recursionStepEquation f g := by
  simp [IPRANativeTheory.recursionStepEquationI, IPRAEqualityOnlyReference.recursionStepEquation,
    erase_equalClosure, PRATheory.applyCode, IPRAEqualityOnlyReference.applyCode,
    Semiterm.lMap_func, Function.comp_def, map_finCases]
  rfl

theorem defining_images {σ : Sentenceᵢ PRALanguage.language}
    (h : IPRANativeTheory.DefiningEquationI σ) :
    IPRAEqualityOnlyReference.ReferenceAxiom (erase σ) := by
  cases h with
  | zero n =>
    simpa only [erase_zeroEquation] using
      IPRAEqualityOnlyReference.ReferenceAxiom.defining (IPRAEqualityOnlyReference.DefiningEquation.zero n)
  | projection i =>
    simpa only [erase_projectionEquation] using
      IPRAEqualityOnlyReference.ReferenceAxiom.defining (IPRAEqualityOnlyReference.DefiningEquation.projection i)
  | composition f g =>
    simpa only [erase_compositionEquation] using
      IPRAEqualityOnlyReference.ReferenceAxiom.defining (IPRAEqualityOnlyReference.DefiningEquation.composition f g)
  | recursionBase f g =>
    simpa only [erase_recursionBaseEquation] using
      IPRAEqualityOnlyReference.ReferenceAxiom.defining (IPRAEqualityOnlyReference.DefiningEquation.recursionBase f g)
  | recursionStep f g =>
    simpa only [erase_recursionStepEquation] using
      IPRAEqualityOnlyReference.ReferenceAxiom.defining (IPRAEqualityOnlyReference.DefiningEquation.recursionStep f g)

end DiophantineConsistency.IPRAErasedDefiningImages
