import DiophantineConsistency.IPRAOrderErasure
import DiophantineConsistency.IPRANativeTheory

/-! Preliminary syntactic images of equality-only reference axioms. -/
set_option autoImplicit false
namespace DiophantineConsistency.IPRAReferenceImages
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder
open PRAFiniteFunctionCodes IPRAOrderErasure

theorem embed_allClosure {ξ : Type} {n : ℕ}
    (φ : Semiformulaᵢ IPRAEqualityOnlyReference.language ξ n) :
    embed (∀⁰* φ) = ∀⁰* embed φ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [allClosure_succ]
    exact ih _

theorem embed_equalClosure {n : ℕ} (a b : IPRAEqualityOnlyReference.TermN n) :
    embed (IPRAEqualityOnlyReference.equalClosure a b) =
      IPRANativeTheory.equalClosureI (Semiterm.lMap toNative a) (Semiterm.lMap toNative b) := by
  simp only [IPRAEqualityOnlyReference.equalClosure, IPRANativeTheory.equalClosureI,
    embed_allClosure, embed]
  congr 1
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun k => Fin.elim0 k) j
    rfl

theorem map_finCases {ξ : Type} {n m : ℕ}
    (a : Semiterm IPRAEqualityOnlyReference.language ξ n)
    (v : Fin m → Semiterm IPRAEqualityOnlyReference.language ξ n) :
    (fun i => Semiterm.lMap toNative (Fin.cases a v i)) =
      Fin.cases (Semiterm.lMap toNative a) (fun i => Semiterm.lMap toNative (v i)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem embed_zeroEquation (n : ℕ) :
    embed (IPRAEqualityOnlyReference.zeroEquation n) = IPRANativeTheory.zeroEquationI n := by
  simp only [IPRAEqualityOnlyReference.zeroEquation, IPRANativeTheory.zeroEquationI,
    embed_equalClosure, IPRAEqualityOnlyReference.applyCode, PRATheory.applyCode,
    Semiterm.lMap_func, toNative]
  congr 2
  funext i
  exact Fin.elim0 i

theorem embed_projectionEquation {n : ℕ} (i : Fin n) :
    embed (IPRAEqualityOnlyReference.projectionEquation i) =
      IPRANativeTheory.projectionEquationI i := by
  simp [IPRAEqualityOnlyReference.projectionEquation, IPRANativeTheory.projectionEquationI,
    embed_equalClosure, IPRAEqualityOnlyReference.applyCode, PRATheory.applyCode,
    IPRAEqualityOnlyReference.vars, Semiterm.lMap_func, toNative,
    Function.comp_def]
  rfl

theorem embed_compositionEquation {m n : ℕ} (f : Code m) (g : Codes n m) :
    embed (IPRAEqualityOnlyReference.compositionEquation f g) =
      IPRANativeTheory.compositionEquationI f g := by
  simp [IPRAEqualityOnlyReference.compositionEquation, IPRANativeTheory.compositionEquationI,
    embed_equalClosure, IPRAEqualityOnlyReference.applyCode, PRATheory.applyCode,
    IPRAEqualityOnlyReference.vars, Semiterm.lMap_func, toNative,
    Function.comp_def]
  rfl

theorem embed_recursionBaseEquation {n : ℕ} (f : Code n) (g : Code (n+2)) :
    embed (IPRAEqualityOnlyReference.recursionBaseEquation f g) =
      IPRANativeTheory.recursionBaseEquationI f g := by
  simp [IPRAEqualityOnlyReference.recursionBaseEquation, IPRANativeTheory.recursionBaseEquationI,
    embed_equalClosure, IPRAEqualityOnlyReference.applyCode, PRATheory.applyCode,
    IPRAEqualityOnlyReference.vars, Semiterm.lMap_func, Function.comp_def, map_finCases]
  congr 3
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cases_zero]
    congr 1
    funext j
    exact Fin.elim0 j
  · rfl

theorem embed_recursionStepEquation {n : ℕ} (f : Code n) (g : Code (n+2)) :
    embed (IPRAEqualityOnlyReference.recursionStepEquation f g) =
      IPRANativeTheory.recursionStepEquationI f g := by
  simp [IPRAEqualityOnlyReference.recursionStepEquation, IPRANativeTheory.recursionStepEquationI,
    embed_equalClosure, IPRAEqualityOnlyReference.applyCode, PRATheory.applyCode,
    Semiterm.lMap_func, Function.comp_def, map_finCases]
  rfl

theorem defining_images {σ : Sentenceᵢ IPRAEqualityOnlyReference.language}
    (h : IPRAEqualityOnlyReference.DefiningEquation σ) :
    IPRANativeTheory.NativeAxiom (embed σ) := by
  cases h with
  | zero n =>
    simpa only [embed_zeroEquation] using
      IPRANativeTheory.NativeAxiom.defining (IPRANativeTheory.DefiningEquationI.zero n)
  | projection i =>
    simpa only [embed_projectionEquation] using
      IPRANativeTheory.NativeAxiom.defining (IPRANativeTheory.DefiningEquationI.projection i)
  | composition f g =>
    simpa only [embed_compositionEquation] using
      IPRANativeTheory.NativeAxiom.defining (IPRANativeTheory.DefiningEquationI.composition f g)
  | recursionBase f g =>
    simpa only [embed_recursionBaseEquation] using
      IPRANativeTheory.NativeAxiom.defining (IPRANativeTheory.DefiningEquationI.recursionBase f g)
  | recursionStep f g =>
    simpa only [embed_recursionStepEquation] using
      IPRANativeTheory.NativeAxiom.defining (IPRANativeTheory.DefiningEquationI.recursionStep f g)

end DiophantineConsistency.IPRAReferenceImages
