/- Modified for ProveIt: adapt import paths to Mathlib v4.32.0.
Mathematical statements and proofs unchanged. -/
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Data.Real.Basic

namespace OAI

section

namespace Erdos3

open MvPolynomial

variable {U B : Type*}

noncomputable def normalizedRealPolynomialChart (H : U → ℝ)
    (A : B → MvPolynomial U ℝ) : U ⊕ B → MvPolynomial (U ⊕ B) ℝ :=
  Sum.elim (fun i => C ((H i)⁻¹) * X (Sum.inl i))
    (fun j => X (Sum.inr j) - rename Sum.inl (A j))

@[simp] theorem normalizedRealPolynomialChart_inl (H : U → ℝ)
    (A : B → MvPolynomial U ℝ) (i : U) :
    normalizedRealPolynomialChart H A (Sum.inl i) = C ((H i)⁻¹) * X (Sum.inl i) :=
  rfl

@[simp] theorem normalizedRealPolynomialChart_inr (H : U → ℝ)
    (A : B → MvPolynomial U ℝ) (j : B) :
    normalizedRealPolynomialChart H A (Sum.inr j) =
      X (Sum.inr j) - rename Sum.inl (A j) :=
  rfl

@[simp] theorem normalizedRealPolynomialChart_eval (H : U → ℝ)
    (A : B → MvPolynomial U ℝ) (u : U → ℝ) (b : B → ℝ) (j : U ⊕ B) :
    eval (Sum.elim u b) (normalizedRealPolynomialChart H A j) =
      Sum.elim (fun i => u i / H i) (fun i => b i - eval u (A i)) j := by
  cases j <;>
    simp [normalizedRealPolynomialChart, eval_rename, Function.comp_def,
      div_eq_mul_inv, mul_comm]

theorem normalizedRealPolynomialChart_eval_comp (H : U → ℝ)
    (A : B → MvPolynomial U ℝ) (u : U → ℝ) (b : B → ℝ) :
    eval (Sum.elim u b) ∘ normalizedRealPolynomialChart H A =
      Sum.elim (fun i => u i / H i) (fun i => b i - eval u (A i)) := by
  funext j
  exact normalizedRealPolynomialChart_eval H A u b j

theorem eval_normalizedRealPolynomialChart_substitution (H : U → ℝ)
    (A : B → MvPolynomial U ℝ) (u : U → ℝ) (b : B → ℝ)
    (p : MvPolynomial (U ⊕ B) ℝ) :
    eval (Sum.elim u b) (eval₂Hom C (normalizedRealPolynomialChart H A) p) =
      eval (Sum.elim (fun i => u i / H i) (fun i => b i - eval u (A i))) p := by
  rw [coe_eval₂Hom, ← eval_assoc, normalizedRealPolynomialChart_eval_comp]

end Erdos3

end

end OAI
