import Surreal.Algebra.PolynomialScaling
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Tactic.LinearCombination

/-!
# Polynomial normalization at a proposed root scale

For the algebraic existence step of `trigonometry:thm:stability`, substitute
`H = λY` and divide by `Aλ`. This module records the exact coefficients,
root correspondence and preservation of native root multiplicities.
-/

namespace Surreal.FinitePolynomial

open Polynomial

noncomputable section

variable {K : Type*} [Field K]

/-- Normalize a root equation by its linear coefficient and displacement scale. -/
def rootNormalization (P : K[X]) (A l : K) : K[X] := C ((A * l)⁻¹) * P.comp (C l * X)

theorem rootNormalization_coeff (P : K[X]) (A l : K) (n : ℕ) :
    (rootNormalization P A l).coeff n = P.coeff n * l ^ n / (A * l) := by
  simp only [rootNormalization, coeff_C_mul, comp_C_mul_X_coeff, div_eq_mul_inv]
  ring

@[simp] theorem rootNormalization_coeff_zero (P : K[X]) (A l : K) :
    (rootNormalization P A l).coeff 0 = P.coeff 0 / (A * l) := by
  simp [rootNormalization_coeff]

theorem rootNormalization_coeff_one (P : K[X]) (A l : K) (hl : l ≠ 0) :
    (rootNormalization P A l).coeff 1 = P.coeff 1 / A := by
  rw [rootNormalization_coeff]
  simp [div_eq_mul_inv, mul_inv_rev, hl, mul_assoc]

/-- Each higher coefficient contains the small ratio `λ/A`. -/
theorem rootNormalization_coeff_add_two (P : K[X]) (A l : K) (hl : l ≠ 0) (n : ℕ) :
    (rootNormalization P A l).coeff (n + 2) = P.coeff (n + 2) * (l / A) * l ^ n := by
  rw [rootNormalization_coeff, pow_add]
  simp only [div_eq_mul_inv, mul_inv_rev, pow_two]
  calc
    _ = P.coeff (n + 2) * l * A⁻¹ * l ^ n * (l * l⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hl, mul_one]; ring

@[simp] theorem eval_rootNormalization (P : K[X]) (A l y : K) :
    (rootNormalization P A l).eval y = P.eval (l * y) / (A * l) := by
  simp only [rootNormalization, eval_mul, eval_C, eval_comp, eval_X, div_eq_mul_inv]
  ring

/-- Nonzero normalization factors preserve the exact equation. -/
theorem isRoot_rootNormalization_iff (P : K[X]) (A l y : K) (hA : A ≠ 0) (hl : l ≠ 0) :
    (rootNormalization P A l).IsRoot y ↔ P.IsRoot (l * y) := by
  simp only [IsRoot.def, eval_rootNormalization, div_eq_zero_iff, mul_ne_zero hA hl,
    or_false]

/-- Root multiplicities survive both multiplication by a constant and the invertible change. -/
theorem rootMultiplicity_rootNormalization (P : K[X]) (A l y : K) (hl : l ≠ 0)
    (hP : rootNormalization P A l ≠ 0) :
    (rootNormalization P A l).rootMultiplicity y = P.rootMultiplicity (l * y) := by
  rw [rootNormalization, rootMultiplicity_mul hP, rootMultiplicity_C, zero_add]
  simpa only [map_zero, add_zero] using
    rootMultiplicity_comp_C_mul_X_add_C P l 0 y (isUnit_iff_ne_zero.mpr hl)

/-- Exact separation of a polynomial into constant, linear and quadratic-remainder terms. -/
theorem eval_constant_linear_quadratic (P : K[X]) (h : K) :
    P.eval h = P.coeff 0 + P.coeff 1 * h + h ^ 2 * P.divX.divX.eval h := by
  have h0 := congrArg (fun Q : K[X] => Q.eval h) (X_mul_divX_add P)
  have h1 := congrArg (fun Q : K[X] => Q.eval h) (X_mul_divX_add P.divX)
  simp only [eval_add, eval_mul, eval_X, eval_C, coeff_divX, Nat.zero_add] at h0 h1
  linear_combination -h0 - h * h1

end
end Surreal.FinitePolynomial
