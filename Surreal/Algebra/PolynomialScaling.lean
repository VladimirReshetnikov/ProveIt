import Surreal.Algebra.PolynomialDepression
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Monic polynomial scaling over arbitrary fields

These finite algebraic change-of-variable formulas support the odd-degree
root argument in `found:sub:realclosed` and its fixed Hahn workspace version.
They require no order, valuation, coefficient summation, or real closedness.
-/

namespace Surreal.FinitePolynomial

noncomputable section

open Polynomial

variable {K : Type*} [Field K]

/-- Degree-normalized change of variable `X ↦ t * X`. -/
def scalePolynomial (P : Polynomial K) (t : K) :
    Polynomial K :=
  C ((t ^ P.natDegree)⁻¹) * P.comp (C t * X)

theorem scalePolynomial_coeff (P : Polynomial K) (t : K)
    (j : ℕ) :
    (scalePolynomial P t).coeff j = (t ^ P.natDegree)⁻¹ * (P.coeff j * t ^ j) := by
  simp only [scalePolynomial, coeff_C_mul, comp_C_mul_X_coeff]

/-- The lower-coefficient formula giving precisely the weights `n-j`. -/
theorem scalePolynomial_coeff_of_le (P : Polynomial K)
    {t : K} (ht : t ≠ 0) {j : ℕ} (hj : j ≤ P.natDegree) :
    (scalePolynomial P t).coeff j = P.coeff j / t ^ (P.natDegree - j) := by
  rw [scalePolynomial_coeff, pow_sub₀ t ht hj]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

theorem scalePolynomial_natDegree (P : Polynomial K)
    {t : K} (ht : t ≠ 0) : (scalePolynomial P t).natDegree = P.natDegree := by
  rw [scalePolynomial, natDegree_C_mul (inv_ne_zero (pow_ne_zero _ ht)),
    natDegree_comp, natDegree_C_mul_X t ht, mul_one]

theorem scalePolynomial_monic {P : Polynomial K} (hP : P.Monic)
    {t : K} (ht : t ≠ 0) : (scalePolynomial P t).Monic := by
  change (scalePolynomial P t).coeff (scalePolynomial P t).natDegree = 1
  rw [scalePolynomial_natDegree P ht, scalePolynomial_coeff_of_le P ht le_rfl,
    Nat.sub_self, pow_zero, div_one, hP.coeff_natDegree]

theorem scalePolynomial_coeff_eq_zero {P : Polynomial K}
    (t : K) {j : ℕ} (hj : P.coeff j = 0) :
    (scalePolynomial P t).coeff j = 0 := by
  simp only [scalePolynomial_coeff, hj, zero_mul, mul_zero]

/-- In particular the depressed coefficient is preserved by every nonzero scaling. -/
theorem scalePolynomial_depressed {P : Polynomial K}
    {t : K} (ht : t ≠ 0) (hP : P.coeff (P.natDegree - 1) = 0) :
    (scalePolynomial P t).coeff ((scalePolynomial P t).natDegree - 1) = 0 := by
  rw [scalePolynomial_natDegree P ht]
  exact scalePolynomial_coeff_eq_zero t hP

theorem eval_scalePolynomial (P : Polynomial K) (t x : K) :
    (scalePolynomial P t).eval x = (t ^ P.natDegree)⁻¹ * P.eval (t * x) := by
  simp [scalePolynomial, eval_comp]

/-- Roots pull back along the actual nonzero change of scale. -/
theorem isRoot_scalePolynomial_iff (P : Polynomial K)
    {t : K} (ht : t ≠ 0) (x : K) :
    (scalePolynomial P t).IsRoot x ↔ P.IsRoot (t * x) := by
  simp only [IsRoot.def, eval_scalePolynomial, mul_eq_zero,
    inv_ne_zero (pow_ne_zero P.natDegree ht), false_or]

/-- The inverse change of variable recovers the original polynomial exactly,
so a later factorization of the scaled polynomial can be pulled back. -/
theorem scalePolynomial_reconstruct (P : Polynomial K)
    {t : K} (ht : t ≠ 0) :
    C (t ^ P.natDegree) * (scalePolynomial P t).comp (C t⁻¹ * X) = P := by
  ext j
  rw [coeff_C_mul, comp_C_mul_X_coeff, scalePolynomial_coeff, inv_pow]
  field_simp

/-- A monic polynomial other than a pure power has a nonzero lower coefficient. -/
theorem exists_lowerCoeff_ne_zero {P : Polynomial K}
    (hm : P.Monic) (hP : P ≠ X ^ P.natDegree) :
    ∃ j : Fin P.natDegree, P.coeff j.val ≠ 0 := by
  classical
  by_contra! h
  apply hP
  ext j
  rcases lt_trichotomy j P.natDegree with hj | rfl | hj
  · rw [h ⟨j, hj⟩, coeff_X_pow, if_neg hj.ne]
  · rw [hm.coeff_natDegree, coeff_X_pow_self]
  · rw [coeff_eq_zero_of_natDegree_lt hj, coeff_X_pow, if_neg hj.ne']

/-- Translation to depressed form followed by scaling is an explicit affine
change of variable. -/
theorem scalePolynomial_depress_eq (P : K[X]) (t : K) :
    scalePolynomial (depress P) t =
      C ((t ^ P.natDegree)⁻¹) * P.comp (C t * X - C (depressionShift P)) := by
  rw [scalePolynomial, natDegree_depress, depress_eq_comp, comp_assoc,
    sub_comp, X_comp, C_comp]

/-- A root of the normalized depressed polynomial pulls back by the affine map. -/
theorem isRoot_scalePolynomial_depress_iff (P : K[X]) {t : K} (ht : t ≠ 0) (x : K) :
    (scalePolynomial (depress P) t).IsRoot x ↔ P.IsRoot (t * x - depressionShift P) :=
  (isRoot_scalePolynomial_iff (depress P) ht x).trans (isRoot_depress_iff P (t * x))

end

end Surreal.FinitePolynomial
