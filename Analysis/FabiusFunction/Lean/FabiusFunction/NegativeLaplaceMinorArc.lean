import FabiusFunction.NegativeLaplaceVertical

/-!
# Uniform bounds for the negative-Laplace minor-arc constant

The vertical-product estimate contains a finite product of elementary
hyperbolic-cotangent factors.  This module supplies a simple uniform criterion
for bounding that product.  If all extracted dyadic arguments are at least
`b ≥ log 2`, the product is at most `exp (4 N exp (-b))`.  The familiar
uniform bound `exp 4` follows when `N * exp (-b) ≤ 1`.

This separates the elementary product estimate from the later choice of the
number of factors along a Lambert saddle scale.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

/-- The empty extracted product has no minor-arc loss. -/
theorem negativeLaplaceMinorArcConstant_zero (r : ℝ) :
    negativeLaplaceMinorArcConstant r 0 = 1 := by
  simp [negativeLaplaceMinorArcConstant]

/-- A positive coth factor is bounded by the exponential of its exact
geometric correction.  This is the cutoff-free form of the estimate used
below. -/
lemma negativeLaplaceCothFactor_le_exp_two_exp_neg_div
    {x : ℝ} (hx : 0 < x) :
    negativeLaplaceCothFactor x ≤
      Real.exp (2 * Real.exp (-x) / (1 - Real.exp (-x))) := by
  have hden : 0 < 1 - Real.exp (-x) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  calc
    negativeLaplaceCothFactor x =
        1 + 2 * Real.exp (-x) / (1 - Real.exp (-x)) := by
      unfold negativeLaplaceCothFactor
      field_simp [hden.ne']
      ring
    _ ≤ Real.exp (2 * Real.exp (-x) / (1 - Real.exp (-x))) := by
      simpa [add_comm] using
        Real.add_one_le_exp (2 * Real.exp (-x) / (1 - Real.exp (-x)))

/-- A coth factor is exponentially close to one once its argument is at least `log 2`. -/
lemma negativeLaplaceCothFactor_le_exp_four_exp_neg
    {x : ℝ} (hx : Real.log 2 ≤ x) :
    negativeLaplaceCothFactor x ≤ Real.exp (4 * Real.exp (-x)) := by
  have hxpos : 0 < x := (Real.log_pos (by norm_num)).trans_le hx
  have he : Real.exp (-x) ≤ (1 / 2 : ℝ) := by
    calc
      Real.exp (-x) ≤ Real.exp (-Real.log 2) :=
        Real.exp_le_exp.mpr (neg_le_neg hx)
      _ = (1 / 2 : ℝ) := by
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        norm_num
  have hden : 0 < 1 - Real.exp (-x) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hfrac : 2 * Real.exp (-x) / (1 - Real.exp (-x)) ≤
      4 * Real.exp (-x) := by
    rw [div_le_iff₀ hden]
    nlinarith [Real.exp_pos (-x)]
  calc
    negativeLaplaceCothFactor x ≤
        Real.exp (2 * Real.exp (-x) / (1 - Real.exp (-x))) :=
      negativeLaplaceCothFactor_le_exp_two_exp_neg_div hxpos
    _ ≤ Real.exp (4 * Real.exp (-x)) := Real.exp_le_exp.mpr hfrac

/-- The complete minor-arc product is controlled by its factor count and
minimum extracted argument.  No final count cutoff is imposed here. -/
theorem negativeLaplaceMinorArcConstant_le_exp_four_mul_count
    {r b : ℝ} {N : ℕ}
    (hb : Real.log 2 ≤ b)
    (harg : ∀ n < N, b ≤ r / (2 : ℝ) ^ (n + 1)) :
    negativeLaplaceMinorArcConstant r N ≤
      Real.exp (4 * ((N : ℝ) * Real.exp (-b))) := by
  unfold negativeLaplaceMinorArcConstant
  calc
    (∏ n ∈ Finset.range N,
        negativeLaplaceCothFactor (r / (2 : ℝ) ^ (n + 1))) ≤
        ∏ _n ∈ Finset.range N, Real.exp (4 * Real.exp (-b)) := by
      apply Finset.prod_le_prod
      · intro n hn
        exact (negativeLaplaceCothFactor_pos _
          ((Real.log_pos (by norm_num)).trans_le
            (hb.trans (harg n (Finset.mem_range.mp hn))))).le
      · intro n hn
        have hxn := harg n (Finset.mem_range.mp hn)
        calc
          negativeLaplaceCothFactor (r / (2 : ℝ) ^ (n + 1)) ≤
              Real.exp (4 * Real.exp (-(r / (2 : ℝ) ^ (n + 1)))) :=
            negativeLaplaceCothFactor_le_exp_four_exp_neg (hb.trans hxn)
          _ ≤ Real.exp (4 * Real.exp (-b)) := by
            apply Real.exp_le_exp.mpr
            gcongr
    _ = Real.exp (4 * ((N : ℝ) * Real.exp (-b))) := by
      rw [Finset.prod_const, Finset.card_range, ← Real.exp_nat_mul]
      congr 1
      ring

/-- A uniform bound for the complete finite minor-arc product. -/
theorem negativeLaplaceMinorArcConstant_le_exp_four
    {r b : ℝ} {N : ℕ}
    (hb : Real.log 2 ≤ b)
    (harg : ∀ n < N, b ≤ r / (2 : ℝ) ^ (n + 1))
    (hcount : (N : ℝ) * Real.exp (-b) ≤ 1) :
    negativeLaplaceMinorArcConstant r N ≤ Real.exp 4 := by
  calc
    negativeLaplaceMinorArcConstant r N ≤
        Real.exp (4 * ((N : ℝ) * Real.exp (-b))) :=
      negativeLaplaceMinorArcConstant_le_exp_four_mul_count hb harg
    _ ≤ Real.exp 4 := Real.exp_le_exp.mpr (by nlinarith)

end Fabius
