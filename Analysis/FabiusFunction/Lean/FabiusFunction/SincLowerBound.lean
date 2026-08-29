import FabiusFunction.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The real sinc function and its quadratic lower bound

The corpus carries the entire `complexSinc`; the product estimates
need its real restriction together with the elementary two-sided
bound

`1 - x²/6 ≤ sinc x ≤ 1`.

The lower bound is the cubic sine estimate `x - x³/6 < sin x`
divided by `x`, extended to negative `x` by evenness and to `x = 0`
by the normalization `sinc 0 = 1`.  Paired with the Weierstrass
product inequality it converts a summable family of squared
arguments into a lower bound for a sinc product, which is how the
dyadic products are kept away from zero.

* `realSinc` — the real sinc, normalized to `1` at the origin;
* `complexSinc_ofReal` — the bridge to the corpus's entire version;
* `realSinc_neg` — evenness;
* `one_sub_sq_div_six_le_realSinc` — **the quadratic lower bound**;
* `realSinc_le_one`, `abs_realSinc_le_one` — the upper bounds.
-/

set_option autoImplicit false

namespace Fabius

/-- The real sinc function `sin x / x`, normalized to `1` at the
origin. -/
noncomputable def realSinc (x : ℝ) : ℝ :=
  if x = 0 then 1 else Real.sin x / x

@[simp] theorem realSinc_zero : realSinc 0 = 1 := by
  rw [realSinc, if_pos rfl]

theorem realSinc_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    realSinc x = Real.sin x / x := by
  rw [realSinc, if_neg hx]

/-- The corpus's entire sinc restricts to the real one. -/
theorem complexSinc_ofReal (x : ℝ) :
    complexSinc ((x : ℝ) : ℂ) = ((realSinc x : ℝ) : ℂ) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [complexSinc, realSinc]
  · have hxC : ((x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
    rw [complexSinc, if_neg hxC, realSinc_of_ne_zero hx,
      ← Complex.ofReal_sin, ← Complex.ofReal_div]

/-- The real sinc is even. -/
@[simp] theorem realSinc_neg (x : ℝ) : realSinc (-x) = realSinc x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [realSinc_of_ne_zero (neg_ne_zero.mpr hx),
      realSinc_of_ne_zero hx, Real.sin_neg, neg_div_neg_eq]

/-- The quadratic lower bound on the positive axis. -/
private theorem one_sub_sq_div_six_le_realSinc_of_pos {x : ℝ}
    (hx : 0 < x) : 1 - x ^ 2 / 6 ≤ realSinc x := by
  have hcube := Real.sin_gt_sub_cube hx
  rw [realSinc_of_ne_zero (ne_of_gt hx), le_div_iff₀ hx]
  nlinarith [hcube]

/-- **The quadratic lower bound**: `1 - x²/6 ≤ sinc x` for every real
`x`.  At `x = 0` it is the normalization; for `x > 0` it is the cubic
sine estimate divided by `x`; for `x < 0` it follows by evenness. -/
theorem one_sub_sq_div_six_le_realSinc (x : ℝ) :
    1 - x ^ 2 / 6 ≤ realSinc x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have h := one_sub_sq_div_six_le_realSinc_of_pos (neg_pos.mpr hx)
    rwa [realSinc_neg, neg_sq] at h
  · simp
  · exact one_sub_sq_div_six_le_realSinc_of_pos hx

/-- The real sinc never exceeds one in absolute value. -/
theorem abs_realSinc_le_one (x : ℝ) : |realSinc x| ≤ 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [realSinc_of_ne_zero hx, abs_div]
    refine div_le_one_of_le₀ (Real.abs_sin_le_abs) (abs_nonneg _)

/-- The real sinc never exceeds one. -/
theorem realSinc_le_one (x : ℝ) : realSinc x ≤ 1 :=
  (le_abs_self _).trans (abs_realSinc_le_one x)

/-- On `|x| ≤ √6` the sinc is nonnegative, by the quadratic lower
bound. -/
theorem realSinc_nonneg_of_sq_le_six {x : ℝ} (hx : x ^ 2 ≤ 6) :
    0 ≤ realSinc x := by
  have h := one_sub_sq_div_six_le_realSinc x
  have h6 : x ^ 2 / 6 ≤ 1 := by linarith
  linarith

end Fabius
