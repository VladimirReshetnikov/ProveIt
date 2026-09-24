import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Absolute-value bounds for square roots of integers

The estimates include negative integer radicands and complex square roots.
They provide the separation gap and a polynomial majorant used in the
relation-combining theorem.
-/

namespace Diophantine.RadicalBounds

theorem norm_sq_of_sq_eq_int {z : ℂ} {a : ℤ} (hsq : z ^ 2 = (a : ℂ)) :
    ‖z‖ ^ 2 = |(a : ℝ)| := by
  have h := congrArg norm hsq
  simpa only [norm_pow, Complex.norm_intCast] using h

/-- Every nonzero complex square root of an integer has norm at least one. -/
theorem one_le_norm_of_sq_eq_int {z : ℂ} {a : ℤ}
    (hsq : z ^ 2 = (a : ℂ)) (hz : z ≠ 0) : 1 ≤ ‖z‖ := by
  have ha : a ≠ 0 := by
    intro ha
    have hzero : z ^ 2 = 0 := by simpa only [ha, Int.cast_zero] using hsq
    exact (pow_ne_zero 2 hz) hzero
  have habs : (1 : ℤ) ≤ |a| := by
    have : (0 : ℤ) < |a| := abs_pos.mpr ha
    omega
  have habsR : (1 : ℝ) ≤ |(a : ℝ)| := by exact_mod_cast habs
  have hnorm := norm_sq_of_sq_eq_int hsq
  have hn := norm_nonneg z
  nlinarith

/-- The square of the integer radicand is a uniform polynomial majorant
for the norm of either square root. -/
theorem norm_le_sq_of_sq_eq_int {z : ℂ} {a : ℤ}
    (hsq : z ^ 2 = (a : ℂ)) : ‖z‖ ≤ (a : ℝ) ^ 2 := by
  by_cases hz : z = 0
  · subst z
    simp only [norm_zero]
    positivity
  have hgap := one_le_norm_of_sq_eq_int hsq hz
  have hnorm := norm_sq_of_sq_eq_int hsq
  have habs : ‖z‖ ≤ |(a : ℝ)| := by nlinarith
  have habs1 : 1 ≤ |(a : ℝ)| := hgap.trans habs
  have hsqabs := sq_abs (a : ℝ)
  nlinarith

end Diophantine.RadicalBounds
