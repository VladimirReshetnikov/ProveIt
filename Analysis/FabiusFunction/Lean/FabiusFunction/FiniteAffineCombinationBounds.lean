import Mathlib.Algebra.Module.BigOperators
import Mathlib.Analysis.Normed.Module.Basic

/-!
# Bounds for finite affine combinations

This module isolates the elementary estimate behind quantitative Toeplitz
arguments.  If a finite family of scalar weights has total mass one, its
weighted sum can be recentered at any reference point.  The triangle
inequality and boundedness of scalar multiplication then bound the resulting
error by the weighted sum of the pointwise errors.

The weights need not be nonnegative or real: the loss is their total
variation, expressed by their norms.  The target may be any seminormed space
over any normed field.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

variable {ι 𝕜 E : Type*}
  [NormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Two finite linear combinations with the same coefficients differ by at
most the sum of the coefficient norms times the pointwise differences.  This
linear estimate needs no normalization or sign condition on the
coefficients. -/
theorem norm_sum_smul_sub_sum_smul_le
    (s : Finset ι) (w : ι → 𝕜) (x z : ι → E) :
    ‖(∑ i ∈ s, w i • x i) - ∑ i ∈ s, w i • z i‖ ≤
      ∑ i ∈ s, ‖w i‖ * ‖x i - z i‖ := by
  have hrecenter :
      (∑ i ∈ s, w i • x i) - ∑ i ∈ s, w i • z i =
        ∑ i ∈ s, w i • (x i - z i) := by
    simp_rw [smul_sub]
    rw [Finset.sum_sub_distrib]
  rw [hrecenter]
  exact norm_sum_le_of_le s fun i _hi => norm_smul_le (w i) (x i - z i)

/-- The error of a finite affine combination is at most the sum of the
coefficient norms times the corresponding pointwise errors.

No sign condition is imposed on the coefficients.  The sole affine
hypothesis `∑ i ∈ s, w i = 1` permits the exact recentering

`(∑ i ∈ s, w i • x i) - y = ∑ i ∈ s, w i • (x i - y)`.
-/
theorem norm_sum_smul_sub_le
    (s : Finset ι) (w : ι → 𝕜) (x : ι → E) (y : E)
    (hw : ∑ i ∈ s, w i = 1) :
    ‖(∑ i ∈ s, w i • x i) - y‖ ≤
      ∑ i ∈ s, ‖w i‖ * ‖x i - y‖ := by
  have hconst : (∑ i ∈ s, w i • y) = y := by
    rw [← Finset.sum_smul, hw, one_smul]
  calc
    ‖(∑ i ∈ s, w i • x i) - y‖ =
        ‖(∑ i ∈ s, w i • x i) -
          ∑ i ∈ s, w i • y‖ := by rw [hconst]
    _ ≤ ∑ i ∈ s, ‖w i‖ * ‖x i - y‖ :=
      norm_sum_smul_sub_sum_smul_le s w x (fun _ => y)

/-- Pointwise-majorant form of `norm_sum_smul_sub_le`: any bounds `r i` for
the individual errors may be summed after multiplication by the coefficient
norms.  No separate nonnegativity assumption on `r` is needed. -/
theorem norm_sum_smul_sub_le_of_norm_sub_le
    (s : Finset ι) (w : ι → 𝕜) (x : ι → E) (y : E) (r : ι → ℝ)
    (hw : ∑ i ∈ s, w i = 1)
    (hr : ∀ i ∈ s, ‖x i - y‖ ≤ r i) :
    ‖(∑ i ∈ s, w i • x i) - y‖ ≤
      ∑ i ∈ s, ‖w i‖ * r i := by
  exact (norm_sum_smul_sub_le s w x y hw).trans
    (Finset.sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_left (hr i hi) (norm_nonneg (w i)))

/-- Metric form of `norm_sum_smul_sub_le`. -/
theorem dist_sum_smul_le
    (s : Finset ι) (w : ι → 𝕜) (x : ι → E) (y : E)
    (hw : ∑ i ∈ s, w i = 1) :
    dist (∑ i ∈ s, w i • x i) y ≤
      ∑ i ∈ s, ‖w i‖ * dist (x i) y := by
  simpa only [dist_eq_norm] using norm_sum_smul_sub_le s w x y hw

end Fabius
