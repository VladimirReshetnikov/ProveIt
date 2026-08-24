import FabiusFunction.LaplaceMoments

/-!
# Derivatives of the negative-Laplace logarithm

This module expresses the first four logarithmic derivatives of the exact
negative-Laplace product in terms of normalized exponentially tilted moments.
If `M_k(s)` is the tilted `k`th moment and `R_k=M_k/M_0`, then

`R_k' = -R_(k+1) + R_k R_1`.

The successive derivatives of `negativeLaplaceLog` are therefore the usual
first four cumulant polynomials in the `R_k`.  These formulas isolate the
real saddle location, variance, cubic correction, and fourth-order error
needed by the quantitative saddle-point argument.
-/

set_option autoImplicit false

open Filter Set Topology

namespace Fabius

/-- A tilted moment normalized by the negative Laplace transform. -/
noncomputable def normalizedLaplaceMoment
    (F : BoundedFabius) (k : ℕ) (s : ℝ) : ℝ :=
  fabiusLaplaceMoment F k s / fabiusLaplaceMoment F 0 s

/-- The negative Laplace transform is strictly positive at positive scale. -/
theorem fabiusLaplaceMoment_zero_pos
    (F : BoundedFabius) (hF : IsFabius F) {s : ℝ} (hs : 0 < s) :
    0 < fabiusLaplaceMoment F 0 s := by
  rw [fabiusLaplaceMoment_zero]
  rw [← exp_negativeLaplaceLog_eq_generatingFunction_neg F hF s hs]
  exact Real.exp_pos _

/-- The exact logarithmic product is the logarithm of the negative Laplace
transform. -/
theorem negativeLaplaceLog_eq_log_laplaceMoment
    (F : BoundedFabius) (hF : IsFabius F) {s : ℝ} (hs : 0 < s) :
    negativeLaplaceLog s = Real.log (fabiusLaplaceMoment F 0 s) := by
  rw [fabiusLaplaceMoment_zero,
    ← exp_negativeLaplaceLog_eq_generatingFunction_neg F hF s hs,
    Real.log_exp]

/-- Logarithmic derivative of the negative Laplace transform. -/
noncomputable def negativeLaplaceLogFirst
    (F : BoundedFabius) (s : ℝ) : ℝ :=
  -normalizedLaplaceMoment F 1 s

/-- Second logarithmic derivative (the tilted variance). -/
noncomputable def negativeLaplaceLogSecond
    (F : BoundedFabius) (s : ℝ) : ℝ :=
  normalizedLaplaceMoment F 2 s - normalizedLaplaceMoment F 1 s ^ 2

/-- Third logarithmic derivative. -/
noncomputable def negativeLaplaceLogThird
    (F : BoundedFabius) (s : ℝ) : ℝ :=
  -normalizedLaplaceMoment F 3 s +
    3 * normalizedLaplaceMoment F 1 s * normalizedLaplaceMoment F 2 s -
      2 * normalizedLaplaceMoment F 1 s ^ 3

/-- Fourth logarithmic derivative. -/
noncomputable def negativeLaplaceLogFourth
    (F : BoundedFabius) (s : ℝ) : ℝ :=
  normalizedLaplaceMoment F 4 s -
    4 * normalizedLaplaceMoment F 1 s * normalizedLaplaceMoment F 3 s -
    3 * normalizedLaplaceMoment F 2 s ^ 2 +
    12 * normalizedLaplaceMoment F 1 s ^ 2 * normalizedLaplaceMoment F 2 s -
    6 * normalizedLaplaceMoment F 1 s ^ 4

/-- Differential recurrence for normalized tilted moments. -/
theorem normalizedLaplaceMoment_hasDerivAt
    (F : BoundedFabius) (hF : IsFabius F) (k : ℕ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (normalizedLaplaceMoment F k)
      (-normalizedLaplaceMoment F (k + 1) s +
        normalizedLaplaceMoment F k s * normalizedLaplaceMoment F 1 s) s := by
  have h0 := (fabiusLaplaceMoment_zero_pos F hF hs).ne'
  unfold normalizedLaplaceMoment
  have hbase := (fabiusLaplaceMoment_hasDerivAt F hF k s).div
    (fabiusLaplaceMoment_hasDerivAt F hF 0 s) h0
  refine hbase.congr_deriv ?_
  field_simp [h0]
  ring

/-- First derivative of the exact logarithmic product. -/
theorem negativeLaplaceLog_hasDerivAt
    (F : BoundedFabius) (hF : IsFabius F) {s : ℝ} (hs : 0 < s) :
    HasDerivAt negativeLaplaceLog (negativeLaplaceLogFirst F s) s := by
  have h0 := (fabiusLaplaceMoment_zero_pos F hF hs).ne'
  have hlog := (fabiusLaplaceMoment_hasDerivAt F hF 0 s).log h0
  have heq : (fun x => Real.log (fabiusLaplaceMoment F 0 x)) =ᶠ[nhds s]
      negativeLaplaceLog := by
    filter_upwards [Ioi_mem_nhds hs] with x hx
    exact (negativeLaplaceLog_eq_log_laplaceMoment F hF hx).symm
  have h := hlog.congr_of_eventuallyEq heq.symm
  refine h.congr_deriv ?_
  simp [negativeLaplaceLogFirst, normalizedLaplaceMoment]
  ring

/-- The derivative of the first log derivative is the tilted variance. -/
theorem negativeLaplaceLogFirst_hasDerivAt
    (F : BoundedFabius) (hF : IsFabius F) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (negativeLaplaceLogFirst F) (negativeLaplaceLogSecond F s) s := by
  unfold negativeLaplaceLogFirst negativeLaplaceLogSecond
  have h := (normalizedLaplaceMoment_hasDerivAt F hF 1 hs).neg
  refine h.congr_deriv ?_
  ring

/-- The derivative of the tilted variance is the third log derivative. -/
theorem negativeLaplaceLogSecond_hasDerivAt
    (F : BoundedFabius) (hF : IsFabius F) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (negativeLaplaceLogSecond F) (negativeLaplaceLogThird F s) s := by
  unfold negativeLaplaceLogSecond negativeLaplaceLogThird
  have h1 := normalizedLaplaceMoment_hasDerivAt F hF 1 hs
  have h2 := normalizedLaplaceMoment_hasDerivAt F hF 2 hs
  have h := h2.sub (h1.pow 2)
  refine h.congr_deriv ?_
  ring

/-- The derivative of the third log derivative is the fourth one. -/
theorem negativeLaplaceLogThird_hasDerivAt
    (F : BoundedFabius) (hF : IsFabius F) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (negativeLaplaceLogThird F) (negativeLaplaceLogFourth F s) s := by
  unfold negativeLaplaceLogThird negativeLaplaceLogFourth
  have h1 := normalizedLaplaceMoment_hasDerivAt F hF 1 hs
  have h2 := normalizedLaplaceMoment_hasDerivAt F hF 2 hs
  have h3 := normalizedLaplaceMoment_hasDerivAt F hF 3 hs
  have h := h3.neg.add ((h1.mul h2).const_mul 3) |>.sub ((h1.pow 3).const_mul 2)
  have hc := h.congr_deriv (g' :=
      normalizedLaplaceMoment F 4 s -
        4 * normalizedLaplaceMoment F 1 s * normalizedLaplaceMoment F 3 s -
        3 * normalizedLaplaceMoment F 2 s ^ 2 +
        12 * normalizedLaplaceMoment F 1 s ^ 2 * normalizedLaplaceMoment F 2 s -
        6 * normalizedLaplaceMoment F 1 s ^ 4) (by ring)
  apply hc.congr_of_eventuallyEq
  filter_upwards with x
  simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply,
    Pi.pow_apply]
  ring

end Fabius
