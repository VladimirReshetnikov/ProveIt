import FabiusFunction.LaplaceMoments

/-!
# Derivatives of the negative-Laplace logarithm

This module expresses the first four logarithmic derivatives of the exact
negative-Laplace product in terms of normalized exponentially tilted moments.
If `M_k(s)` is the tilted `k`th moment and `R_k=M_k/M_0`, then

`R_k' = -R_(k+1) + R_k R_1`.

On the positive half-line, the successive derivatives of
`negativeLaplaceLog` are therefore the usual first four cumulant polynomials
in the `R_k`.  These formulas isolate the real saddle location, variance,
cubic correction, and fourth-order error needed by the quantitative
saddle-point argument.

The zeroth tilted moment is in fact positive at every real tilt.  Thus each
quotient `R_k` is globally smooth, and its differential recurrence holds on
the whole real line.  The positive-scale declarations are retained below as
compatibility interfaces because the logarithmic product itself still has a
separately proved positive-scale domain.
-/

set_option autoImplicit false

open scoped ContDiff

open Filter Set Topology

namespace Fabius

/-- A tilted moment normalized by the negative Laplace transform. -/
noncomputable def normalizedLaplaceMoment
    (F : BoundedFabius) (k : ℕ) (s : ℝ) : ℝ :=
  fabiusLaplaceMoment F k s / fabiusLaplaceMoment F 0 s

/-- The zeroth normalized tilted moment is one wherever its denominator does
not vanish. -/
theorem normalizedLaplaceMoment_zero_of_ne
    (F : BoundedFabius) {s : ℝ} (h0 : fabiusLaplaceMoment F 0 s ≠ 0) :
    normalizedLaplaceMoment F 0 s = 1 := by
  unfold normalizedLaplaceMoment
  exact div_self h0

/-- The zeroth normalized tilted moment is one at every real tilt, because
its globally positive denominator is also its numerator. -/
theorem normalizedLaplaceMoment_zero_all
    (F : BoundedFabius) (hF : IsFabius F) (s : ℝ) :
    normalizedLaplaceMoment F 0 s = 1 :=
  normalizedLaplaceMoment_zero_of_ne F
    (fabiusLaplaceMoment_zero_pos_all F hF s).ne'

/-- Positive-scale form of `normalizedLaplaceMoment_zero_of_ne`. -/
theorem normalizedLaplaceMoment_zero
    (F : BoundedFabius) (hF : IsFabius F) {s : ℝ} (hs : 0 < s) :
    normalizedLaplaceMoment F 0 s = 1 :=
  normalizedLaplaceMoment_zero_of_ne F
    (fabiusLaplaceMoment_zero_pos F hF hs).ne'

/-- Every normalized tilted moment is smooth on the whole real line: both
raw moments are smooth, and the globally positive zeroth moment never makes
the quotient singular. -/
theorem contDiff_normalizedLaplaceMoment
    (F : BoundedFabius) (hF : IsFabius F) (k : ℕ) :
    ContDiff ℝ ∞ (normalizedLaplaceMoment F k) := by
  change ContDiff ℝ ∞ (fun s : ℝ =>
    fabiusLaplaceMoment F k s / fabiusLaplaceMoment F 0 s)
  exact (contDiff_fabiusLaplaceMoment F hF k).div
    (contDiff_fabiusLaplaceMoment F hF 0)
    (fun s => (fabiusLaplaceMoment_zero_pos_all F hF s).ne')

/-- Every normalized tilted moment is continuous on the whole real line, as
a direct consequence of its global smoothness. -/
theorem continuous_normalizedLaplaceMoment
    (F : BoundedFabius) (hF : IsFabius F) (k : ℕ) :
    Continuous (normalizedLaplaceMoment F k) :=
  (contDiff_normalizedLaplaceMoment F hF k).continuous

/-- The exact logarithmic product is the logarithm of the negative Laplace
transform. -/
theorem negativeLaplaceLog_eq_log_laplaceMoment
    (F : BoundedFabius) (hF : IsFabius F) {s : ℝ} (hs : 0 < s) :
    negativeLaplaceLog s = Real.log (fabiusLaplaceMoment F 0 s) := by
  rw [fabiusLaplaceMoment_zero,
    ← exp_negativeLaplaceLog_eq_generatingFunction_neg F hF s hs,
    Real.log_exp]

/-- The first normalized cumulant; at positive scale it is the logarithmic
derivative of the negative Laplace transform. -/
noncomputable def negativeLaplaceLogFirst
    (F : BoundedFabius) (s : ℝ) : ℝ :=
  -normalizedLaplaceMoment F 1 s

/-- The second normalized cumulant, or tilted variance; at positive scale it
is the second logarithmic derivative of the negative Laplace transform. -/
noncomputable def negativeLaplaceLogSecond
    (F : BoundedFabius) (s : ℝ) : ℝ :=
  normalizedLaplaceMoment F 2 s - normalizedLaplaceMoment F 1 s ^ 2

/-- The third normalized cumulant; at positive scale it is the third
logarithmic derivative of the negative Laplace transform. -/
noncomputable def negativeLaplaceLogThird
    (F : BoundedFabius) (s : ℝ) : ℝ :=
  -normalizedLaplaceMoment F 3 s +
    3 * normalizedLaplaceMoment F 1 s * normalizedLaplaceMoment F 2 s -
      2 * normalizedLaplaceMoment F 1 s ^ 3

/-- The fourth normalized cumulant; at positive scale it is the fourth
logarithmic derivative of the negative Laplace transform. -/
noncomputable def negativeLaplaceLogFourth
    (F : BoundedFabius) (s : ℝ) : ℝ :=
  normalizedLaplaceMoment F 4 s -
    4 * normalizedLaplaceMoment F 1 s * normalizedLaplaceMoment F 3 s -
    3 * normalizedLaplaceMoment F 2 s ^ 2 +
    12 * normalizedLaplaceMoment F 1 s ^ 2 * normalizedLaplaceMoment F 2 s -
    6 * normalizedLaplaceMoment F 1 s ^ 4

/-- Differential recurrence for normalized tilted moments wherever the
normalizing zeroth moment is nonzero. -/
theorem normalizedLaplaceMoment_hasDerivAt_of_ne
    (F : BoundedFabius) (hF : IsFabius F) (k : ℕ) {s : ℝ}
    (h0 : fabiusLaplaceMoment F 0 s ≠ 0) :
    HasDerivAt (normalizedLaplaceMoment F k)
      (-normalizedLaplaceMoment F (k + 1) s +
        normalizedLaplaceMoment F k s * normalizedLaplaceMoment F 1 s) s := by
  unfold normalizedLaplaceMoment
  have hbase := (fabiusLaplaceMoment_hasDerivAt F hF k s).div
    (fabiusLaplaceMoment_hasDerivAt F hF 0 s) h0
  refine hbase.congr_deriv ?_
  field_simp [h0]
  ring

/-- The normalized-moment differential recurrence holds at every real tilt;
global positivity of the zeroth moment discharges the quotient rule's only
nonvanishing side condition. -/
theorem normalizedLaplaceMoment_hasDerivAt_all
    (F : BoundedFabius) (hF : IsFabius F) (k : ℕ) (s : ℝ) :
    HasDerivAt (normalizedLaplaceMoment F k)
      (-normalizedLaplaceMoment F (k + 1) s +
        normalizedLaplaceMoment F k s * normalizedLaplaceMoment F 1 s) s :=
  normalizedLaplaceMoment_hasDerivAt_of_ne F hF k
    (fabiusLaplaceMoment_zero_pos_all F hF s).ne'

/-- Positive-scale compatibility form of the normalized-moment differential
recurrence. -/
theorem normalizedLaplaceMoment_hasDerivAt
    (F : BoundedFabius) (hF : IsFabius F) (k : ℕ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (normalizedLaplaceMoment F k)
      (-normalizedLaplaceMoment F (k + 1) s +
        normalizedLaplaceMoment F k s * normalizedLaplaceMoment F 1 s) s :=
  normalizedLaplaceMoment_hasDerivAt_of_ne F hF k
    (fabiusLaplaceMoment_zero_pos F hF hs).ne'

/-- Normalized tilted moments are continuous on any set where the zeroth
moment does not vanish. -/
theorem continuousOn_normalizedLaplaceMoment_of_ne
    (F : BoundedFabius) (hF : IsFabius F) (k : ℕ) (S : Set ℝ)
    (hS : ∀ s ∈ S, fabiusLaplaceMoment F 0 s ≠ 0) :
    ContinuousOn (normalizedLaplaceMoment F k) S := by
  intro s hs
  exact (normalizedLaplaceMoment_hasDerivAt_of_ne F hF k
    (hS s hs)).continuousAt.continuousWithinAt

/-- Every normalized tilted moment is continuous on the positive half-line. -/
theorem continuousOn_normalizedLaplaceMoment
    (F : BoundedFabius) (hF : IsFabius F) (k : ℕ) :
    ContinuousOn (normalizedLaplaceMoment F k) (Ioi 0) :=
  (continuous_normalizedLaplaceMoment F hF k).continuousOn

/-- `deriv` form of the normalized-moment recurrence at every point where the
zeroth moment is nonzero. -/
theorem deriv_normalizedLaplaceMoment_of_ne
    (F : BoundedFabius) (hF : IsFabius F) (k : ℕ) {s : ℝ}
    (h0 : fabiusLaplaceMoment F 0 s ≠ 0) :
    deriv (normalizedLaplaceMoment F k) s =
      -normalizedLaplaceMoment F (k + 1) s +
        normalizedLaplaceMoment F k s * normalizedLaplaceMoment F 1 s :=
  (normalizedLaplaceMoment_hasDerivAt_of_ne F hF k h0).deriv

/-- The `deriv` form of the normalized-moment recurrence holds at every real
tilt. -/
theorem deriv_normalizedLaplaceMoment_all
    (F : BoundedFabius) (hF : IsFabius F) (k : ℕ) (s : ℝ) :
    deriv (normalizedLaplaceMoment F k) s =
      -normalizedLaplaceMoment F (k + 1) s +
        normalizedLaplaceMoment F k s * normalizedLaplaceMoment F 1 s :=
  (normalizedLaplaceMoment_hasDerivAt_all F hF k s).deriv

/-- Positive-scale compatibility form of `deriv_normalizedLaplaceMoment_of_ne`. -/
theorem deriv_normalizedLaplaceMoment
    (F : BoundedFabius) (hF : IsFabius F) (k : ℕ) {s : ℝ} (hs : 0 < s) :
    deriv (normalizedLaplaceMoment F k) s =
      -normalizedLaplaceMoment F (k + 1) s +
        normalizedLaplaceMoment F k s * normalizedLaplaceMoment F 1 s :=
  deriv_normalizedLaplaceMoment_of_ne F hF k
    (fabiusLaplaceMoment_zero_pos F hF hs).ne'

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
