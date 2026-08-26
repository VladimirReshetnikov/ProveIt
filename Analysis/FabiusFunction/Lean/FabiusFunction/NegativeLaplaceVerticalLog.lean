import FabiusFunction.NegativeLaplaceVertical
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# A logarithm of the vertical negative-Laplace transform

The dyadic product has no zero off the imaginary axis, and the associated vertical curve is
nonzero for every real radial parameter, including the degenerate line at `r = 0`.
Consequently each vertical line has an unambiguous logarithm normalized to vanish at the real
point.  We construct that logarithm by integrating the logarithmic derivative, rather than
selecting a global branch of `Complex.log`, and prove that exponentiating it recovers the exact
transform ratio for every real `r`.  This is the branch-safe input needed by the central saddle
expansion.
-/

set_option autoImplicit false

open Filter Set MeasureTheory
open scoped Interval

namespace Fabius

/-- A single negative-Laplace factor is nonzero off the imaginary axis. -/
lemma negativeLaplaceComplexFactor_ne_zero_of_re_ne_zero
    {z : ℂ} (hz : z.re ≠ 0) :
    negativeLaplaceComplexFactor z ≠ 0 := by
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    norm_num at hz
  rw [negativeLaplaceComplexFactor, complexExpm1Div_of_ne (neg_ne_zero.mpr hz0)]
  apply div_ne_zero
  · intro hnum
    have hexp : Complex.exp (-z) = 1 := sub_eq_zero.mp hnum
    have hnorm := congrArg norm hexp
    rw [Complex.norm_exp, norm_one] at hnorm
    have hre : (-z).re = 0 := (Real.exp_eq_one_iff _).mp hnorm
    apply hz
    norm_num at hre
    linarith
  · exact neg_ne_zero.mpr hz0

/-- A single negative-Laplace factor has no zero in the open right half-plane. -/
lemma negativeLaplaceComplexFactor_ne_zero {z : ℂ} (hz : 0 < z.re) :
    negativeLaplaceComplexFactor z ≠ 0 := by
  exact negativeLaplaceComplexFactor_ne_zero_of_re_ne_zero hz.ne'

/-- Every dyadically rescaled negative-Laplace factor is nonzero off the
imaginary axis. -/
lemma negativeLaplaceDyadicFactor_ne_zero_of_re_ne_zero
    {z : ℂ} (hz : z.re ≠ 0) (n : ℕ) :
    negativeLaplaceDyadicFactor z n ≠ 0 := by
  unfold negativeLaplaceDyadicFactor
  apply negativeLaplaceComplexFactor_ne_zero_of_re_ne_zero
  have ha : 0 < (2 : ℝ) ^ (n + 1) := by positivity
  have hpow : (2 : ℂ) ^ (n + 1) = (((2 : ℝ) ^ (n + 1) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hpow]
  let a : ℝ := (2 : ℝ) ^ (n + 1)
  have ha' : 0 < a := by dsimp [a]; positivity
  have hza : (z / (a : ℂ)).re ≠ 0 := by
    rw [Complex.div_re]
    norm_num
    exact ⟨hz, ha'.ne'⟩
  simpa [a] using hza

/-- Every dyadically rescaled negative-Laplace factor is nonzero in the right half-plane. -/
lemma negativeLaplaceDyadicFactor_ne_zero {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    negativeLaplaceDyadicFactor z n ≠ 0 := by
  exact negativeLaplaceDyadicFactor_ne_zero_of_re_ne_zero hz.ne' n

/-- The entire generating function is nonzero at the negative of every point
off the imaginary axis. -/
theorem complexGeneratingFunction_neg_ne_zero_of_re_ne_zero
    (F : BoundedFabius) (hF : IsFabius F) {z : ℂ} (hz : z.re ≠ 0) :
    complexGeneratingFunction F (-z) ≠ 0 := by
  rw [complexGeneratingFunction_neg_eq_tprod F hF z]
  have h := tprod_one_add_ne_zero_of_summable
    (f := fun n : ℕ => negativeLaplaceDyadicFactor z n - 1)
    (fun n => by
      simpa using negativeLaplaceDyadicFactor_ne_zero_of_re_ne_zero hz n)
    (by simpa using (summable_negativeLaplaceDyadicFactor_sub_one z).norm)
  simpa using h

/-- The entire generating function has no zero at the negative of a right-half-plane point. -/
theorem complexGeneratingFunction_neg_ne_zero
    (F : BoundedFabius) (hF : IsFabius F) {z : ℂ} (hz : 0 < z.re) :
    complexGeneratingFunction F (-z) ≠ 0 := by
  exact complexGeneratingFunction_neg_ne_zero_of_re_ne_zero F hF hz.ne'

/-- The complex generating function is nonzero off the imaginary axis. -/
theorem complexGeneratingFunction_ne_zero_of_re_ne_zero
    (F : BoundedFabius) (hF : IsFabius F) {z : ℂ} (hz : z.re ≠ 0) :
    complexGeneratingFunction F z ≠ 0 := by
  have hneg : (-z).re ≠ 0 := by simpa using hz
  simpa using
    (complexGeneratingFunction_neg_ne_zero_of_re_ne_zero F hF hneg)

/-- The complex exponential generating function is entire. -/
theorem differentiable_complexGeneratingFunction
    (F : BoundedFabius) (hF : IsFabius F) :
    Differentiable ℂ (complexGeneratingFunction F) := by
  have heq : complexGeneratingFunction F = fun z : ℂ =>
      Complex.exp (z / 2) *
        rvachevFourier F (Complex.I * z / (4 * Real.pi)) := by
    funext z
    exact complexGeneratingFunction_eq_fourier_analytic F hF z
  rw [heq]
  have hrv := rvachevFourier_differentiable_analytic F hF
  fun_prop

/-- Smoothness, to every complex order, of the exponential generating function. -/
theorem contDiff_complexGeneratingFunction
    (F : BoundedFabius) (hF : IsFabius F) :
    ContDiff ℂ ⊤ (complexGeneratingFunction F) :=
  (differentiable_complexGeneratingFunction F hF).contDiff

/-- Restriction of the negative-Laplace transform to the vertical line through `r`. -/
noncomputable def negativeLaplaceVerticalCurve
    (F : BoundedFabius) (r θ : ℝ) : ℂ :=
  complexGeneratingFunction F (-((r : ℂ) * (1 + (θ : ℂ) * Complex.I)))

/-- The vertical negative-Laplace curve is nonzero for every real radial
parameter, including the constant curve at `r = 0`. -/
theorem negativeLaplaceVerticalCurve_ne_zero_all
    (F : BoundedFabius) (hF : IsFabius F) (r θ : ℝ) :
    negativeLaplaceVerticalCurve F r θ ≠ 0 := by
  by_cases hr : r = 0
  · subst r
    simp [negativeLaplaceVerticalCurve, complexGeneratingFunction]
  · apply complexGeneratingFunction_neg_ne_zero_of_re_ne_zero F hF
    norm_num
    exact hr

set_option linter.unusedVariables false in
/-- Positive-coordinate compatibility form of
`negativeLaplaceVerticalCurve_ne_zero_all`.  The hypothesis `hr` is retained
for API compatibility; the curve is nonzero for every real `r`. -/
theorem negativeLaplaceVerticalCurve_ne_zero
    (F : BoundedFabius) (hF : IsFabius F) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    negativeLaplaceVerticalCurve F r θ ≠ 0 := by
  exact negativeLaplaceVerticalCurve_ne_zero_all F hF r θ

/-- The vertical curve is real analytic in the vertical parameter.  The
smoothness exponent is the top element of `WithTop ℕ∞`, which in this Mathlib
is the *analytic* exponent `ω` rather than `C^∞`: the curve is an entire
generating function composed with an affine map, so analyticity, not merely
infinite differentiability, is what is proved here. -/
theorem contDiff_negativeLaplaceVerticalCurve
    (F : BoundedFabius) (hF : IsFabius F) (r : ℝ) :
    ContDiff ℝ ⊤ (negativeLaplaceVerticalCurve F r) := by
  unfold negativeLaplaceVerticalCurve
  have hθ : ContDiff ℝ ⊤ (fun θ : ℝ => (θ : ℂ)) := Complex.ofRealCLM.contDiff
  exact ((contDiff_complexGeneratingFunction F hF).restrict_scalars ℝ).comp
    (by
      exact (contDiff_const.mul
        (contDiff_const.add (hθ.mul contDiff_const))).neg)

/-- Logarithmic derivative of the vertical negative-Laplace curve. -/
noncomputable def negativeLaplaceVerticalLogDerivative
    (F : BoundedFabius) (r θ : ℝ) : ℂ :=
  deriv (negativeLaplaceVerticalCurve F r) θ /
    negativeLaplaceVerticalCurve F r θ

/-- Branch-safe vertical logarithm, normalized to vanish at `θ = 0`. -/
noncomputable def negativeLaplaceVerticalLog
    (F : BoundedFabius) (r θ : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..θ, negativeLaplaceVerticalLogDerivative F r t

/-- The logarithmic derivative is continuous on every real vertical line. -/
theorem continuous_negativeLaplaceVerticalLogDerivative_all
    (F : BoundedFabius) (hF : IsFabius F) (r : ℝ) :
    Continuous (negativeLaplaceVerticalLogDerivative F r) := by
  unfold negativeLaplaceVerticalLogDerivative
  exact ((contDiff_negativeLaplaceVerticalCurve F hF r).continuous_deriv (by simp)).div
    (contDiff_negativeLaplaceVerticalCurve F hF r).continuous
    (negativeLaplaceVerticalCurve_ne_zero_all F hF r)

set_option linter.unusedVariables false in
/-- Positive-line compatibility form of
`continuous_negativeLaplaceVerticalLogDerivative_all`.  The hypothesis `hr`
is retained for API compatibility; continuity holds for every real `r`. -/
theorem continuous_negativeLaplaceVerticalLogDerivative
    (F : BoundedFabius) (hF : IsFabius F) {r : ℝ} (hr : 0 < r) :
    Continuous (negativeLaplaceVerticalLogDerivative F r) := by
  exact continuous_negativeLaplaceVerticalLogDerivative_all F hF r

/-- On every real vertical line, the normalized logarithm has derivative equal
to the logarithmic derivative of the vertical curve. -/
theorem negativeLaplaceVerticalLog_hasDerivAt_all
    (F : BoundedFabius) (hF : IsFabius F) (r θ : ℝ) :
    HasDerivAt (negativeLaplaceVerticalLog F r)
      (negativeLaplaceVerticalLogDerivative F r θ) θ := by
  unfold negativeLaplaceVerticalLog
  have hc := continuous_negativeLaplaceVerticalLogDerivative_all F hF r
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 θ)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

set_option linter.unusedVariables false in
/-- Positive-line compatibility form of
`negativeLaplaceVerticalLog_hasDerivAt_all`.  The hypothesis `hr` is retained
for API compatibility; the derivative identity holds for every real `r`. -/
theorem negativeLaplaceVerticalLog_hasDerivAt
    (F : BoundedFabius) (hF : IsFabius F) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    HasDerivAt (negativeLaplaceVerticalLog F r)
      (negativeLaplaceVerticalLogDerivative F r θ) θ := by
  exact negativeLaplaceVerticalLog_hasDerivAt_all F hF r θ

/-- The normalized vertical logarithm vanishes at its base point `θ = 0`. -/
@[simp] theorem negativeLaplaceVerticalLog_zero
    (F : BoundedFabius) (r : ℝ) :
    negativeLaplaceVerticalLog F r 0 = 0 := by
  simp [negativeLaplaceVerticalLog]

/-- For every real radial parameter, exponentiating the integrated logarithmic
derivative recovers the exact vertical-transform ratio. -/
theorem exp_negativeLaplaceVerticalLog_all
    (F : BoundedFabius) (hF : IsFabius F) (r θ : ℝ) :
    Complex.exp (negativeLaplaceVerticalLog F r θ) =
      negativeLaplaceVerticalCurve F r θ /
        negativeLaplaceVerticalCurve F r 0 := by
  let H : ℝ → ℂ := fun t =>
    negativeLaplaceVerticalCurve F r t *
      Complex.exp (-negativeLaplaceVerticalLog F r t)
  have hHdiff : Differentiable ℝ H := by
    intro t
    dsimp [H]
    exact ((contDiff_negativeLaplaceVerticalCurve F hF r).differentiable (by simp) t).mul
      ((negativeLaplaceVerticalLog_hasDerivAt_all F hF r t).neg.cexp.differentiableAt)
  have hHderiv : ∀ t : ℝ, deriv H t = 0 := by
    intro t
    have hc := ((contDiff_negativeLaplaceVerticalCurve F hF r).differentiable
      (by simp) t).hasDerivAt
    have hl := negativeLaplaceVerticalLog_hasDerivAt_all F hF r t
    have hp' : HasDerivAt H
        (deriv (negativeLaplaceVerticalCurve F r) t *
              Complex.exp (-negativeLaplaceVerticalLog F r t) +
            negativeLaplaceVerticalCurve F r t *
              (Complex.exp (-negativeLaplaceVerticalLog F r t) *
                (-negativeLaplaceVerticalLogDerivative F r t))) t := by
      convert! hc.mul hl.neg.cexp using 1
    rw [hp'.deriv]
    unfold negativeLaplaceVerticalLogDerivative
    field_simp [negativeLaplaceVerticalCurve_ne_zero_all F hF r t]
    ring
  have hconst := is_const_of_deriv_eq_zero hHdiff hHderiv θ 0
  dsimp [H] at hconst
  simp only [negativeLaplaceVerticalLog_zero, neg_zero, Complex.exp_zero, mul_one] at hconst
  have hcurve0 := negativeLaplaceVerticalCurve_ne_zero_all F hF r 0
  have hexp := Complex.exp_ne_zero (negativeLaplaceVerticalLog F r θ)
  rw [Complex.exp_neg] at hconst
  apply (eq_div_iff hcurve0).2
  field_simp [hexp] at hconst
  simpa [mul_comm] using hconst.symm

set_option linter.unusedVariables false in
/-- Positive-line compatibility form of `exp_negativeLaplaceVerticalLog_all`.
The hypothesis `hr` is retained for API compatibility; exponential recovery
holds for every real `r`. -/
theorem exp_negativeLaplaceVerticalLog
    (F : BoundedFabius) (hF : IsFabius F) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    Complex.exp (negativeLaplaceVerticalLog F r θ) =
      negativeLaplaceVerticalCurve F r θ /
        negativeLaplaceVerticalCurve F r 0 := by
  exact exp_negativeLaplaceVerticalLog_all F hF r θ

end Fabius
