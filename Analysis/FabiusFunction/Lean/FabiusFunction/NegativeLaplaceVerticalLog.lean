import FabiusFunction.NegativeLaplaceVertical
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# A logarithm of the vertical negative-Laplace transform

The dyadic product has no zero in the open right half-plane.  Consequently its restriction to
each vertical line has an unambiguous logarithm normalized to vanish at the real point.  We
construct that logarithm by integrating the logarithmic derivative, rather than selecting a
global branch of `Complex.log`, and prove that exponentiating it recovers the exact transform
ratio.  This is the branch-safe input needed by the central saddle expansion.
-/

set_option autoImplicit false

open Filter Set MeasureTheory
open scoped Interval

namespace Fabius

/-- A single negative-Laplace factor has no zero in the open right half-plane. -/
lemma negativeLaplaceComplexFactor_ne_zero {z : ℂ} (hz : 0 < z.re) :
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
    norm_num at hre
    linarith
  · exact neg_ne_zero.mpr hz0

/-- Every dyadically rescaled negative-Laplace factor is nonzero in the right half-plane. -/
lemma negativeLaplaceDyadicFactor_ne_zero {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    negativeLaplaceDyadicFactor z n ≠ 0 := by
  unfold negativeLaplaceDyadicFactor
  apply negativeLaplaceComplexFactor_ne_zero
  have ha : 0 < (2 : ℝ) ^ (n + 1) := by positivity
  have hpow : (2 : ℂ) ^ (n + 1) = (((2 : ℝ) ^ (n + 1) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hpow]
  let a : ℝ := (2 : ℝ) ^ (n + 1)
  have ha' : 0 < a := by dsimp [a]; positivity
  have hza : 0 < (z / (a : ℂ)).re := by
    rw [Complex.div_re]
    norm_num
    exact div_pos (mul_pos hz ha') (mul_pos ha' ha')
  simpa [a] using hza

/-- The entire generating function has no zero at the negative of a right-half-plane point. -/
theorem complexGeneratingFunction_neg_ne_zero
    (F : BoundedFabius) (hF : IsFabius F) {z : ℂ} (hz : 0 < z.re) :
    complexGeneratingFunction F (-z) ≠ 0 := by
  rw [complexGeneratingFunction_neg_eq_tprod F hF z]
  have h := tprod_one_add_ne_zero_of_summable
    (f := fun n : ℕ => negativeLaplaceDyadicFactor z n - 1)
    (fun n => by simpa using negativeLaplaceDyadicFactor_ne_zero hz n)
    (by simpa using (summable_negativeLaplaceDyadicFactor_sub_one z).norm)
  simpa using h

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

/-- The vertical curve is nonzero when its real coordinate is positive. -/
theorem negativeLaplaceVerticalCurve_ne_zero
    (F : BoundedFabius) (hF : IsFabius F) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    negativeLaplaceVerticalCurve F r θ ≠ 0 := by
  apply complexGeneratingFunction_neg_ne_zero F hF
  norm_num
  exact hr

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

/-- Continuity of the logarithmic derivative on a positive vertical line. -/
theorem continuous_negativeLaplaceVerticalLogDerivative
    (F : BoundedFabius) (hF : IsFabius F) {r : ℝ} (hr : 0 < r) :
    Continuous (negativeLaplaceVerticalLogDerivative F r) := by
  unfold negativeLaplaceVerticalLogDerivative
  exact ((contDiff_negativeLaplaceVerticalCurve F hF r).continuous_deriv (by simp)).div
    (contDiff_negativeLaplaceVerticalCurve F hF r).continuous
    (negativeLaplaceVerticalCurve_ne_zero F hF hr)

/-- Fundamental-theorem derivative of the normalized vertical logarithm. -/
theorem negativeLaplaceVerticalLog_hasDerivAt
    (F : BoundedFabius) (hF : IsFabius F) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    HasDerivAt (negativeLaplaceVerticalLog F r)
      (negativeLaplaceVerticalLogDerivative F r θ) θ := by
  unfold negativeLaplaceVerticalLog
  have hc := continuous_negativeLaplaceVerticalLogDerivative F hF hr
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 θ)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

@[simp] theorem negativeLaplaceVerticalLog_zero
    (F : BoundedFabius) (r : ℝ) :
    negativeLaplaceVerticalLog F r 0 = 0 := by
  simp [negativeLaplaceVerticalLog]

/-- Exponentiating the integrated logarithmic derivative recovers the exact vertical transform
ratio. -/
theorem exp_negativeLaplaceVerticalLog
    (F : BoundedFabius) (hF : IsFabius F) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
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
      ((negativeLaplaceVerticalLog_hasDerivAt F hF hr t).neg.cexp.differentiableAt)
  have hHderiv : ∀ t : ℝ, deriv H t = 0 := by
    intro t
    have hc := ((contDiff_negativeLaplaceVerticalCurve F hF r).differentiable
      (by simp) t).hasDerivAt
    have hl := negativeLaplaceVerticalLog_hasDerivAt F hF hr t
    have hp' : HasDerivAt H
        (deriv (negativeLaplaceVerticalCurve F r) t *
              Complex.exp (-negativeLaplaceVerticalLog F r t) +
            negativeLaplaceVerticalCurve F r t *
              (Complex.exp (-negativeLaplaceVerticalLog F r t) *
                (-negativeLaplaceVerticalLogDerivative F r t))) t := by
      convert! hc.mul hl.neg.cexp using 1
    rw [hp'.deriv]
    unfold negativeLaplaceVerticalLogDerivative
    field_simp [negativeLaplaceVerticalCurve_ne_zero F hF hr t]
    ring
  have hconst := is_const_of_deriv_eq_zero hHdiff hHderiv θ 0
  dsimp [H] at hconst
  simp only [negativeLaplaceVerticalLog_zero, neg_zero, Complex.exp_zero, mul_one] at hconst
  have hcurve0 := negativeLaplaceVerticalCurve_ne_zero F hF hr 0
  have hexp := Complex.exp_ne_zero (negativeLaplaceVerticalLog F r θ)
  rw [Complex.exp_neg] at hconst
  apply (eq_div_iff hcurve0).2
  field_simp [hexp] at hconst
  simpa [mul_comm] using hconst.symm

end Fabius
