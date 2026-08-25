import FabiusFunction.BromwichSaddle
import FabiusFunction.LaplaceTransform
import FabiusFunction.Monotonicity
import FabiusFunction.NegativeLaplaceVertical
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Exact Bromwich input for the Fabius function

This module discharges the analytic input hypotheses of the generic
quantitative saddle framework.  Exponentially tilting the bounded Fabius CDF
produces an integrable continuous Fourier input.  Its Fourier transform is the
negative generating function divided by the vertical Laplace coordinate.
The exact norm, exponential envelope, and ordinary/topological supports of
the tilted input are recorded independently for reuse.

The arbitrary-order vertical product bound from `NegativeLaplaceVertical`
then proves integrability of that transform.  Consequently Fourier inversion
gives both an exact Bromwich formula and its dimensionless saddle-coordinate
version, with no contour-shifting assumption.
-/

set_option autoImplicit false

open Filter Set MeasureTheory
open scoped FourierTransform

namespace Fabius

/-- The Fabius CDF after exponential tilting, as a complex-valued Fourier input. -/
noncomputable def fabiusExponentialTilt
    (F : BoundedFabius) (r x : ℝ) : ℂ :=
  QuantitativeSaddle.exponentialTilt (fun t => (fabiusReal F t : ℂ)) r x

/-- The exponentially tilted Fabius CDF is continuous. -/
theorem continuous_fabiusExponentialTilt
    (F : BoundedFabius) (hF : IsFabius F) (r : ℝ) :
    Continuous (fabiusExponentialTilt F r) := by
  unfold fabiusExponentialTilt QuantitativeSaddle.exponentialTilt
  apply Continuous.mul
  · fun_prop
  · exact Complex.continuous_ofReal.comp hF.contDiff.continuous

/-- Exact norm of the exponentially tilted Fabius CDF. -/
theorem norm_fabiusExponentialTilt_eq
    (F : BoundedFabius) (r x : ℝ) :
    ‖fabiusExponentialTilt F r x‖ =
      Real.exp (-r * x) * fabiusReal F x := by
  unfold fabiusExponentialTilt QuantitativeSaddle.exponentialTilt
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (fabiusReal_nonneg F x)]
  simp

/-- The tilted CDF is bounded pointwise by its exponential envelope. -/
theorem norm_fabiusExponentialTilt_le_exp_neg
    (F : BoundedFabius) (r x : ℝ) :
    ‖fabiusExponentialTilt F r x‖ ≤ Real.exp (-r * x) := by
  rw [norm_fabiusExponentialTilt_eq]
  exact mul_le_of_le_one_right (Real.exp_nonneg _)
    (fabiusReal_le_one F x)

/-- Exponential tilting preserves the exact ordinary support `(0, ∞)` of the
bounded Fabius CDF. -/
theorem support_fabiusExponentialTilt
    (F : BoundedFabius) (hF : IsFabius F) (r : ℝ) :
    Function.support (fabiusExponentialTilt F r) = Ioi (0 : ℝ) := by
  ext x
  change fabiusExponentialTilt F r x ≠ 0 ↔ 0 < x
  constructor
  · intro hx
    by_contra hxpos
    have hFx : fabiusReal F x = 0 :=
      hF.zero_of_nonpos x (le_of_not_gt hxpos)
    exact hx (by
      simp [fabiusExponentialTilt, QuantitativeSaddle.exponentialTilt, hFx])
  · intro hx
    unfold fabiusExponentialTilt QuantitativeSaddle.exponentialTilt
    exact mul_ne_zero (Complex.exp_ne_zero _)
      (Complex.ofReal_ne_zero.mpr (fabius_pos_of_pos F hF hx).ne')

/-- The topological support of the tilted CDF is the closed nonnegative
half-line. -/
theorem tsupport_fabiusExponentialTilt
    (F : BoundedFabius) (hF : IsFabius F) (r : ℝ) :
    tsupport (fabiusExponentialTilt F r) = Ici (0 : ℝ) := by
  have hts : tsupport (fabiusExponentialTilt F r) =
      closure (Function.support (fabiusExponentialTilt F r)) := rfl
  rw [hts, support_fabiusExponentialTilt F hF r, closure_Ioi]

/-- Compatibility subset form of `support_fabiusExponentialTilt`. -/
theorem support_fabiusExponentialTilt_subset
    (F : BoundedFabius) (hF : IsFabius F) (r : ℝ) :
    Function.support (fabiusExponentialTilt F r) ⊆ Ioi (0 : ℝ) := by
  rw [support_fabiusExponentialTilt F hF r]

/-- The exponentially tilted Fabius CDF is integrable for a positive tilt. -/
theorem integrable_fabiusExponentialTilt
    (F : BoundedFabius) (hF : IsFabius F) {r : ℝ} (hr : 0 < r) :
    Integrable (fabiusExponentialTilt F r) := by
  have hexp : IntegrableOn (fun x : ℝ => Real.exp ((-r) * x)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have hmeas : AEStronglyMeasurable (fabiusExponentialTilt F r)
      (volume.restrict (Ioi 0)) :=
    (continuous_fabiusExponentialTilt F hF r).aestronglyMeasurable
  have htail : IntegrableOn (fabiusExponentialTilt F r) (Ioi 0) := by
    apply hexp.mono' hmeas
    filter_upwards with x
    exact norm_fabiusExponentialTilt_le_exp_neg F r x
  have hindicator := htail.integrable_indicator measurableSet_Ioi
  have heq : (Ioi 0).indicator (fabiusExponentialTilt F r) =
      fabiusExponentialTilt F r := by
    funext x
    by_cases hx : 0 < x
    · simp [hx]
    · have hFx : fabiusReal F x = 0 := hF.zero_of_nonpos x (le_of_not_gt hx)
      simp [fabiusExponentialTilt, QuantitativeSaddle.exponentialTilt, hx, hFx]
  rw [heq] at hindicator
  exact hindicator

/-- Fourier transform of the tilted CDF, in exact Laplace coordinates. -/
theorem fourier_fabiusExponentialTilt
    (F : BoundedFabius) (hF : IsFabius F) {r : ℝ} (hr : 0 < r) (ξ : ℝ) :
    𝓕 (fabiusExponentialTilt F r) ξ =
      complexGeneratingFunction F (-((r : ℂ) + 2 * Real.pi * Complex.I * ξ)) /
        ((r : ℂ) + 2 * Real.pi * Complex.I * ξ) := by
  let z : ℂ := (r : ℂ) + 2 * Real.pi * Complex.I * ξ
  have hz : 0 < z.re := by
    dsimp [z]
    simp [hr]
  rw [Real.fourier_real_eq_integral_exp_smul]
  rw [complexGeneratingFunction_neg_div_eq_laplace F hF hz]
  rw [← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : 0 < x
  · have hx' : x ∈ Ioi (0 : ℝ) := hx
    simp only [Set.indicator, smul_eq_mul]
    rw [if_pos hx']
    unfold fabiusExponentialTilt QuantitativeSaddle.exponentialTilt
    dsimp [z]
    rw [← mul_assoc, ← Complex.exp_add]
    rw [mul_comm (Complex.exp _) (fabiusReal F x : ℂ)]
    congr 1
    push_cast
    ring_nf
  · have hFx : fabiusReal F x = 0 := hF.zero_of_nonpos x (le_of_not_gt hx)
    simp [Set.indicator, hx, fabiusExponentialTilt,
      QuantitativeSaddle.exponentialTilt, hFx]

/-- The Fourier transform of the tilted CDF is integrable. -/
theorem integrable_fourier_fabiusExponentialTilt
    (F : BoundedFabius) (hF : IsFabius F) {r : ℝ} (hr : 0 < r) :
    Integrable (𝓕 (fabiusExponentialTilt F r)) := by
  let a : ℝ := 2 * Real.pi / r
  have ha : a ≠ 0 := by
    dsimp [a]
    positivity
  have hk := (integrable_negativeLaplaceVerticalKernel F hF r hr).comp_mul_left' ha
  have hscaled : Integrable (fun ξ : ℝ =>
      (r : ℂ)⁻¹ * negativeLaplaceVerticalKernel F r (a * ξ)) :=
    hk.const_mul _
  refine hscaled.congr ?_
  filter_upwards with ξ
  rw [fourier_fabiusExponentialTilt F hF hr]
  unfold negativeLaplaceVerticalKernel
  dsimp [a]
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hden : 1 + (((2 * Real.pi / r) * ξ : ℝ) : ℂ) * Complex.I ≠ 0 := by
    intro hz
    have hre := congrArg Complex.re hz
    norm_num at hre
  have harg :
      (r : ℂ) * (1 + (((2 * Real.pi / r) * ξ : ℝ) : ℂ) * Complex.I) =
        (r : ℂ) + 2 * Real.pi * Complex.I * ξ := by
    push_cast
    field_simp
  rw [harg]
  have hfactor :
      (r : ℂ) + 2 * Real.pi * Complex.I * ξ =
        (r : ℂ) * (1 + Complex.I * (((2 * Real.pi * ξ / r : ℝ) : ℂ))) := by
    push_cast
    field_simp
  rw [hfactor]
  field_simp

/-- Exact Bromwich inversion formula for the bounded Fabius CDF. -/
theorem fabius_bromwich
    (F : BoundedFabius) (hF : IsFabius F) {r : ℝ} (hr : 0 < r) (x : ℝ) :
    (fabiusReal F x : ℂ) = Complex.exp (r * x) *
      ∫ ξ : ℝ,
        Complex.exp (2 * Real.pi * Complex.I * (ξ * x)) *
          (complexGeneratingFunction F
              (-((r : ℂ) + 2 * Real.pi * Complex.I * ξ)) /
            ((r : ℂ) + 2 * Real.pi * Complex.I * ξ)) := by
  exact QuantitativeSaddle.fourier_bromwich
    (fun t => (fabiusReal F t : ℂ)) r x
    (fun z => complexGeneratingFunction F (-z) / z)
    (continuous_fabiusExponentialTilt F hF r)
    (integrable_fabiusExponentialTilt F hF hr)
    (fourier_fabiusExponentialTilt F hF hr)
    (integrable_fourier_fabiusExponentialTilt F hF hr)

/-- Exact Fabius inversion in the dimensionless saddle coordinates used by
the quantitative extraction framework. -/
theorem fabius_bromwich_scaled
    (F : BoundedFabius) (hF : IsFabius F)
    {r b : ℝ} (hr : 0 < r) (hb : 0 < b) (x : ℝ) :
    (fabiusReal F x : ℂ) =
      Complex.exp (r * x) *
          complexGeneratingFunction F (-(r : ℂ)) /
          (Real.sqrt (2 * Real.pi * b) : ℂ) *
        ((Real.sqrt (2 * Real.pi) : ℂ)⁻¹ *
          ∫ v : ℝ,
            QuantitativeSaddle.scaledSaddleKernel
              (fun z => complexGeneratingFunction F (-z)) x r b v) := by
  have hPr : complexGeneratingFunction F (-(r : ℂ)) ≠ 0 := by
    rw [show -(r : ℂ) = ((-r : ℝ) : ℂ) by simp,
      complexGeneratingFunction_ofReal]
    exact Complex.ofReal_ne_zero.mpr
      (generatingFunction_neg_pos F hF r hr).ne'
  exact QuantitativeSaddle.fourier_bromwich_scaled
    (fun t => (fabiusReal F t : ℂ))
    (fun z => complexGeneratingFunction F (-z)) r b x hr hb hPr
    (continuous_fabiusExponentialTilt F hF r)
    (integrable_fabiusExponentialTilt F hF hr)
    (fourier_fabiusExponentialTilt F hF hr)
    (integrable_fourier_fabiusExponentialTilt F hF hr)

end Fabius
