import FabiusFunction.FabiusBromwichInput
import FabiusFunction.NegativeLaplaceDerivatives
import Mathlib.Analysis.Complex.Asymptotics

/-!
# From a normalized saddle integral to a logarithmic Fabius asymptotic

The exact Bromwich formula separates into a positive real saddle prefactor
and a normalized complex kernel integral.  This module records that separation
as the real quantity `fabiusSaddleRatio` and proves that its complexification
is exactly the kernel mass used by `QuantitativeSaddle`.  In particular, the
normalized kernel mass is real: its real part is the saddle ratio and its
imaginary part vanishes.

The final theorem is the algebraic/analytic reduction used by the sharp
asymptotic: if the normalized kernel mass is `1 + O(1 / b)` and `b → ∞`,
then

`log F(x) = r x + q(r) - log(2 π b) / 2 + O(1 / b)`.

Thus no positivity, Fourier-normalization, or logarithm manipulation remains
inside the later central-arc estimates.
-/

set_option autoImplicit false

open Filter MeasureTheory Asymptotics
open scoped Topology

namespace Fabius

/-- The normalized dimensionless kernel mass in the Fabius Bromwich formula. -/
noncomputable def fabiusSaddleKernelMass
    (F : BoundedFabius) (x r b : ℝ) : ℂ :=
  (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ *
    ∫ v : ℝ,
      QuantitativeSaddle.scaledSaddleKernel
        (fun z => complexGeneratingFunction F (-z)) x r b v

/-- The exact real ratio between `F(x)` and its saddle prefactor. -/
noncomputable def fabiusSaddleRatio
    (F : BoundedFabius) (x r b : ℝ) : ℝ :=
  fabiusReal F x * Real.sqrt (2 * Real.pi * b) /
    Real.exp (r * x + negativeLaplaceLog r)

/-- The real saddle ratio is exactly the normalized complex kernel mass. -/
theorem fabiusSaddleRatio_ofReal_eq_kernelMass
    (F : BoundedFabius) (hF : IsFabius F)
    {x r b : ℝ} (hr : 0 < r) (hb : 0 < b) :
    (fabiusSaddleRatio F x r b : ℂ) =
      fabiusSaddleKernelMass F x r b := by
  have hB := fabius_bromwich_scaled F hF hr hb x
  have hP : complexGeneratingFunction F (-(r : ℂ)) =
      (Real.exp (negativeLaplaceLog r) : ℂ) := by
    rw [show -(r : ℂ) = ((-r : ℝ) : ℂ) by simp,
      complexGeneratingFunction_ofReal,
      ← exp_negativeLaplaceLog_eq_generatingFunction_neg F hF r hr]
  rw [hP] at hB
  unfold fabiusSaddleRatio fabiusSaddleKernelMass
  push_cast
  rw [hB]
  have hsqrt : Real.sqrt (2 * Real.pi * b) ≠ 0 := by positivity
  have hsqrtC : (Real.sqrt (2 * Real.pi * b) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hsqrt
  have hexp : Real.exp (r * x + negativeLaplaceLog r) ≠ 0 := by positivity
  rw [Complex.ofReal_exp]
  rw [← Complex.exp_add]
  field_simp [hsqrtC]

/-- The real part of the normalized complex kernel mass is exactly the real
saddle ratio. -/
theorem fabiusSaddleKernelMass_re_eq_ratio
    (F : BoundedFabius) (hF : IsFabius F)
    {x r b : ℝ} (hr : 0 < r) (hb : 0 < b) :
    (fabiusSaddleKernelMass F x r b).re = fabiusSaddleRatio F x r b := by
  simpa using congrArg Complex.re
    (fabiusSaddleRatio_ofReal_eq_kernelMass F hF hr hb).symm

/-- The normalized complex kernel mass has zero imaginary part on the
positive saddle domain. -/
theorem fabiusSaddleKernelMass_im_eq_zero
    (F : BoundedFabius) (hF : IsFabius F)
    {x r b : ℝ} (hr : 0 < r) (hb : 0 < b) :
    (fabiusSaddleKernelMass F x r b).im = 0 := by
  simpa using congrArg Complex.im
    (fabiusSaddleRatio_ofReal_eq_kernelMass F hF hr hb).symm

/-- Positivity of the exact saddle ratio. -/
theorem fabiusSaddleRatio_pos
    (F : BoundedFabius) {x r b : ℝ}
    (hFx : 0 < fabiusReal F x) (hb : 0 < b) :
    0 < fabiusSaddleRatio F x r b := by
  unfold fabiusSaddleRatio
  exact div_pos (mul_pos hFx (by positivity)) (by positivity)

/-- Exact logarithm of the saddle ratio. -/
theorem log_fabiusSaddleRatio
    (F : BoundedFabius) {x r b : ℝ}
    (hFxpos : 0 < fabiusReal F x) (hb : 0 < b) :
    Real.log (fabiusSaddleRatio F x r b) =
      Real.log (fabiusReal F x) -
        (r * x + negativeLaplaceLog r - Real.log (2 * Real.pi * b) / 2) := by
  have hFx : fabiusReal F x ≠ 0 := hFxpos.ne'
  have hsqrt : Real.sqrt (2 * Real.pi * b) ≠ 0 := by positivity
  have hexp : Real.exp (r * x + negativeLaplaceLog r) ≠ 0 := by positivity
  unfold fabiusSaddleRatio
  rw [Real.log_div (mul_ne_zero hFx hsqrt) hexp,
    Real.log_mul hFx hsqrt, Real.log_exp,
    Real.log_sqrt (by positivity : 0 ≤ 2 * Real.pi * b)]
  ring

/-- A relative `O(1/b)` estimate for the normalized Fabius saddle integral
implies the corresponding logarithmic saddle formula. -/
theorem fabius_saddle_log_error_isBigO
    {α : Type*} (l : Filter α)
    (F : BoundedFabius) (hF : IsFabius F) (x r b : α → ℝ)
    (hr : ∀ᶠ i in l, 0 < r i)
    (hbpos : ∀ᶠ i in l, 0 < b i)
    (hbinfty : Tendsto b l atTop)
    (hFxpos : ∀ᶠ i in l, 0 < fabiusReal F (x i))
    (hrelative :
      (fun i => fabiusSaddleKernelMass F (x i) (r i) (b i) - 1) =O[l]
        (fun i => (b i)⁻¹)) :
    (fun i => Real.log (fabiusReal F (x i)) -
      (r i * x i + negativeLaplaceLog (r i) -
        Real.log (2 * Real.pi * b i) / 2)) =O[l]
      (fun i => (b i)⁻¹) := by
  have hratioComplex :
      (fun i => ((fabiusSaddleRatio F (x i) (r i) (b i) - 1 : ℝ) : ℂ)) =O[l]
        (fun i => (b i)⁻¹) := by
    apply hrelative.congr'
    · filter_upwards [hr, hbpos] with i hri hbi
      rw [← fabiusSaddleRatio_ofReal_eq_kernelMass F hF hri hbi]
      push_cast
      rfl
    · exact Filter.EventuallyEq.rfl
  have hratio :
      (fun i => fabiusSaddleRatio F (x i) (r i) (b i) - 1) =O[l]
        (fun i => (b i)⁻¹) := by
    exact Complex.isBigO_ofReal_left.mp hratioComplex
  have hlog := QuantitativeSaddle.real_log_of_relative_error_isBigO_inv
    l b (fun i => fabiusSaddleRatio F (x i) (r i) (b i)) hbinfty hratio
  exact hlog.congr'
    (by
      filter_upwards [hFxpos, hbpos] with i hFxi hbi
      rw [log_fabiusSaddleRatio F hFxi hbi])
    Filter.EventuallyEq.rfl

end Fabius
