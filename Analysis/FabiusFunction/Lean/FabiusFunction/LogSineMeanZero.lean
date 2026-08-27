import Mathlib.Analysis.SpecialFunctions.Integrals.LogTrigonometric
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic

/-!
# The doubling cocycle is centered: `∫₀¹ log (2 sin πt) dt = 0`

The exact input behind the *typical* row of the Fourier-decay
spectrum: the geometric-mean scale of the dyadic sine product is
`Λ₀ = exp (∫₀¹ log |sin πt| dt) = 1/2`, equivalently the cocycle
`ψ(t) = log (2 sin πt)` of `DoublingCocycleIdentities` has Lebesgue
mean zero.  By Birkhoff's theorem this is what makes the
almost-everywhere decay exponent equal to
`κ₀ = 3/2 + log₂ π`, and it is the centering used throughout the
fluctuation theory (variance `π²/4`, corrected LIL).

* `intervalIntegrable_log_sin_pi_mul` — integrability of
  `t ↦ log (sin πt)` on `[0,1]` (the singularities at the endpoints
  are logarithmic).
* `integral_log_sin_pi_mul` — `∫₀¹ log (sin πt) dt = -log 2`
  (the classical Euler log-sine value in the audit's normalization).
* `integral_log_two_sin_pi_mul` — `∫₀¹ log (2 sin πt) dt = 0`.
-/

set_option autoImplicit false

open intervalIntegral Real MeasureTheory

namespace Fabius

/-- `t ↦ log (sin (πt))` is interval integrable on `[0,1]`. -/
theorem intervalIntegrable_log_sin_pi_mul :
    IntervalIntegrable (fun t => Real.log (Real.sin (π * t)))
      MeasureTheory.volume 0 1 := by
  have h : IntervalIntegrable (fun x => (Real.log ∘ Real.sin) (π * x))
      MeasureTheory.volume (0 / π) (π / π) :=
    (intervalIntegrable_log_sin (a := (0:ℝ)) (b := π)).comp_mul_left
  simp only [Function.comp_def] at h
  simpa [zero_div, div_self Real.pi_ne_zero] using h

/-- **Euler's log-sine integral in shell normalization**:
`∫₀¹ log (sin πt) dt = -log 2`. -/
theorem integral_log_sin_pi_mul :
    ∫ t in (0:ℝ)..1, Real.log (Real.sin (π * t)) = -Real.log 2 := by
  have h := intervalIntegral.integral_comp_mul_left
    (a := (0:ℝ)) (b := 1) (f := fun x => Real.log (Real.sin x))
    (c := π) Real.pi_ne_zero
  simp only [mul_zero, mul_one] at h
  rw [h, integral_log_sin_zero_pi, smul_eq_mul]
  field_simp

/-- **The doubling cocycle is centered**:
`∫₀¹ log (2 sin πt) dt = 0` — the geometric-mean scale of the dyadic
sine product is exactly `1/2`, forcing the typical decay exponent
`κ₀`. -/
theorem integral_log_two_sin_pi_mul :
    ∫ t in (0:ℝ)..1, Real.log (2 * Real.sin (π * t)) = 0 := by
  have hsplit : ∫ t in (0:ℝ)..1, Real.log (2 * Real.sin (π * t)) =
      ∫ t in (0:ℝ)..1, (Real.log 2 + Real.log (Real.sin (π * t))) := by
    apply intervalIntegral.integral_congr_ae
    have h0ae : ∀ᵐ t : ℝ, t ≠ 0 := by
      rw [MeasureTheory.ae_iff]
      simp
    have h1ae : ∀ᵐ t : ℝ, t ≠ 1 := by
      rw [MeasureTheory.ae_iff]
      simp
    filter_upwards [h0ae, h1ae] with t ht0 ht1 hmem
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hmem
    have htpos : 0 < t := lt_of_le_of_ne hmem.1.le (Ne.symm ht0)
    have htlt : t < 1 := lt_of_le_of_ne hmem.2 ht1
    have hs : 0 < Real.sin (π * t) := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · positivity
      · nlinarith [Real.pi_pos]
    rw [Real.log_mul two_ne_zero (ne_of_gt hs)]
  rw [hsplit,
    intervalIntegral.integral_add intervalIntegrable_const
      intervalIntegrable_log_sin_pi_mul,
    intervalIntegral.integral_const, integral_log_sin_pi_mul, smul_eq_mul]
  ring

end Fabius
