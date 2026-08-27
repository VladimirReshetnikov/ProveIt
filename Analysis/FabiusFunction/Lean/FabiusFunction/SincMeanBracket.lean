import FabiusFunction.SharpGelfondBound

/-!
# The two-sided elementary bracket for the mean of the dyadic sine product

Combining the sharp Gelfond bound of `SharpGelfondBound` with the exact
`L²` identity of `LacunaryRieszIntegral` brackets the `L¹` mean
`I₁(n) = ∫₀¹ ∏_{j<n} |sin (π 2ʲ t)| dt` between two explicit geometric
sequences:

* lower (`le_mul_integral_prod_abs_sin_two_pow`, already in
  `GelfondLogisticBound`): `I₁(n) ≥ √(3/5)·3^{-n/2}` — the source of
  `ϱ₁ ≥ 3^{-1/2} > 1/2` and hence of the singularity of the
  transfer-operator eigenmeasure;
* upper (`integral_prod_abs_sin_two_pow_le`, this file):
  `I₁(n+1) ≤ (√3/2)ⁿ` — the integral cannot beat the sharp sup bound.

Together: `3^{-1/2} ≤ liminf I₁(n)^{1/n} ≤ limsup I₁(n)^{1/n} ≤ √3/2`,
the audit's elementary two-sided estimate for the Perron root
`ϱ₁ = 0.661322…` (true value strictly inside the bracket).
-/

set_option autoImplicit false

open Finset intervalIntegral Real

namespace Fabius

/-- **Sharp upper bound for the mean**: with `n+1` factors,
`∫₀¹ ∏_{j≤n} |sin (π 2ʲ t)| dt ≤ (√3/2)ⁿ` — the audit's
`I₁(n) ≤ ‖Pₙ‖_∞ ≤ (√3/2)^{n-1}`. -/
theorem integral_prod_abs_sin_two_pow_le (n : ℕ) :
    ∫ t in (0:ℝ)..1, ∏ j ∈ range (n + 1), |Real.sin (π * 2 ^ j * t)| ≤
      (Real.sqrt 3 / 2) ^ n := by
  have hQcont : Continuous fun t : ℝ =>
      ∏ j ∈ range (n + 1), |Real.sin (π * 2 ^ j * t)| := by
    refine continuous_finsetProd _ fun j _ => ?_
    fun_prop
  have hpoint : ∀ t ∈ Set.Icc (0:ℝ) 1,
      ∏ j ∈ range (n + 1), |Real.sin (π * 2 ^ j * t)| ≤
        (Real.sqrt 3 / 2) ^ n := fun t _ =>
    abs_prod_sin_two_pow_le_sharp t n
  have hmono := intervalIntegral.integral_mono_on
    (μ := MeasureTheory.volume) (by norm_num : (0:ℝ) ≤ 1)
    (hQcont.intervalIntegrable 0 1)
    (intervalIntegrable_const)
    hpoint
  calc ∫ t in (0:ℝ)..1, ∏ j ∈ range (n + 1), |Real.sin (π * 2 ^ j * t)|
      ≤ ∫ _t in (0:ℝ)..1, (Real.sqrt 3 / 2) ^ n := hmono
    _ = (Real.sqrt 3 / 2) ^ n := by simp

end Fabius
