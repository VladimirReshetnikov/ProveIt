import Surreal.Algebra.AnalyticTaylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Ordinary Taylor coefficients for the recentered trigonometric formulas

Mathlib's even and odd iterated derivatives identify the centered Taylor
series with the ordinary sine/cosine addition formulas. These are the
coefficient identities needed to connect `trigonometry:eq:sinfinite` and
`trigonometry:eq:cosfinite` to the general analytic lift.
-/

namespace Surreal.Analytic

/-- Cosine Taylor coefficients split into the even and odd series at zero. -/
theorem taylorSeries_real_cos (c : ℝ) :
    taylorSeries Real.cos c =
      PowerSeries.C (Real.cos c) * taylorSeries Real.cos 0 -
        PowerSeries.C (Real.sin c) * taylorSeries Real.sin 0 := by
  ext n
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · simp only [map_sub, PowerSeries.coeff_C_mul, coeff_taylorSeries,
      Real.iteratedDeriv_even_cos, Real.iteratedDeriv_even_sin,
      Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, Pi.one_apply, Real.cos_zero, Real.sin_zero]
    ring
  · simp only [map_sub, PowerSeries.coeff_C_mul, coeff_taylorSeries,
      Real.iteratedDeriv_odd_cos, Real.iteratedDeriv_odd_sin,
      Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, Pi.one_apply, Real.cos_zero, Real.sin_zero,
      pow_succ]
    ring

/-- Sine Taylor coefficients give the same ordinary-center decomposition. -/
theorem taylorSeries_real_sin (c : ℝ) :
    taylorSeries Real.sin c =
      PowerSeries.C (Real.sin c) * taylorSeries Real.cos 0 +
        PowerSeries.C (Real.cos c) * taylorSeries Real.sin 0 := by
  ext n
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · simp only [map_add, PowerSeries.coeff_C_mul, coeff_taylorSeries,
      Real.iteratedDeriv_even_cos, Real.iteratedDeriv_even_sin,
      Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, Pi.one_apply, Real.cos_zero, Real.sin_zero]
    ring
  · simp only [map_add, PowerSeries.coeff_C_mul, coeff_taylorSeries,
      Real.iteratedDeriv_odd_cos, Real.iteratedDeriv_odd_sin,
      Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, Pi.one_apply, Real.cos_zero, Real.sin_zero]
    ring

/-- The sine coefficients at zero are explicitly even-zero and odd-factorial. -/
theorem coeff_taylorSeries_sin_zero (n : ℕ) :
    (taylorSeries Real.sin 0).coeff n =
      if Even n then 0 else (-1 : ℝ) ^ (n / 2) / n.factorial := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · simp [coeff_taylorSeries, Real.iteratedDeriv_even_sin]
  · simp [coeff_taylorSeries, show (2 * k + 1) / 2 = k by omega]

/-- The cosine coefficients at zero are explicitly odd-zero and even-factorial. -/
theorem coeff_taylorSeries_cos_zero (n : ℕ) :
    (taylorSeries Real.cos 0).coeff n =
      if Even n then (-1 : ℝ) ^ (n / 2) / n.factorial else 0 := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · simp [coeff_taylorSeries, Real.iteratedDeriv_even_cos]
  · simp [coeff_taylorSeries]

end Surreal.Analytic
