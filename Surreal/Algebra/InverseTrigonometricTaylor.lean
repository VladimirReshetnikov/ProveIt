import Surreal.Algebra.AnalyticTaylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Explicit ordinary inverse-tangent Taylor coefficients

The ordinary derivative identity gives a formal differential equation.
Coefficient comparison determines all even and odd Taylor coefficients,
which can then be evaluated at actual surreal infinitesimals.
-/

namespace Surreal.Analytic

noncomputable section

/-- The inverse-tangent Taylor series satisfies its formal differential equation. -/
theorem taylorSeries_arctan_differential :
    (1 + PowerSeries.X ^ 2) * PowerSeries.derivative ℝ (taylorSeries Real.arctan 0) = 1 := by
  let p : ℝ → ℝ := (fun _ => 1) + id * id
  have hp : AnalyticAt ℝ p 0 := analyticAt_const.add (analyticAt_id.mul analyticAt_id)
  have ha : AnalyticAt ℝ Real.arctan 0 := Real.contDiff_arctan.contDiffAt.analyticAt
  have hps : taylorSeries p 0 = 1 + PowerSeries.X ^ 2 := by
    rw [taylorSeries_add analyticAt_const (analyticAt_id.mul analyticAt_id),
      taylorSeries_mul analyticAt_id analyticAt_id]
    simp [pow_two]
  have he : p * deriv Real.arctan = fun _ => (1 : ℝ) := by
    funext x
    change (1 + x * x) * deriv Real.arctan x = 1
    rw [Real.deriv_arctan]
    have hn : (1 + x ^ 2 : ℝ) ≠ 0 := by positivity
    field_simp
  rw [← hps, ← taylorSeries_deriv, ← taylorSeries_mul hp ha.deriv, he]
  simp

/-- The first inverse-tangent coefficient is one. -/
theorem coeff_taylorSeries_arctan_one : (taylorSeries Real.arctan 0).coeff 1 = 1 := by
  simp [coeff_taylorSeries, iteratedDeriv_succ, Real.deriv_arctan]

/-- The formal equation relates coefficients two degrees apart. -/
theorem coeff_taylorSeries_arctan_step (n : ℕ) :
    (taylorSeries Real.arctan 0).coeff (n + 2) * (n + 2 : ℝ) +
      (taylorSeries Real.arctan 0).coeff n * n = 0 := by
  have h := congrArg (fun p : PowerSeries ℝ => p.coeff (n + 1)) taylorSeries_arctan_differential
  rw [add_mul, one_mul, map_add, PowerSeries.coeff_X_pow_mul'] at h
  cases n with
  | zero => simpa [PowerSeries.coeff_derivative] using h
  | succ n =>
    simp only [show 2 ≤ n + 1 + 1 by omega, if_true,
      show n + 1 + 1 - 2 = n by omega, PowerSeries.coeff_derivative,
      PowerSeries.coeff_one, show n + 1 + 1 ≠ 0 by omega, if_false] at h
    convert h using 1
    push_cast
    ring

/-- Every even inverse-tangent Taylor coefficient vanishes. -/
theorem coeff_taylorSeries_arctan_even (n : ℕ) :
    (taylorSeries Real.arctan 0).coeff (2 * n) = 0 := by
  induction n with
  | zero => simp [coeff_taylorSeries]
  | succ n ih =>
    have h := coeff_taylorSeries_arctan_step (2 * n)
    rw [ih, zero_mul, add_zero] at h
    have hn : (2 * n + 2 : ℝ) ≠ 0 := by positivity
    simpa only [Nat.mul_add, Nat.mul_one] using (mul_eq_zero.mp h).resolve_right
      (by exact_mod_cast hn)

/-- The odd coefficients are the alternating reciprocal odd integers. -/
theorem coeff_taylorSeries_arctan_odd (n : ℕ) :
    (taylorSeries Real.arctan 0).coeff (2 * n + 1) = (-1 : ℝ) ^ n / (2 * n + 1) := by
  induction n with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, mul_zero, zero_add, div_one]
    exact coeff_taylorSeries_arctan_one
  | succ n ih =>
    have h := coeff_taylorSeries_arctan_step (2 * n + 1)
    rw [ih] at h
    have h₁ : (2 * n + 1 : ℝ) ≠ 0 := by positivity
    have h₃ : (2 * n + 3 : ℝ) ≠ 0 := by positivity
    have he : 2 * (n + 1) + 1 = 2 * n + 1 + 2 := by omega
    rw [he, pow_succ]
    push_cast at h ⊢
    field_simp at h ⊢
    nlinarith

/-- The complete coefficient formula, ready for an actual strongly summable evaluation. -/
theorem coeff_taylorSeries_arctan_zero (n : ℕ) :
    (taylorSeries Real.arctan 0).coeff n =
      if Even n then 0 else (-1 : ℝ) ^ (n / 2) / n := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [coeff_taylorSeries_arctan_even]
    simp
  · rw [coeff_taylorSeries_arctan_odd]
    simp [show (2 * k + 1) / 2 = k by omega]

end
end Surreal.Analytic
