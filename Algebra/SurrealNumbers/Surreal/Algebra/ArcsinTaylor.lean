import Surreal.Algebra.AnalyticTaylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Explicit ordinary inverse-sine Taylor coefficients

The analytic inverse satisfies `(1-X^2) A'' = X A'`. Coefficient comparison
and Mathlib's central-binomial recurrence determine every coefficient.
These identities supply the strong series in `trigonometry:eq:smallseries`
and the endpoint expansion in `trigonometry:eq:acosseries`.
-/

namespace Surreal.Analytic

open Filter Topology

noncomputable section

private theorem arcsin_derivative_equation (r : ℝ) (hr : r ∈ Set.Ioo (-1) 1) :
    (1 - r ^ 2) * deriv (deriv Real.arcsin) r = r * deriv Real.arcsin r := by
  have hp : 0 < 1 - r ^ 2 := by nlinarith [hr.1, hr.2]
  have hs := Real.sqrt_pos.mpr hp
  have hsq := Real.sq_sqrt hp.le
  have hg : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-2 * r) r := by
    simpa using ((hasDerivAt_id r).pow 2).const_sub 1
  have he : HasDerivAt (deriv Real.arcsin)
      (-((-2 * r) / (2 * Real.sqrt (1 - r ^ 2))) / Real.sqrt (1 - r ^ 2) ^ 2) r := by
    convert (hg.sqrt hp.ne').inv hs.ne' using 1 <;>
      first | rfl | (funext y; simp [Real.deriv_arcsin])
  rw [he.deriv, Real.deriv_arcsin]
  field_simp
  linear_combination -r * hsq

/-- The formal Taylor series of inverse sine obeys its ordinary differential equation. -/
theorem taylorSeries_arcsin_differential :
    (1 - PowerSeries.X ^ 2) *
        PowerSeries.derivative ℝ (PowerSeries.derivative ℝ (taylorSeries Real.arcsin 0)) =
      PowerSeries.X * PowerSeries.derivative ℝ (taylorSeries Real.arcsin 0) := by
  let p : ℝ → ℝ := (fun _ => 1) - id * id
  have hp : AnalyticAt ℝ p 0 := analyticAt_const.sub (analyticAt_id.mul analyticAt_id)
  have ha : AnalyticAt ℝ Real.arcsin 0 := (Real.contDiffAt_arcsin (by norm_num) (by norm_num)).analyticAt
  have hps : taylorSeries p 0 = 1 - PowerSeries.X ^ 2 := by
    change taylorSeries ((fun _ : ℝ => 1) + -(id * id)) 0 = _
    rw [taylorSeries_add analyticAt_const (analyticAt_id.mul analyticAt_id).neg,
      taylorSeries_neg, taylorSeries_mul analyticAt_id analyticAt_id]
    simp [pow_two, sub_eq_add_neg]
  have he : p * deriv (deriv Real.arcsin) =ᶠ[𝓝 (0 : ℝ)] id * deriv Real.arcsin := by
    filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num) (show (0 : ℝ) < 1 by norm_num)]
      with r hr
    change (1 - r * r) * deriv (deriv Real.arcsin) r = r * deriv Real.arcsin r
    simpa only [pow_two] using arcsin_derivative_equation r hr
  rw [← hps, ← taylorSeries_deriv, ← taylorSeries_deriv,
    ← taylorSeries_mul hp ha.deriv.deriv, taylorSeries_congr he,
    taylorSeries_mul analyticAt_id ha.deriv, taylorSeries_id, taylorSeries_deriv]
  simp

/-- The first inverse-sine coefficient is one. -/
theorem coeff_taylorSeries_arcsin_one : (taylorSeries Real.arcsin 0).coeff 1 = 1 := by
  simp [coeff_taylorSeries, iteratedDeriv_succ, Real.deriv_arcsin]

/-- The differential equation gives a two-degree recurrence for inverse-sine coefficients. -/
theorem coeff_taylorSeries_arcsin_step (n : ℕ) :
    (taylorSeries Real.arcsin 0).coeff (n + 2) * (n + 2 : ℝ) * (n + 1) =
      (taylorSeries Real.arcsin 0).coeff n * n ^ 2 := by
  have h := congrArg (fun p : PowerSeries ℝ => p.coeff n) taylorSeries_arcsin_differential
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_X_pow_mul'] at h
  rw [show (PowerSeries.X : PowerSeries ℝ) = PowerSeries.X ^ 1 by simp,
    PowerSeries.coeff_X_pow_mul'] at h
  rcases n with _ | _ | n
  · simpa [PowerSeries.coeff_derivative] using h
  · norm_num [PowerSeries.coeff_derivative] at h ⊢
    exact h
  · simp only [show 2 ≤ n + 1 + 1 by omega, show 1 ≤ n + 1 + 1 by omega,
      if_true, show n + 1 + 1 - 2 = n by omega, show n + 1 + 1 - 1 = n + 1 by omega,
      PowerSeries.coeff_derivative] at h
    push_cast at h ⊢
    nlinarith

/-- Every even inverse-sine Taylor coefficient vanishes. -/
theorem coeff_taylorSeries_arcsin_even (n : ℕ) :
    (taylorSeries Real.arcsin 0).coeff (2 * n) = 0 := by
  induction n with
  | zero => simp [coeff_taylorSeries]
  | succ n ih =>
    have h := coeff_taylorSeries_arcsin_step (2 * n)
    rw [ih, zero_mul] at h
    have hp : (0 : ℝ) < (2 * n : ℕ) + 2 := by positivity
    have hq : (0 : ℝ) < (2 * n : ℕ) + 1 := by positivity
    have hz := (mul_eq_zero.mp h).resolve_right hq.ne'
    have hz' := (mul_eq_zero.mp hz).resolve_right hp.ne'
    simpa only [Nat.mul_add, Nat.mul_one] using hz'

/-- The odd coefficients are the central-binomial inverse-sine coefficients. -/
theorem coeff_taylorSeries_arcsin_odd (n : ℕ) :
    (taylorSeries Real.arcsin 0).coeff (2 * n + 1) =
      (Nat.centralBinom n : ℝ) / (4 ^ n * (2 * n + 1)) := by
  induction n with
  | zero =>
    simpa only [pow_zero, Nat.centralBinom_zero, Nat.cast_one, Nat.cast_zero,
      mul_zero, zero_add, one_mul, div_one] using coeff_taylorSeries_arcsin_one
  | succ n ih =>
    have h := coeff_taylorSeries_arcsin_step (2 * n + 1)
    rw [ih] at h
    have hb : ((n : ℝ) + 1) * Nat.centralBinom (n + 1) =
        2 * (2 * n + 1) * Nat.centralBinom n := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ n
    have h₁ : (2 * n + 1 : ℝ) ≠ 0 := by positivity
    have h₂ : (2 * n + 2 : ℝ) ≠ 0 := by positivity
    have h₃ : (2 * n + 3 : ℝ) ≠ 0 := by positivity
    have h₄ : (4 : ℝ) ^ n ≠ 0 := by positivity
    have he : 2 * (n + 1) + 1 = 2 * n + 1 + 2 := by omega
    rw [he, pow_succ]
    push_cast at h ⊢
    field_simp at h ⊢
    nlinarith

/-- The complete inverse-sine coefficient formula at zero. -/
theorem coeff_taylorSeries_arcsin_zero (n : ℕ) :
    (taylorSeries Real.arcsin 0).coeff n = if Even n then 0 else
      (Nat.centralBinom (n / 2) : ℝ) / (4 ^ (n / 2) * n) := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [coeff_taylorSeries_arcsin_even]
    simp
  · rw [coeff_taylorSeries_arcsin_odd]
    simp [show (2 * k + 1) / 2 = k by omega]

end
end Surreal.Analytic
