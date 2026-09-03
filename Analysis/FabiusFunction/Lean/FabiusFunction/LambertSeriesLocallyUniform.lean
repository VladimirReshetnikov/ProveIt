import FabiusFunction.QPochhammerLogDerivative
import FabiusFunction.LambertSeriesLog
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Locally uniform convergence of the Lambert-series expansions

For `‖q‖ < 1` the three series of thm:lambert-log,

* `∑_{m ≥ 1} a^m / (m (1 - q^m))`  (`= -log (a;q)_∞`),
* `∑_{m ≥ 1} a^{m-1} / (1 - q^m)`  (its derivative),
* `∑_{j ≥ 0} q^j / (1 - a q^j)`  (the same derivative, summed the other way),

converge uniformly on every closed disc `‖a‖ ≤ r < 1` (`tendstoUniformlyOn_lambert_log`,
`tendstoUniformlyOn_lambert_deriv`, `tendstoUniformlyOn_lambert_geom`), hence locally
uniformly on the open unit disc (`tendstoLocallyUniformlyOn_lambert_log`, …).  The uniform
statements are Weierstrass M-tests with the explicit majorants `r^{m+1}/(1-‖q‖)`,
`r^m/(1-‖q‖)` and `‖q‖^j/(1-r)` respectively.
-/

set_option autoImplicit false

open Filter Topology

namespace Fabius

/-- Uniform convergence on every closed disc `‖a‖ ≤ r < 1` gives locally uniform convergence
on the open unit disc. -/
theorem tendstoLocallyUniformlyOn_ball_of_closedBall {ι : Type*} {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    {p : Filter ι}
    (h : ∀ r : ℝ, r < 1 → TendstoUniformlyOn F f p (Metric.closedBall 0 r)) :
    TendstoLocallyUniformlyOn F f p (Metric.ball 0 1) := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact Metric.isOpen_ball]
  intro K hK hKc
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact tendstoUniformlyOn_empty
  obtain ⟨x, hxK, hx⟩ := hKc.exists_isMaxOn hne continuous_norm.continuousOn
  have hx1 : ‖x‖ < 1 := by
    have := hK hxK
    rwa [Metric.mem_ball, dist_zero_right] at this
  refine (h ‖x‖ hx1).mono fun y hy => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  exact hx hy

variable {q : ℂ}

/-- `1 - ‖q‖ ≤ ‖1 - q^{m+1}‖` for `‖q‖ < 1`. -/
theorem one_sub_norm_le_norm_one_sub_pow_succ (hq : ‖q‖ < 1) (m : ℕ) :
    1 - ‖q‖ ≤ ‖1 - q ^ (m + 1)‖ := by
  have hpow : ‖q‖ ^ (m + 1) ≤ ‖q‖ := pow_le_of_le_one (norm_nonneg q) hq.le (Nat.succ_ne_zero m)
  calc 1 - ‖q‖ ≤ 1 - ‖q ^ (m + 1)‖ := by rw [norm_pow]; linarith
    _ = ‖(1 : ℂ)‖ - ‖q ^ (m + 1)‖ := by rw [norm_one]
    _ ≤ ‖1 - q ^ (m + 1)‖ := norm_sub_norm_le _ _

/-- **Uniform convergence of the Lambert series** `∑ a^{m+1}/((m+1)(1-q^{m+1}))` on
`‖a‖ ≤ r < 1`. -/
theorem tendstoUniformlyOn_lambert_log (hq : ‖q‖ < 1) {r : ℝ} (hr : r < 1) :
    TendstoUniformlyOn
      (fun N => fun a : ℂ => ∑ m ∈ Finset.range N, a ^ (m + 1) / ((m + 1) * (1 - q ^ (m + 1))))
      (fun a => ∑' m : ℕ, a ^ (m + 1) / ((m + 1) * (1 - q ^ (m + 1)))) atTop
      (Metric.closedBall 0 r) := by
  rcases lt_or_ge r 0 with hr0 | hr0
  · rw [Metric.closedBall_eq_empty.mpr hr0]
    exact tendstoUniformlyOn_empty
  have h1q : 0 < 1 - ‖q‖ := by linarith
  refine tendstoUniformlyOn_tsum_nat (u := fun m => r ^ (m + 1) * (1 - ‖q‖)⁻¹) ?_ ?_
  · exact ((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hr0 hr)).mul_right _
  · intro m a ha
    rw [Metric.mem_closedBall, dist_zero_right] at ha
    rw [norm_div, norm_pow, norm_mul]
    have hm : (1 : ℝ) ≤ ‖((m : ℂ) + 1)‖ := one_le_norm_natCast_add_one m
    have hd := one_sub_norm_le_norm_one_sub_pow_succ hq m
    have hden : 1 * (1 - ‖q‖) ≤ ‖((m : ℂ) + 1)‖ * ‖1 - q ^ (m + 1)‖ :=
      mul_le_mul hm hd h1q.le (norm_nonneg _)
    calc ‖a‖ ^ (m + 1) / (‖((m : ℂ) + 1)‖ * ‖1 - q ^ (m + 1)‖)
        ≤ r ^ (m + 1) / (1 * (1 - ‖q‖)) :=
          div_le_div₀ (pow_nonneg hr0 _) (pow_le_pow_left₀ (norm_nonneg a) ha _)
            (by rw [one_mul]; exact h1q) hden
      _ = r ^ (m + 1) * (1 - ‖q‖)⁻¹ := by rw [one_mul, div_eq_mul_inv]

/-- **Uniform convergence of the derivative series** `∑ a^m/(1-q^{m+1})` on `‖a‖ ≤ r < 1`. -/
theorem tendstoUniformlyOn_lambert_deriv (hq : ‖q‖ < 1) {r : ℝ} (hr : r < 1) :
    TendstoUniformlyOn
      (fun N => fun a : ℂ => ∑ m ∈ Finset.range N, a ^ m / (1 - q ^ (m + 1)))
      (fun a => ∑' m : ℕ, a ^ m / (1 - q ^ (m + 1))) atTop (Metric.closedBall 0 r) := by
  rcases lt_or_ge r 0 with hr0 | hr0
  · rw [Metric.closedBall_eq_empty.mpr hr0]
    exact tendstoUniformlyOn_empty
  have h1q : 0 < 1 - ‖q‖ := by linarith
  refine tendstoUniformlyOn_tsum_nat (u := fun m => r ^ m * (1 - ‖q‖)⁻¹) ?_ ?_
  · exact (summable_geometric_of_lt_one hr0 hr).mul_right _
  · intro m a ha
    rw [Metric.mem_closedBall, dist_zero_right] at ha
    rw [norm_div, norm_pow]
    calc ‖a‖ ^ m / ‖1 - q ^ (m + 1)‖ ≤ r ^ m / (1 - ‖q‖) :=
          div_le_div₀ (pow_nonneg hr0 _) (pow_le_pow_left₀ (norm_nonneg a) ha _) h1q
            (one_sub_norm_le_norm_one_sub_pow_succ hq m)
      _ = r ^ m * (1 - ‖q‖)⁻¹ := div_eq_mul_inv _ _

/-- **Uniform convergence of the geometric-type series** `∑ q^j/(1 - a q^j)` on
`‖a‖ ≤ r < 1`. -/
theorem tendstoUniformlyOn_lambert_geom (hq : ‖q‖ < 1) {r : ℝ} (hr : r < 1) :
    TendstoUniformlyOn
      (fun N => fun a : ℂ => ∑ j ∈ Finset.range N, q ^ j / (1 - a * q ^ j))
      (fun a => ∑' j : ℕ, q ^ j / (1 - a * q ^ j)) atTop (Metric.closedBall 0 r) := by
  rcases lt_or_ge r 0 with hr0 | hr0
  · rw [Metric.closedBall_eq_empty.mpr hr0]
    exact tendstoUniformlyOn_empty
  have h1r : 0 < 1 - r := by linarith
  refine tendstoUniformlyOn_tsum_nat (u := fun j => ‖q‖ ^ j * (1 - r)⁻¹) ?_ ?_
  · exact (summable_geometric_of_lt_one (norm_nonneg q) hq).mul_right _
  · intro j a ha
    rw [Metric.mem_closedBall, dist_zero_right] at ha
    have hd : 1 - r ≤ ‖1 - a * q ^ j‖ := by
      have h1 : ‖a * q ^ j‖ ≤ r := by
        rw [norm_mul, norm_pow]
        exact (mul_le_of_le_one_right (norm_nonneg a) (pow_le_one₀ (norm_nonneg q) hq.le)).trans ha
      calc 1 - r ≤ 1 - ‖a * q ^ j‖ := by linarith
        _ = ‖(1 : ℂ)‖ - ‖a * q ^ j‖ := by rw [norm_one]
        _ ≤ ‖1 - a * q ^ j‖ := norm_sub_norm_le _ _
    rw [norm_div, norm_pow]
    calc ‖q‖ ^ j / ‖1 - a * q ^ j‖ ≤ ‖q‖ ^ j / (1 - r) :=
          div_le_div_of_nonneg_left (pow_nonneg (norm_nonneg q) j) h1r hd
      _ = ‖q‖ ^ j * (1 - r)⁻¹ := div_eq_mul_inv _ _

/-- The Lambert series converges locally uniformly on the open unit disc. -/
theorem tendstoLocallyUniformlyOn_lambert_log (hq : ‖q‖ < 1) :
    TendstoLocallyUniformlyOn
      (fun N => fun a : ℂ => ∑ m ∈ Finset.range N, a ^ (m + 1) / ((m + 1) * (1 - q ^ (m + 1))))
      (fun a => ∑' m : ℕ, a ^ (m + 1) / ((m + 1) * (1 - q ^ (m + 1)))) atTop (Metric.ball 0 1) :=
  tendstoLocallyUniformlyOn_ball_of_closedBall fun _ hr => tendstoUniformlyOn_lambert_log hq hr

/-- The derivative series converges locally uniformly on the open unit disc. -/
theorem tendstoLocallyUniformlyOn_lambert_deriv (hq : ‖q‖ < 1) :
    TendstoLocallyUniformlyOn
      (fun N => fun a : ℂ => ∑ m ∈ Finset.range N, a ^ m / (1 - q ^ (m + 1)))
      (fun a => ∑' m : ℕ, a ^ m / (1 - q ^ (m + 1))) atTop (Metric.ball 0 1) :=
  tendstoLocallyUniformlyOn_ball_of_closedBall fun _ hr => tendstoUniformlyOn_lambert_deriv hq hr

/-- The geometric-type series converges locally uniformly on the open unit disc. -/
theorem tendstoLocallyUniformlyOn_lambert_geom (hq : ‖q‖ < 1) :
    TendstoLocallyUniformlyOn
      (fun N => fun a : ℂ => ∑ j ∈ Finset.range N, q ^ j / (1 - a * q ^ j))
      (fun a => ∑' j : ℕ, q ^ j / (1 - a * q ^ j)) atTop (Metric.ball 0 1) :=
  tendstoLocallyUniformlyOn_ball_of_closedBall fun _ hr => tendstoUniformlyOn_lambert_geom hq hr

end Fabius
