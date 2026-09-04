import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Complex.Basic

/-!
# Formal-to-analytic transfer for scalar power series

A scalar power series `∑ a_n z^n` converging on `‖z‖ < R` is a `HasFPowerSeriesOnBall` for the
formal multilinear series `ofScalars ℂ a`.  Mathlib's uniqueness of one-dimensional power series
then gives:

* **coefficient uniqueness**: if `∑ a_n z^n` and `∑ b_n z^n` converge to the same function on
  `‖z‖ < R`, then `a = b`;
* **the identity theorem form**: if the two sums converge on `‖z‖ < R` and agree on a set with an
  accumulation point in the disk, then `a = b`;

and, trivially, equal coefficients give equal sums.  These are the two directions of the
formal-to-analytic transfer used for `q`-series identities.

## Main declarations

* `hasFPowerSeriesOnBall_ofScalars_of_hasSum`.
* `eq_of_hasSum_pow_eq`, `eq_of_hasSum_pow_frequently_eq`, `eqOn_of_coeff_eq`.
-/

set_option autoImplicit false

open Filter Topology Set
open FormalMultilinearSeries

namespace Fabius

/-- A scalar power series converging on `‖z‖ < R` is a power series on the ball of radius `R`. -/
theorem hasFPowerSeriesOnBall_ofScalars_of_hasSum {a : ℕ → ℂ} {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (ha : ∀ z : ℂ, ‖z‖ < R → HasSum (fun n => a n * z ^ n) (f z)) :
    HasFPowerSeriesOnBall f (ofScalars ℂ a) 0 (ENNReal.ofReal R) := by
  refine ⟨?_, ENNReal.ofReal_pos.mpr hR, ?_⟩
  · refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
    rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff hR] at hr
    have h := (ha ((r : ℝ) : ℂ)
      (by rw [Complex.norm_real, NNReal.norm_eq]; exact hr)).summable.tendsto_atTop_zero
    refine (ofScalars ℂ a).le_radius_of_tendsto (l := 0) ?_
    have h' := h.norm
    simp only [norm_zero, norm_mul, norm_pow, Complex.norm_real, NNReal.norm_eq] at h'
    simpa only [ofScalars_norm] using h'
  · intro y hy
    rw [Metric.eball_ofReal, mem_ball_zero_iff] at hy
    have h := ha y hy
    simp only [zero_add, ofScalars_apply_eq, smul_eq_mul]
    exact h

/-- **Coefficient uniqueness**: two scalar power series converging to the same function on
`‖z‖ < R` have the same coefficients. -/
theorem eq_of_hasSum_pow_eq {a b : ℕ → ℂ} {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (ha : ∀ z : ℂ, ‖z‖ < R → HasSum (fun n => a n * z ^ n) (f z))
    (hb : ∀ z : ℂ, ‖z‖ < R → HasSum (fun n => b n * z ^ n) (f z)) : a = b :=
  ofScalars_series_injective ℂ ℂ
    ((hasFPowerSeriesOnBall_ofScalars_of_hasSum hR ha).hasFPowerSeriesAt.eq_formalMultilinearSeries
      (hasFPowerSeriesOnBall_ofScalars_of_hasSum hR hb).hasFPowerSeriesAt)

/-- **Formal-to-analytic transfer, identity-theorem form**: two scalar power series converging on
`‖z‖ < R` whose sums agree on a set accumulating at a point of the disk have the same
coefficients. -/
theorem eq_of_hasSum_pow_frequently_eq {a b : ℕ → ℂ} {f g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (ha : ∀ z : ℂ, ‖z‖ < R → HasSum (fun n => a n * z ^ n) (f z))
    (hb : ∀ z : ℂ, ‖z‖ < R → HasSum (fun n => b n * z ^ n) (g z))
    {z₀ : ℂ} (hz₀ : ‖z₀‖ < R) (hfg : ∃ᶠ z in 𝓝[≠] z₀, f z = g z) : a = b := by
  have hfa := hasFPowerSeriesOnBall_ofScalars_of_hasSum hR ha
  have hgb := hasFPowerSeriesOnBall_ofScalars_of_hasSum hR hb
  have hU : EqOn f g (Metric.ball (0 : ℂ) R) := by
    refine AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq
      (fun z hz => hfa.analyticAt_of_mem ?_) (fun z hz => hgb.analyticAt_of_mem ?_)
      Metric.isPreconnected_ball (mem_ball_zero_iff.mpr hz₀) hfg
    · rwa [Metric.eball_ofReal]
    · rwa [Metric.eball_ofReal]
  refine eq_of_hasSum_pow_eq hR (f := g) (fun z hz => ?_) hb
  rw [← hU (mem_ball_zero_iff.mpr hz)]
  exact ha z hz

/-- Equal coefficients give equal sums on the common disk of convergence. -/
theorem eqOn_of_coeff_eq {a b : ℕ → ℂ} {f g : ℂ → ℂ} {R : ℝ}
    (ha : ∀ z : ℂ, ‖z‖ < R → HasSum (fun n => a n * z ^ n) (f z))
    (hb : ∀ z : ℂ, ‖z‖ < R → HasSum (fun n => b n * z ^ n) (g z)) (hab : a = b) :
    ∀ z : ℂ, ‖z‖ < R → f z = g z :=
  fun z hz => (ha z hz).unique (hab ▸ hb z hz)

end Fabius
