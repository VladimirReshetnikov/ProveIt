import FabiusFunction.BirkhoffVariance

/-!
# First and normalized second moments of the Birkhoff sums

Closing the moment picture of the audits' fluctuation theorem: the
Birkhoff sums are exactly centered, and their normalized variance
converges to the audits' `σ² = π²/4`:

`∫₀¹ Sₙ = 0`,   `(1/n)·∫₀¹ Sₙ² → π²/4`.

* `intervalIntegrable_cocycle_iterate` — `ψ∘Tᵏ ∈ L¹`.
* `integral_cocycle_iterate` — `∫₀¹ ψ∘Tᵏ = 0` for every `k`.
* `integral_birkhoff_sum` — the exact centering.
* `tendsto_integral_sq_birkhoff_div` — `σ² = π²/4` as a limit.
-/

set_option autoImplicit false

open Filter Topology intervalIntegral Real MeasureTheory Set

namespace Fabius

/-- Each iterate of the cocycle is integrable. -/
theorem intervalIntegrable_cocycle_iterate (k : ℕ) :
    IntervalIntegrable (fun t =>
      Real.log (2 * Real.sin (π * (doublingMap^[k] t))))
      MeasureTheory.volume 0 1 := by
  induction k with
  | zero =>
      simpa using intervalIntegrable_log_two_sin_pi_mul_self
  | succ k ih =>
      have h : IntervalIntegrable (fun t =>
          Real.log (2 * Real.sin
            (π * (doublingMap^[k] (doublingMap t)))))
          MeasureTheory.volume 0 1 :=
        intervalIntegrable_comp_doublingMap ih
      have heq : (fun t : ℝ =>
          Real.log (2 * Real.sin
            (π * (doublingMap^[k] (doublingMap t))))) =
          fun t => Real.log (2 * Real.sin
            (π * (doublingMap^[k + 1] t))) := by
        funext t
        rw [Function.iterate_succ_apply]
      rwa [heq] at h

/-- Each iterate of the cocycle has mean zero:
`∫₀¹ ψ(Tᵏt) dt = 0`. -/
theorem integral_cocycle_iterate (k : ℕ) :
    ∫ t in (0:ℝ)..1,
      Real.log (2 * Real.sin (π * (doublingMap^[k] t))) = 0 := by
  induction k with
  | zero =>
      simpa using integral_log_two_sin_pi_mul
  | succ k ih =>
      have h := integral_comp_doublingMap
        (fun s => Real.log (2 * Real.sin (π * (doublingMap^[k] s))))
        (intervalIntegrable_cocycle_iterate k)
      have heq : ∫ t in (0:ℝ)..1,
          Real.log (2 * Real.sin (π * (doublingMap^[k + 1] t))) =
          ∫ t in (0:ℝ)..1, (fun s =>
            Real.log (2 * Real.sin (π * (doublingMap^[k] s))))
            (doublingMap t) := by
        refine intervalIntegral.integral_congr fun t _ => ?_
        show Real.log (2 * Real.sin (π * (doublingMap^[k + 1] t))) =
          Real.log (2 * Real.sin
            (π * (doublingMap^[k] (doublingMap t))))
        rw [Function.iterate_succ_apply]
      rw [heq, h]
      exact ih

/-- **The Birkhoff sums are exactly centered**: `∫₀¹ Sₙ = 0`. -/
theorem integral_birkhoff_sum (n : ℕ) :
    ∫ t in (0:ℝ)..1, (∑ k ∈ Finset.range n,
      Real.log (2 * Real.sin (π * (doublingMap^[k] t)))) = 0 := by
  rw [intervalIntegral.integral_finsetSum
    (fun k _ => intervalIntegrable_cocycle_iterate k)]
  exact Finset.sum_eq_zero (fun k _ => integral_cocycle_iterate k)

/-- **The audits' `σ² = π²/4` as a normalized limit**:
`(1/n)·∫₀¹ Sₙ² → π²/4`. -/
theorem tendsto_integral_sq_birkhoff_div :
    Tendsto (fun n : ℕ => (∫ t in (0:ℝ)..1,
      (∑ k ∈ Finset.range n,
        Real.log (2 * Real.sin (π * (doublingMap^[k] t)))) ^ 2) / n)
      atTop (𝓝 (π ^ 2 / 4)) := by
  have hzero : Tendsto (fun n : ℕ =>
      π ^ 2 / 3 * (1 - (1 / 2 : ℝ) ^ n) / n) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun n : ℕ => (π ^ 2 / 3) / n)
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (0:ℝ) < (n:ℝ) := by
        have h1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
        linarith
      have hB0 : (0:ℝ) ≤ 1 - (1 / 2 : ℝ) ^ n := by
        have h := pow_le_one₀ (by norm_num : (0:ℝ) ≤ 1 / 2)
          (by norm_num : (1:ℝ) / 2 ≤ 1) (n := n)
        linarith
      have hB1 : (1:ℝ) - (1 / 2 : ℝ) ^ n ≤ 1 := by
        have h : (0:ℝ) ≤ ((1:ℝ) / 2) ^ n := by positivity
        linarith
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
        (0:ℝ) ≤ π ^ 2 / 3 * (1 - (1 / 2 : ℝ) ^ n) / n)]
      gcongr
      exact mul_le_of_le_one_right (by positivity) hB1
    · exact tendsto_const_div_atTop_nhds_zero_nat _
  have hmain : Tendsto (fun n : ℕ => π ^ 2 / 4 -
      π ^ 2 / 3 * (1 - (1 / 2 : ℝ) ^ n) / n) atTop
      (𝓝 (π ^ 2 / 4)) := by
    have h := (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => π ^ 2 / 4) atTop
        (𝓝 (π ^ 2 / 4))).sub hzero
    rwa [sub_zero] at h
  refine Filter.Tendsto.congr' ?_ hmain
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : ((n:ℝ)) ≠ 0 := by
    have h1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    linarith
  rw [integral_sq_birkhoff_sum n hn]
  field_simp

end Fabius
