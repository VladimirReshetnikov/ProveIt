import FabiusFunction.DoublingMapTransfer
import FabiusFunction.CocycleCovarianceHalving

/-!
# The covariance ladder: `c_r = (π²/12)·2⁻ʳ`

The complete geometric decay of the doubling-cocycle covariances, for
**every** lag: with `T` the doubling map mod one and
`ψ = log (2 sin π·)`,

`c_r := ∫₀¹ ψ·(ψ∘Tʳ) = (π²/12)·(1/2)ʳ`.

Induction on `r`: the base is the Clausen value
(`CocycleParseval`), and each step halves by the transfer identity
(`DoublingMapTransfer`) against the Perron eigenrelation `𝒫ψ = ψ/2`
(`DoublingCocycleIdentities`), with square-integrability of all
composites supplied by measure preservation of `T`.

This closes the covariance input of Document 6's variance theorem:
combined with `VarianceBookkeeping`'s closed form, the Birkhoff
variance of the cocycle is now fully numeric,
`Var = (π²/4)n − (π²/3)(1 − 2⁻ⁿ)`, modulo only the CLT/LIL machinery.

* `intervalIntegrable_comp_doublingMap` — composability of `L¹` data.
* `intervalIntegrable_sq_cocycle_iterate`,
  `integral_sq_cocycle_iterate` — `ψ∘Tʳ ∈ L²` with constant norm.
* `integral_cocycle_covariance` — **the ladder**.
-/

set_option autoImplicit false

open Filter Topology intervalIntegral Real MeasureTheory Set

namespace Fabius

/-- Composition with the doubling map preserves interval
integrability on `[0,1]`. -/
theorem intervalIntegrable_comp_doublingMap {g : ℝ → ℝ}
    (hg : IntervalIntegrable g MeasureTheory.volume 0 1) :
    IntervalIntegrable (fun t => g (doublingMap t))
      MeasureTheory.volume 0 1 := by
  have hA : IntervalIntegrable
      (fun t => (fun _ : ℝ => (1:ℝ)) t * g (doublingMap t))
      MeasureTheory.volume 0 (1 / 2) :=
    intervalIntegrable_mul_comp_doublingMap_left (by simpa using hg)
  have hB : IntervalIntegrable
      (fun t => (fun _ : ℝ => (1:ℝ)) t * g (doublingMap t))
      MeasureTheory.volume (1 / 2) 1 :=
    intervalIntegrable_mul_comp_doublingMap_right (by simpa using hg)
  have heq : (fun t => (fun _ : ℝ => (1:ℝ)) t * g (doublingMap t)) =
      fun t => g (doublingMap t) := by
    funext t
    simp
  rw [heq] at hA hB
  exact hA.trans hB

/-- The iterated composites `ψ∘Tʳ` are square-integrable. -/
theorem intervalIntegrable_sq_cocycle_iterate (r : ℕ) :
    IntervalIntegrable (fun t =>
      Real.log (2 * Real.sin (π * (doublingMap^[r] t))) ^ 2)
      MeasureTheory.volume 0 1 := by
  induction r with
  | zero =>
      simpa using intervalIntegrable_sq_log_two_sin_pi_mul
  | succ r ih =>
      have h : IntervalIntegrable (fun t =>
          Real.log (2 * Real.sin
            (π * (doublingMap^[r] (doublingMap t)))) ^ 2)
          MeasureTheory.volume 0 1 :=
        intervalIntegrable_comp_doublingMap ih
      have heq : (fun t : ℝ =>
          Real.log (2 * Real.sin
            (π * (doublingMap^[r] (doublingMap t)))) ^ 2) =
          fun t => Real.log (2 * Real.sin
            (π * (doublingMap^[r + 1] t))) ^ 2 := by
        funext t
        rw [Function.iterate_succ_apply]
      rwa [heq] at h

/-- `T` preserves the `L²` mass of the cocycle:
`∫₀¹ (ψ∘Tʳ)² = π²/12` for every `r`. -/
theorem integral_sq_cocycle_iterate (r : ℕ) :
    ∫ t in (0:ℝ)..1,
      Real.log (2 * Real.sin (π * (doublingMap^[r] t))) ^ 2 =
      π ^ 2 / 12 := by
  induction r with
  | zero =>
      simpa using integral_sq_log_two_sin_pi_mul
  | succ r ih =>
      have h := integral_comp_doublingMap
        (fun s => Real.log (2 * Real.sin (π * (doublingMap^[r] s))) ^ 2)
        (intervalIntegrable_sq_cocycle_iterate r)
      have heq : ∫ t in (0:ℝ)..1,
          Real.log (2 * Real.sin
            (π * (doublingMap^[r + 1] t))) ^ 2 =
          ∫ t in (0:ℝ)..1, (fun s =>
            Real.log (2 * Real.sin (π * (doublingMap^[r] s))) ^ 2)
            (doublingMap t) := by
        refine intervalIntegral.integral_congr fun t _ => ?_
        show Real.log (2 * Real.sin (π * (doublingMap^[r + 1] t))) ^ 2 =
          Real.log (2 * Real.sin
            (π * (doublingMap^[r] (doublingMap t)))) ^ 2
        rw [Function.iterate_succ_apply]
      rw [heq, h]
      exact ih

/-- **The covariance ladder**: `∫₀¹ ψ·(ψ∘Tʳ) = (π²/12)·(1/2)ʳ` for
every lag `r` — the audits' exact geometric covariance decay, now with
both the mechanism and the number formal. -/
theorem integral_cocycle_covariance (r : ℕ) :
    ∫ t in (0:ℝ)..1, Real.log (2 * Real.sin (π * t)) *
      Real.log (2 * Real.sin (π * (doublingMap^[r] t))) =
      π ^ 2 / 12 * (1 / 2) ^ r := by
  induction r with
  | zero =>
      have heq : ∫ t in (0:ℝ)..1, Real.log (2 * Real.sin (π * t)) *
          Real.log (2 * Real.sin (π * (doublingMap^[0] t))) =
          ∫ t in (0:ℝ)..1, Real.log (2 * Real.sin (π * t)) ^ 2 := by
        refine intervalIntegral.integral_congr fun t _ => ?_
        show Real.log (2 * Real.sin (π * t)) *
          Real.log (2 * Real.sin (π * (doublingMap^[0] t))) =
          Real.log (2 * Real.sin (π * t)) ^ 2
        rw [Function.iterate_zero_apply]
        ring
      rw [heq, integral_sq_log_two_sin_pi_mul]
      simp
  | succ r ih =>
      set g : ℝ → ℝ := fun s =>
        Real.log (2 * Real.sin (π * (doublingMap^[r] s))) with hg
      -- branch-product integrability via AM–GM domination
      have hgsq := intervalIntegrable_sq_cocycle_iterate r
      have hmeasg : Measurable g :=
        measurable_log_two_sin_pi_mul.comp
          (measurable_doublingMap.iterate r)
      have hint1 : IntervalIntegrable (fun u =>
          Real.log (2 * Real.sin (π * (u / 2))) * g u)
          MeasureTheory.volume 0 1 := by
        have hdom : IntervalIntegrable (fun u => (1 / 2 : ℝ) *
            (Real.log (2 * Real.sin (π * (u / 2))) ^ 2 + g u ^ 2))
            MeasureTheory.volume 0 1 :=
          (intervalIntegrable_sq_log_two_sin_half.add hgsq).const_mul
            (1 / 2)
        apply hdom.mono_fun
        · exact ((measurable_log_two_sin_pi_mul.comp
            (measurable_id.div_const 2)).mul hmeasg).aestronglyMeasurable
        · filter_upwards with u
          set A := Real.log (2 * Real.sin (π * (u / 2)))
          simp only [Real.norm_eq_abs]
          rw [abs_mul, abs_of_nonneg (by positivity :
            (0:ℝ) ≤ 1 / 2 * (A ^ 2 + g u ^ 2))]
          nlinarith [sq_nonneg (|A| - |g u|), sq_abs A, sq_abs (g u),
            abs_nonneg A, abs_nonneg (g u)]
      have hint2 : IntervalIntegrable (fun u =>
          Real.log (2 * Real.sin (π * ((u + 1) / 2))) * g u)
          MeasureTheory.volume 0 1 := by
        have hdom : IntervalIntegrable (fun u => (1 / 2 : ℝ) *
            (Real.log (2 * Real.sin (π * ((u + 1) / 2))) ^ 2 + g u ^ 2))
            MeasureTheory.volume 0 1 :=
          (intervalIntegrable_sq_log_two_sin_shift.add hgsq).const_mul
            (1 / 2)
        apply hdom.mono_fun
        · exact ((measurable_log_two_sin_pi_mul.comp
            ((measurable_id.add_const 1).div_const 2)).mul
            hmeasg).aestronglyMeasurable
        · filter_upwards with u
          set A := Real.log (2 * Real.sin (π * ((u + 1) / 2)))
          simp only [Real.norm_eq_abs]
          rw [abs_mul, abs_of_nonneg (by positivity :
            (0:ℝ) ≤ 1 / 2 * (A ^ 2 + g u ^ 2))]
          nlinarith [sq_nonneg (|A| - |g u|), sq_abs A, sq_abs (g u),
            abs_nonneg A, abs_nonneg (g u)]
      -- rewrite the (r+1)-covariance as a pairing with g∘T
      have hstep : ∫ t in (0:ℝ)..1, Real.log (2 * Real.sin (π * t)) *
          Real.log (2 * Real.sin (π * (doublingMap^[r + 1] t))) =
          ∫ t in (0:ℝ)..1, Real.log (2 * Real.sin (π * t)) *
            g (doublingMap t) := by
        refine intervalIntegral.integral_congr fun t _ => ?_
        show Real.log (2 * Real.sin (π * t)) *
          Real.log (2 * Real.sin (π * (doublingMap^[r + 1] t))) =
          Real.log (2 * Real.sin (π * t)) *
            Real.log (2 * Real.sin (π * (doublingMap^[r] (doublingMap t))))
        rw [Function.iterate_succ_apply]
      -- transfer + Perron halving
      have htrans := integral_mul_comp_doublingMap
        (fun t => Real.log (2 * Real.sin (π * t))) g hint1 hint2
      have hhalf : ∫ t in (0:ℝ)..1,
          ((fun t => Real.log (2 * Real.sin (π * t))) (t / 2) +
            (fun t => Real.log (2 * Real.sin (π * t))) ((t + 1) / 2)) / 2 *
            g t =
          ∫ t in (0:ℝ)..1, (1 / 2 : ℝ) *
            (Real.log (2 * Real.sin (π * t)) * g t) := by
        apply intervalIntegral.integral_congr_ae
        have h1ae : ∀ᵐ t : ℝ, t ≠ (1:ℝ) := by
          rw [MeasureTheory.ae_iff]
          simp
        filter_upwards [h1ae] with t ht1 hmem
        rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hmem
        have hs : Real.sin (π * t) ≠ 0 := by
          have h : 0 < Real.sin (π * t) := by
            apply Real.sin_pos_of_pos_of_lt_pi
            · have := hmem.1
              positivity
            · nlinarith [Real.pi_pos, hmem.1,
                lt_of_le_of_ne hmem.2 ht1]
          exact ne_of_gt h
        have hkey := log_two_sin_half_add t hs
        show (Real.log (2 * Real.sin (π * (t / 2))) +
          Real.log (2 * Real.sin (π * ((t + 1) / 2)))) / 2 * g t =
          1 / 2 * (Real.log (2 * Real.sin (π * t)) * g t)
        rw [show π * (t / 2) = π * t / 2 by ring,
          show π * ((t + 1) / 2) = π * (t + 1) / 2 by ring, hkey]
        ring
      rw [hstep, htrans, hhalf, intervalIntegral.integral_const_mul, ih]
      ring

end Fabius
