import FabiusFunction.CovarianceLadder
import FabiusFunction.DistanceCounting
import FabiusFunction.VarianceBookkeeping

/-!
# The exact Birkhoff variance: `∫₀¹ Sₙ² = (π²/4)n − (π²/3)(1 − 2⁻ⁿ)`

The audits' variance theorem (`thm:variance`), fully numeric: for the
Birkhoff sums `Sₙ(t) = ∑_{k<n} ψ(Tᵏt)` of the doubling cocycle
`ψ = log (2 sin π·)` under the doubling map `T`,

`∫₀¹ Sₙ² = n·c₀ + 2·∑_{r=1}^{n−1} (n−r)·c_r
        = (π²/4)·n − (π²/3)·(1 − (1/2)ⁿ)`.

Every ingredient is now formal: the covariance ladder
`c_r = (π²/12)·2⁻ʳ` (`CovarianceLadder`), stationarity by measure
preservation, the diagonal count (`DistanceCounting`), and the
geometric bookkeeping (`VarianceBookkeeping`).  This is the exact
finite-`n` variance behind `σ = π/2` and the corrected LIL constant
`π/√2`.

* `intervalIntegrable_cocycle_pair` — pairwise products in `L¹`.
* `integral_cocycle_pair` — stationarity:
  `∫ (ψ∘Tʲ)(ψ∘Tʲ⁺ʳ) = c_r`.
* `integral_cocycle_pair_dist` — both orders via `Nat.dist`.
* `integral_sq_birkhoff_sum` — **the exact variance**.
-/

set_option autoImplicit false

open Filter Topology intervalIntegral Real MeasureTheory Set

namespace Fabius

/-- All pairwise products of cocycle iterates are integrable. -/
theorem intervalIntegrable_cocycle_pair (a b : ℕ) :
    IntervalIntegrable (fun t =>
      Real.log (2 * Real.sin (π * (doublingMap^[a] t))) *
        Real.log (2 * Real.sin (π * (doublingMap^[b] t))))
      MeasureTheory.volume 0 1 := by
  have hdom : IntervalIntegrable (fun t => (1 / 2 : ℝ) *
      (Real.log (2 * Real.sin (π * (doublingMap^[a] t))) ^ 2 +
        Real.log (2 * Real.sin (π * (doublingMap^[b] t))) ^ 2))
      MeasureTheory.volume 0 1 :=
    ((intervalIntegrable_sq_cocycle_iterate a).add
      (intervalIntegrable_sq_cocycle_iterate b)).const_mul (1 / 2)
  apply hdom.mono_fun
  · exact ((measurable_log_two_sin_pi_mul.comp
      (measurable_doublingMap.iterate a)).mul
      (measurable_log_two_sin_pi_mul.comp
        (measurable_doublingMap.iterate b))).aestronglyMeasurable
  · filter_upwards with t
    set A := Real.log (2 * Real.sin (π * (doublingMap^[a] t)))
    set B := Real.log (2 * Real.sin (π * (doublingMap^[b] t)))
    simp only [Real.norm_eq_abs]
    rw [abs_mul, abs_of_nonneg (by positivity :
      (0:ℝ) ≤ 1 / 2 * (A ^ 2 + B ^ 2))]
    nlinarith [sq_nonneg (|A| - |B|), sq_abs A, sq_abs B,
      abs_nonneg A, abs_nonneg B]

/-- **Stationarity**: the pair correlation depends only on the lag,
`∫₀¹ (ψ∘Tʲ)·(ψ∘Tʲ⁺ʳ) = (π²/12)·(1/2)ʳ`. -/
theorem integral_cocycle_pair (j r : ℕ) :
    ∫ t in (0:ℝ)..1,
      Real.log (2 * Real.sin (π * (doublingMap^[j] t))) *
        Real.log (2 * Real.sin (π * (doublingMap^[j + r] t))) =
      π ^ 2 / 12 * (1 / 2) ^ r := by
  induction j with
  | zero =>
      have heq : ∫ t in (0:ℝ)..1,
          Real.log (2 * Real.sin (π * (doublingMap^[0] t))) *
            Real.log (2 * Real.sin (π * (doublingMap^[0 + r] t))) =
          ∫ t in (0:ℝ)..1, Real.log (2 * Real.sin (π * t)) *
            Real.log (2 * Real.sin (π * (doublingMap^[r] t))) := by
        refine intervalIntegral.integral_congr fun t _ => ?_
        show Real.log (2 * Real.sin (π * (doublingMap^[0] t))) *
          Real.log (2 * Real.sin (π * (doublingMap^[0 + r] t))) =
          Real.log (2 * Real.sin (π * t)) *
            Real.log (2 * Real.sin (π * (doublingMap^[r] t)))
        rw [Function.iterate_zero_apply, Nat.zero_add]
      rw [heq]
      exact integral_cocycle_covariance r
  | succ j ih =>
      have h := integral_comp_doublingMap
        (fun s => Real.log (2 * Real.sin (π * (doublingMap^[j] s))) *
          Real.log (2 * Real.sin (π * (doublingMap^[j + r] s))))
        (intervalIntegrable_cocycle_pair j (j + r))
      have heq : ∫ t in (0:ℝ)..1,
          Real.log (2 * Real.sin (π * (doublingMap^[j + 1] t))) *
            Real.log (2 * Real.sin (π * (doublingMap^[j + 1 + r] t))) =
          ∫ t in (0:ℝ)..1, (fun s =>
            Real.log (2 * Real.sin (π * (doublingMap^[j] s))) *
              Real.log (2 * Real.sin (π * (doublingMap^[j + r] s))))
            (doublingMap t) := by
        refine intervalIntegral.integral_congr fun t _ => ?_
        show Real.log (2 * Real.sin (π * (doublingMap^[j + 1] t))) *
          Real.log (2 * Real.sin (π * (doublingMap^[j + 1 + r] t))) =
          Real.log (2 * Real.sin
            (π * (doublingMap^[j] (doublingMap t)))) *
            Real.log (2 * Real.sin
              (π * (doublingMap^[j + r] (doublingMap t))))
        have hidx : j + 1 + r = (j + r) + 1 := by omega
        rw [hidx, Function.iterate_succ_apply,
          Function.iterate_succ_apply]
      rw [heq, h]
      exact ih

/-- Both orders via the distance: for all `j, k`,
`∫₀¹ (ψ∘Tʲ)·(ψ∘Tᵏ) = (π²/12)·(1/2)^{|j−k|}`. -/
theorem integral_cocycle_pair_dist (j k : ℕ) :
    ∫ t in (0:ℝ)..1,
      Real.log (2 * Real.sin (π * (doublingMap^[j] t))) *
        Real.log (2 * Real.sin (π * (doublingMap^[k] t))) =
      π ^ 2 / 12 * (1 / 2) ^ (Nat.dist j k) := by
  rcases le_total j k with hjk | hkj
  · have h := integral_cocycle_pair j (k - j)
    rw [show j + (k - j) = k by omega] at h
    rw [h, Nat.dist_eq_sub_of_le hjk]
  · have h := integral_cocycle_pair k (j - k)
    rw [show k + (j - k) = j by omega] at h
    have hcomm : ∫ t in (0:ℝ)..1,
        Real.log (2 * Real.sin (π * (doublingMap^[j] t))) *
          Real.log (2 * Real.sin (π * (doublingMap^[k] t))) =
        ∫ t in (0:ℝ)..1,
          Real.log (2 * Real.sin (π * (doublingMap^[k] t))) *
            Real.log (2 * Real.sin (π * (doublingMap^[j] t))) := by
      refine intervalIntegral.integral_congr fun t _ => ?_
      exact mul_comm _ _
    rw [hcomm, h, Nat.dist_comm, Nat.dist_eq_sub_of_le hkj]

/-- **The exact Birkhoff variance** (`thm:variance`):

`∫₀¹ (∑_{k<n} ψ(Tᵏt))² dt = (π²/4)·n − (π²/3)·(1 − (1/2)ⁿ)`. -/
theorem integral_sq_birkhoff_sum (n : ℕ) (hn : 1 ≤ n) :
    ∫ t in (0:ℝ)..1, (∑ k ∈ Finset.range n,
      Real.log (2 * Real.sin (π * (doublingMap^[k] t)))) ^ 2 =
      π ^ 2 / 4 * n - π ^ 2 / 3 * (1 - (1 / 2) ^ n) := by
  have hexp : ∫ t in (0:ℝ)..1, (∑ k ∈ Finset.range n,
      Real.log (2 * Real.sin (π * (doublingMap^[k] t)))) ^ 2 =
      ∫ t in (0:ℝ)..1, ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n,
        Real.log (2 * Real.sin (π * (doublingMap^[j] t))) *
          Real.log (2 * Real.sin (π * (doublingMap^[k] t))) := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    show (∑ k ∈ Finset.range n,
      Real.log (2 * Real.sin (π * (doublingMap^[k] t)))) ^ 2 =
      ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n,
        Real.log (2 * Real.sin (π * (doublingMap^[j] t))) *
          Real.log (2 * Real.sin (π * (doublingMap^[k] t)))
    rw [sq, Finset.sum_mul_sum]
  have hInner : ∀ j : ℕ, IntervalIntegrable (fun t =>
      ∑ k ∈ Finset.range n,
        Real.log (2 * Real.sin (π * (doublingMap^[j] t))) *
          Real.log (2 * Real.sin (π * (doublingMap^[k] t))))
      MeasureTheory.volume 0 1 := by
    intro j
    have h := IntervalIntegrable.sum (Finset.range n)
      (f := fun k => fun t =>
        Real.log (2 * Real.sin (π * (doublingMap^[j] t))) *
          Real.log (2 * Real.sin (π * (doublingMap^[k] t))))
      (fun k _ => intervalIntegrable_cocycle_pair j k)
    have heq : (∑ k ∈ Finset.range n, fun t =>
        Real.log (2 * Real.sin (π * (doublingMap^[j] t))) *
          Real.log (2 * Real.sin (π * (doublingMap^[k] t)))) =
        fun t => ∑ k ∈ Finset.range n,
          Real.log (2 * Real.sin (π * (doublingMap^[j] t))) *
            Real.log (2 * Real.sin (π * (doublingMap^[k] t))) := by
      funext t
      simp [Finset.sum_apply]
    rwa [heq] at h
  have hswap : ∫ t in (0:ℝ)..1,
      ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n,
        Real.log (2 * Real.sin (π * (doublingMap^[j] t))) *
          Real.log (2 * Real.sin (π * (doublingMap^[k] t))) =
      ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n,
        ∫ t in (0:ℝ)..1,
          Real.log (2 * Real.sin (π * (doublingMap^[j] t))) *
            Real.log (2 * Real.sin (π * (doublingMap^[k] t))) := by
    rw [intervalIntegral.integral_finsetSum (fun j _ => hInner j)]
    exact Finset.sum_congr rfl (fun j _ =>
      intervalIntegral.integral_finsetSum (fun k _ =>
        intervalIntegrable_cocycle_pair j k))
  have hval : ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n,
      (∫ t in (0:ℝ)..1,
        Real.log (2 * Real.sin (π * (doublingMap^[j] t))) *
          Real.log (2 * Real.sin (π * (doublingMap^[k] t)))) =
      ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n,
        (fun r : ℕ => π ^ 2 / 12 * (1 / 2 : ℝ) ^ r) (Nat.dist j k) :=
    Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ =>
      integral_cocycle_pair_dist j k))
  rw [hexp, hswap, hval,
    sum_sum_dist (fun r : ℕ => π ^ 2 / 12 * (1 / 2 : ℝ) ^ r) n]
  have h0 : π ^ 2 / 12 * (1 / 2 : ℝ) ^ (0 : ℕ) = π ^ 2 / 12 := by
    norm_num
  rw [h0]
  exact variance_closed_form n hn

end Fabius
