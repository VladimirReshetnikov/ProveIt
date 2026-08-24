import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Finite Abel summation with complex weights

This module gives a zero-based finite partial-summation identity and its norm
inequality for genuinely complex weights.  It is independent of exponential
sums and of the Iwaniec--Mozzochi parameters.

For `P k = a 0 + ... + a k`, the exact identity is

`sum_{i=0}^K w i * a i = w K * P K + sum_{i=0}^{K-1} (w i - w (i+1)) * P i`.

Consequently a uniform bound `norm (P i) <= M` costs precisely the terminal
weight plus the discrete total variation

`norm (w K) + sum_{i=0}^{K-1} norm (w i - w (i+1))`.

No positivity, reality, monotonicity, or normalization condition is imposed on
`w`.  In particular, the intended Section 8 application may take

`w n = sigma (n / N) * (e (t n) - 1)`

after coercing the real value of `sigma` to `Complex`; all quantitative facts
about that particular weight remain explicit obligations of the caller.
-/

open scoped BigOperators
open Finset

namespace LeanProofs.IntegerPoints

namespace FiniteComplexAbel

/-- The inclusive prefix `a 0 + ... + a K`. -/
noncomputable def prefixSum (a : ℕ → ℂ) (K : ℕ) : ℂ :=
  ∑ i ∈ Finset.range (K + 1), a i

@[simp]
theorem prefixSum_zero (a : ℕ → ℂ) : prefixSum a 0 = a 0 := by
  simp [prefixSum]

/-- Extending an inclusive prefix by one index adds exactly the new term. -/
theorem prefixSum_succ (a : ℕ → ℂ) (K : ℕ) :
    prefixSum a (K + 1) = prefixSum a K + a (K + 1) := by
  simp [prefixSum, Finset.sum_range_succ]

/-- The terminal norm plus the full discrete variation of a complex weight on
the inclusive range `0, ..., K`. -/
noncomputable def variation (w : ℕ → ℂ) (K : ℕ) : ℝ :=
  ‖w K‖ + ∑ i ∈ Finset.range K, ‖w i - w (i + 1)‖

theorem variation_nonneg (w : ℕ → ℂ) (K : ℕ) :
    0 ≤ variation w K := by
  unfold variation
  exact add_nonneg (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)

/-! ## Exact finite partial summation -/

/-- Abel's finite summation identity for complex sequences and genuinely
complex weights.  The formula includes both endpoint conventions explicitly
and remains valid for `K = 0`. -/
theorem weighted_sum_eq_last_prefix_add_sum_drops
    (a w : ℕ → ℂ) (K : ℕ) :
    ∑ i ∈ Finset.range (K + 1), w i * a i =
      w K * prefixSum a K +
        ∑ i ∈ Finset.range K, (w i - w (i + 1)) * prefixSum a i := by
  induction K with
  | zero => simp [prefixSum]
  | succ K ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, prefixSum_succ]
      ring

/-! ## The norm/variation inequality -/

/-- If every inclusive prefix of `a` through `K` has norm at most `M`, then
the complex-weighted sum is bounded by `M` times the exact terminal variation
of `w`.

No separate hypothesis `0 <= M` is necessary: it follows from the prefix
bound at index zero. -/
theorem norm_weighted_sum_le_variation
    (a w : ℕ → ℂ) (K : ℕ) (M : ℝ)
    (hprefix : ∀ i, i ≤ K → ‖prefixSum a i‖ ≤ M) :
    ‖∑ i ∈ Finset.range (K + 1), w i * a i‖ ≤ M * variation w K := by
  rw [weighted_sum_eq_last_prefix_add_sum_drops]
  calc
    ‖w K * prefixSum a K +
        ∑ i ∈ Finset.range K, (w i - w (i + 1)) * prefixSum a i‖ ≤
        ‖w K * prefixSum a K‖ +
          ‖∑ i ∈ Finset.range K,
            (w i - w (i + 1)) * prefixSum a i‖ :=
      norm_add_le _ _
    _ ≤ ‖w K‖ * M +
        ∑ i ∈ Finset.range K, ‖w i - w (i + 1)‖ * M := by
      gcongr
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hprefix K le_rfl) (norm_nonneg _)
      · refine (norm_sum_le _ _).trans ?_
        refine Finset.sum_le_sum fun i hi => ?_
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left
          (hprefix i (Nat.le_of_lt (Finset.mem_range.mp hi))) (norm_nonneg _)
    _ = M * variation w K := by
      unfold variation
      rw [← Finset.sum_mul]
      ring

/-- A caller-facing form in which the exact variation is subsequently bounded
by an arbitrary real number `V`.  These are the complete finite hypotheses:
a prefix bound and a variation bound. -/
theorem norm_weighted_sum_le_of_variation_le
    (a w : ℕ → ℂ) (K : ℕ) (M V : ℝ)
    (hprefix : ∀ i, i ≤ K → ‖prefixSum a i‖ ≤ M)
    (hvariation : variation w K ≤ V) :
    ‖∑ i ∈ Finset.range (K + 1), w i * a i‖ ≤ M * V := by
  have hM : 0 ≤ M :=
    (norm_nonneg (prefixSum a 0)).trans (hprefix 0 (Nat.zero_le K))
  exact (norm_weighted_sum_le_variation a w K M hprefix).trans
    (mul_le_mul_of_nonneg_left hvariation hM)

/-- A convenient decomposition of the preceding interface into separate
terminal-weight and successive-drop estimates. -/
theorem norm_weighted_sum_le_of_endpoint_and_drops
    (a w : ℕ → ℂ) (K : ℕ) (M W₀ W₁ : ℝ)
    (hprefix : ∀ i, i ≤ K → ‖prefixSum a i‖ ≤ M)
    (hterminal : ‖w K‖ ≤ W₀)
    (hdrops : (∑ i ∈ Finset.range K, ‖w i - w (i + 1)‖) ≤ W₁) :
    ‖∑ i ∈ Finset.range (K + 1), w i * a i‖ ≤ M * (W₀ + W₁) := by
  apply norm_weighted_sum_le_of_variation_le a w K M (W₀ + W₁) hprefix
  unfold variation
  exact add_le_add hterminal hdrops

end FiniteComplexAbel

end LeanProofs.IntegerPoints
