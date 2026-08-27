import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The stationary double-sum counting identity

For any `f : ℕ → ℝ`,

`∑_{j,k < n} f (|j − k|) = n·f 0 + 2·∑_{r=1}^{n−1} (n − r)·f r` —

the diagonal count of a stationary covariance array: `n` diagonal
entries and `n − r` entries on each of the two `r`-th off-diagonals.
This is the combinatorial half of every stationary-variance
decomposition (`Var(Sₙ) = n c₀ + 2Σ (n−r) c_r`).

* `sum_Ico_succ_eq_sum_range` — index shift.
* `sum_range_sub_index` — reflection `∑_{j<n} f(n−j) = ∑_{j<n} f(j+1)`.
* `sum_sum_dist` — **the counting identity**.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- Index shift: `∑_{r ∈ [1, n+1)} f r = ∑_{j < n} f (j+1)`. -/
theorem sum_Ico_succ_eq_sum_range (f : ℕ → ℝ) (n : ℕ) :
    ∑ r ∈ Finset.Ico 1 (n + 1), f r =
      ∑ j ∈ Finset.range n, f (j + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ n + 1), ih,
        Finset.sum_range_succ]

/-- Reflection: `∑_{j<n} f (n − j) = ∑_{j<n} f (j+1)`. -/
theorem sum_range_sub_index (f : ℕ → ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range n, f (n - j) =
      ∑ j ∈ Finset.range n, f (j + 1) := by
  have h := Finset.sum_range_reflect (fun m => f (m + 1)) n
  have hcongr : ∑ j ∈ Finset.range n, (fun m => f (m + 1)) (n - 1 - j) =
      ∑ j ∈ Finset.range n, f (n - j) :=
    Finset.sum_congr rfl (fun j hj => by
      have hjn : j < n := Finset.mem_range.mp hj
      have : n - 1 - j + 1 = n - j := by omega
      simp only
      rw [this])
  rw [← hcongr, h]

/-- **The stationary counting identity**:
`∑_{j,k<n} f(|j−k|) = n·f 0 + 2·∑_{r∈[1,n)} (n−r)·f r`. -/
theorem sum_sum_dist (f : ℕ → ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n, f (Nat.dist j k) =
      (n : ℝ) * f 0 +
        2 * ∑ r ∈ Finset.Ico 1 n, ((n : ℝ) - (r : ℝ)) * f r := by
  induction n with
  | zero => simp
  | succ n ih =>
      -- expand the two new border sums
      have houter : ∑ j ∈ Finset.range (n + 1),
          ∑ k ∈ Finset.range (n + 1), f (Nat.dist j k) =
          (∑ j ∈ Finset.range n,
            ∑ k ∈ Finset.range n, f (Nat.dist j k)) +
          (∑ j ∈ Finset.range n, f (Nat.dist j n)) +
          (∑ k ∈ Finset.range n, f (Nat.dist n k)) +
          f (Nat.dist n n) := by
        rw [Finset.sum_range_succ]
        have hinner : ∑ j ∈ Finset.range n,
            ∑ k ∈ Finset.range (n + 1), f (Nat.dist j k) =
            ∑ j ∈ Finset.range n,
              (∑ k ∈ Finset.range n, f (Nat.dist j k) +
                f (Nat.dist j n)) :=
          Finset.sum_congr rfl (fun j _ => Finset.sum_range_succ _ n)
        rw [hinner, Finset.sum_add_distrib, Finset.sum_range_succ]
        ring
      have hdist1 : ∑ j ∈ Finset.range n, f (Nat.dist j n) =
          ∑ j ∈ Finset.range n, f (n - j) :=
        Finset.sum_congr rfl (fun j hj => by
          rw [Nat.dist_eq_sub_of_le (Finset.mem_range.mp hj).le])
      have hdist2 : ∑ k ∈ Finset.range n, f (Nat.dist n k) =
          ∑ k ∈ Finset.range n, f (n - k) :=
        Finset.sum_congr rfl (fun k hk => by
          rw [Nat.dist_comm,
            Nat.dist_eq_sub_of_le (Finset.mem_range.mp hk).le])
      have hborder : ∑ j ∈ Finset.range n, f (n - j) =
          ∑ r ∈ Finset.Ico 1 (n + 1), f r := by
        rw [sum_range_sub_index, sum_Ico_succ_eq_sum_range]
      -- the RHS increment
      have hRHS : ((n + 1 : ℕ) : ℝ) * f 0 +
          2 * ∑ r ∈ Finset.Ico 1 (n + 1),
            (((n + 1 : ℕ) : ℝ) - (r : ℝ)) * f r =
          ((n : ℝ) * f 0 +
            2 * ∑ r ∈ Finset.Ico 1 n, ((n : ℝ) - (r : ℝ)) * f r) +
          f 0 + 2 * ∑ r ∈ Finset.Ico 1 (n + 1), f r := by
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp
        · rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ n),
            Finset.sum_Ico_succ_top (by omega : 1 ≤ n)]
          have hsplit : ∑ r ∈ Finset.Ico 1 n,
              (((n + 1 : ℕ) : ℝ) - (r : ℝ)) * f r =
              (∑ r ∈ Finset.Ico 1 n, ((n : ℝ) - (r : ℝ)) * f r) +
                ∑ r ∈ Finset.Ico 1 n, f r := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl (fun r _ => ?_)
            push_cast
            ring
          rw [hsplit]
          push_cast
          ring
      rw [houter, hdist1, hdist2, hborder, Nat.dist_self, ih, hRHS]
      ring

end Fabius
