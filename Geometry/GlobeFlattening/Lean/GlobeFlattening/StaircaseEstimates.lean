import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic.Ring

/-!
# Summation by parts and increment comparison for the staircase series
-/

open Filter Finset
open scoped Topology

namespace GlobeFlattening

/-- Summation by parts retains the limit of the boundary product. -/
theorem tsum_weighted_increment {e A : ℕ → ℝ} {L : ℝ}
    (hs : Summable (fun n => (e n - e (n + 1)) * A n))
    (ht : Summable (fun n => (A (n + 1) - A n) * e (n + 1)))
    (hend : Tendsto (fun n => e n * A n) atTop (𝓝 L)) :
    A 0 * e 0 + (∑' n, (A (n + 1) - A n) * e (n + 1)) =
      L + ∑' n, (e n - e (n + 1)) * A n := by
  have hstep (n : ℕ) :
      (A (n + 1) - A n) * e (n + 1) - (e n - e (n + 1)) * A n =
        e (n + 1) * A (n + 1) - e n * A n := by ring
  have h := (ht.hasSum.sub hs.hasSum).tendsto_sum_nat
  simp only [hstep, sum_range_sub (fun n => e n * A n)] at h
  linarith only [tendsto_nhds_unique h (hend.sub_const _)]

/-- Absolute increments of a weighted sum of Lipschitz transforms are
bounded by the corresponding increments of the monotone majorant. -/
theorem abs_tsum_weighted_comp_sub_le {a b : ℕ → ℝ} {X f : ℕ → ℝ → ℝ}
    (hb : ∀ t, Summable (fun n => b n * X n t)) (ha : ∀ n, |a n| ≤ b n)
    (hmono : ∀ n, Monotone (X n)) (hlip : ∀ n x y, |f n y - f n x| ≤ |y - x|)
    (x y : ℝ) (hx : Summable (fun n => a n * f n (X n x))) (hy : Summable (fun n => a n * f n (X n y))) :
    |(∑' n, a n * f n (X n y)) - ∑' n, a n * f n (X n x)| ≤
      |(∑' n, b n * X n y) - ∑' n, b n * X n x| := by
  wlog h : x ≤ y generalizing x y
  · simpa only [abs_sub_comm] using this y x hy hx (le_of_not_ge h)
  refine ((hy.hasSum.sub hx.hasSum).norm_le_of_bounded
    ((hb y).hasSum.sub (hb x).hasSum) fun n => ?_).trans (le_abs_self _)
  rw [← mul_sub, ← mul_sub]
  refine norm_mul_le_of_le (ha n) ?_
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (hmono n h))] using hlip n (X n x) (X n y)

end GlobeFlattening
