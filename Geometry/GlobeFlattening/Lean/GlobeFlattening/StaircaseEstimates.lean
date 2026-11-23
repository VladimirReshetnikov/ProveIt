import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Ring

/-!
# Summation by parts and increment comparison for the staircase series
-/

open Filter Finset
open scoped Topology

namespace GlobeFlattening

/-- Summation by parts with the sequence centered at `z`. -/
theorem tsum_weighted_increment_centered {e A : ℕ → ℝ} {z L : ℝ}
    (hs : Summable (fun n => (e n - e (n + 1)) * (A n - z)))
    (ht : Summable (fun n => (A (n + 1) - A n) * e (n + 1)))
    (hend : Tendsto (fun n => e n * (A n - z)) atTop (𝓝 L)) :
    A 0 * e 0 + (∑' n, (A (n + 1) - A n) * e (n + 1)) - z * e 0 =
      L + ∑' n, (e n - e (n + 1)) * (A n - z) := by
  have hstep (n : ℕ) :
      (A (n + 1) - A n) * e (n + 1) - (e n - e (n + 1)) * (A n - z) =
        e (n + 1) * (A (n + 1) - z) - e n * (A n - z) := by ring
  have h := (ht.hasSum.sub hs.hasSum).tendsto_sum_nat
  simp only [hstep, sum_range_sub (fun n => e n * (A n - z))] at h
  linarith only [tendsto_nhds_unique h (hend.sub_const _)]

/-- Absolute increments of a weighted sum of Lipschitz transforms are
bounded by the corresponding increments of the monotone majorant. -/
theorem abs_tsum_weighted_comp_sub_le {a b : ℕ → ℝ} {X f : ℕ → ℝ → ℝ} {A B : ℝ}
    (hb : Summable b) (ha : ∀ n, |a n| ≤ b n) (hmono : ∀ n, Monotone (X n))
    (hX : ∀ n x, |X n x| ≤ B) (hlip : ∀ n, LipschitzWith 1 (f n))
    (hf : ∀ n x, |f n (X n x)| ≤ A) (x y : ℝ) :
    |(∑' n, a n * f n (X n y)) - ∑' n, a n * f n (X n x)| ≤
      |(∑' n, b n * X n y) - ∑' n, b n * X n x| := by
  have hb₀ (n : ℕ) : 0 ≤ b n := (abs_nonneg _).trans (ha n)
  have hs (t : ℝ) : Summable (fun n => a n * f n (X n t)) :=
    (hb.mul_right A).of_norm_bounded (fun n => norm_mul_le_of_le (ha n) (hf n t))
  have ht (t : ℝ) : Summable (fun n => b n * X n t) :=
    (hb.mul_right B).of_norm_bounded (fun n => norm_mul_le_of_le (abs_of_nonneg (hb₀ n)).le (hX n t))
  wlog h : x ≤ y generalizing x y
  · simpa only [abs_sub_comm] using this y x (le_of_not_ge h)
  refine (((hs y).hasSum.sub (hs x).hasSum).norm_le_of_bounded
    ((ht y).hasSum.sub (ht x).hasSum) fun n => ?_).trans (le_abs_self _)
  rw [← mul_sub, ← mul_sub]
  refine norm_mul_le_of_le (ha n) ?_
  simpa only [Real.dist_eq, Real.norm_eq_abs, NNReal.coe_one, one_mul,
    abs_of_nonneg (sub_nonneg.mpr (hmono n h))] using (hlip n).dist_le_mul (X n y) (X n x)

end GlobeFlattening
