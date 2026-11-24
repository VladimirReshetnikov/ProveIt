import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Summation by parts and increment comparison for the staircase series
-/

open Filter Finset
open scoped Topology

namespace GlobeFlattening

/-- The weighted increments converge to the boundary limit plus the correction. -/
theorem tendsto_sum_weighted_increment {e A : ℕ → ℝ} {L C : ℝ}
    (hs : HasSum (fun n => (e n - e (n + 1)) * A n) C)
    (hend : Tendsto (fun n => A n * e n) atTop (𝓝 L)) :
    Tendsto (fun N => (∑ n ∈ range N, (A (n + 1) - A n) * e (n + 1)) + A 0 * e 0)
      atTop (𝓝 (L + C)) := by
  refine (hend.add hs.tendsto_sum_nat).congr' (Eventually.of_forall fun N => ?_)
  have htel := sum_range_sub (fun n => A n * e n) N
  simp only [sub_mul, sum_sub_distrib, mul_comm (e _) (A _)] at htel ⊢
  linarith only [htel]

/-- Compare the limits of weighted increments with the increments of their monotone majorant. -/
theorem abs_sub_le_of_tendsto_weighted_comp {a b : ℕ → ℝ} {X f : ℕ → ℝ → ℝ} {A B : ℝ}
    (hb : ∀ t, Summable (fun n => b n * X n t)) (ha : ∀ n, |a n| ≤ b n)
    (hmono : ∀ n, Monotone (X n)) (hlip : ∀ n x y, |f n y - f n x| ≤ |y - x|)
    (x y : ℝ)
    (hx : Tendsto (fun N => ∑ n ∈ range N, a n * f n (X n x)) atTop (𝓝 A))
    (hy : Tendsto (fun N => ∑ n ∈ range N, a n * f n (X n y)) atTop (𝓝 B)) :
    |B - A| ≤ |(∑' n, b n * X n y) - ∑' n, b n * X n x| := by
  wlog h : x ≤ y generalizing x y A B
  · simpa only [abs_sub_comm] using this y x hy hx (le_of_not_ge h)
  have hm := ((hb y).hasSum.sub (hb x).hasSum).tendsto_sum_nat
  refine (le_of_tendsto_of_tendsto' (hy.sub hx).norm hm fun N => ?_).trans (le_abs_self _)
  simp only [← sum_sub_distrib, ← mul_sub]
  exact norm_sum_le_of_le _ fun n _ => norm_mul_le_of_le (ha n) <| by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (hmono n h))] using hlip n (X n x) (X n y)

end GlobeFlattening
