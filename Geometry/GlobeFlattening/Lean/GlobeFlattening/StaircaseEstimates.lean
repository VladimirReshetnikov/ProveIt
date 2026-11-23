import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Ring

/-!
# Summation by parts and increment comparison for the staircase series
-/

open Filter Finset
open scoped Topology

namespace GlobeFlattening

/-- Discrete summation by parts retains the limit of the boundary term. -/
theorem tsum_weighted_increment {e A : ℕ → ℝ} {L : ℝ} (h0 : A 0 = 0)
    (hs : Summable (fun n => (e n - e (n + 1)) * A (n + 1)))
    (ht : Summable (fun n => (A (n + 1) - A n) * e n))
    (hend : Tendsto (fun n => e n * A n) atTop (𝓝 L)) :
    (∑' n, (A (n + 1) - A n) * e n) = L + ∑' n, (e n - e (n + 1)) * A (n + 1) := by
  have hstep (n : ℕ) :
      (A (n + 1) - A n) * e n - (e n - e (n + 1)) * A (n + 1) =
        e (n + 1) * A (n + 1) - e n * A n := by ring
  have h := (ht.hasSum.sub hs.hasSum).tendsto_sum_nat
  simp only [hstep, sum_range_sub (fun n => e n * A n), h0, mul_zero, sub_zero] at h
  exact eq_add_of_sub_eq (tendsto_nhds_unique h hend)

/-- A summable product majorant bounds the difference of weighted sums. -/
theorem abs_sub_le_of_hasSum_weighted {a b c f g : ℕ → ℝ} {F G C : ℝ}
    (hf : HasSum (fun n => a n * f n) F) (hg : HasSum (fun n => a n * g n) G)
    (hC : HasSum (fun n => b n * c n) C)
    (ha : ∀ n, |a n| ≤ b n) (hd : ∀ n, |f n - g n| ≤ c n) : |F - G| ≤ C := by
  refine (hf.sub hg).norm_le_of_bounded hC fun n => ?_
  rw [← mul_sub]
  exact norm_mul_le_of_le (ha n) (hd n)

/-- Multiplying a summably bounded sequence by a uniformly bounded one preserves summability. -/
theorem summable_mul_of_abs_le {b c d : ℕ → ℝ} {C : ℝ} (hb : Summable b)
    (hc : ∀ n, |c n| ≤ b n) (hd : ∀ n, |d n| ≤ C) :
    Summable (fun n => c n * d n) :=
  (hb.mul_right C).of_norm_bounded (fun n => norm_mul_le_of_le (hc n) (hd n))

/-- Absolute increments of a weighted sum of Lipschitz transforms are
bounded by the corresponding increments of the monotone majorant. -/
theorem abs_tsum_weighted_comp_sub_le {a b : ℕ → ℝ} {X f : ℕ → ℝ → ℝ} {A B : ℝ}
    (hb : Summable b) (ha : ∀ n, |a n| ≤ b n) (hmono : ∀ n, Monotone (X n))
    (hX : ∀ n x, |X n x| ≤ B) (hlip : ∀ n, LipschitzWith 1 (f n))
    (hf : ∀ n x, |f n (X n x)| ≤ A) (x y : ℝ) :
    |(∑' n, a n * f n (X n y)) - ∑' n, a n * f n (X n x)| ≤
      |(∑' n, b n * X n y) - ∑' n, b n * X n x| := by
  have hb₀ (n : ℕ) : 0 ≤ b n := (abs_nonneg _).trans (ha n)
  have hs (t : ℝ) := summable_mul_of_abs_le hb ha (fun n => hf n t)
  have ht (t : ℝ) := summable_mul_of_abs_le hb
    (fun n => (abs_of_nonneg (hb₀ n)).le) (fun n => hX n t)
  wlog h : x ≤ y generalizing x y
  · rw [abs_sub_comm (∑' n, a n * f n (X n y)), abs_sub_comm (∑' n, b n * X n y)]
    exact this y x (le_of_not_ge h)
  have hdiff : HasSum (fun n => b n * (X n y - X n x))
      ((∑' n, b n * X n y) - ∑' n, b n * X n x) := by
    simpa only [mul_sub] using (ht y).hasSum.sub (ht x).hasSum
  refine (abs_sub_le_of_hasSum_weighted (hs y).hasSum (hs x).hasSum hdiff ha fun n => ?_).trans
    (le_abs_self _)
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul, abs_of_nonneg (sub_nonneg.mpr (hmono n h))]
    using (hlip n).dist_le_mul (X n y) (X n x)

end GlobeFlattening
