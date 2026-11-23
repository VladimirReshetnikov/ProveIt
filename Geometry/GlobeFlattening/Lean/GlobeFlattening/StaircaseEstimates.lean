import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Summation by parts and increment comparison for the staircase series
-/

open Filter Finset
open scoped Topology

namespace GlobeFlattening

private theorem sum_weighted_increment_succ (e A : ℕ → ℝ) (h0 : A 0 = 0) (n : ℕ) :
    (∑ i ∈ range (n + 1), e i * (A (i + 1) - A i)) =
      e n * A (n + 1) + ∑ i ∈ range n, (e i - e (i + 1)) * A (i + 1) := by
  have h := sum_range_by_parts e (fun i => A (i + 1) - A i) (n + 1)
  simp only [smul_eq_mul, Nat.add_sub_cancel, sum_range_sub, h0, sub_zero] at h
  rw [h, sub_eq_add_neg, ← sum_neg_distrib]
  simp only [← neg_mul, neg_sub]

/-- Discrete summation by parts retains the limit of the boundary term. -/
theorem tsum_weighted_increment {e A : ℕ → ℝ} {L : ℝ} (h0 : A 0 = 0)
    (hs : Summable (fun n => (e n - e (n + 1)) * A (n + 1)))
    (ht : Summable (fun n => e n * (A (n + 1) - A n)))
    (hend : Tendsto (fun n => e n * A (n + 1)) atTop (𝓝 L)) :
    (∑' n, e n * (A (n + 1) - A n)) = L + ∑' n, (e n - e (n + 1)) * A (n + 1) := by
  have hleft := ht.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  simp only [Function.comp_def, sum_weighted_increment_succ e A h0] at hleft
  exact tendsto_nhds_unique hleft (hend.add hs.hasSum.tendsto_sum_nat)

/-- An absolute termwise difference bound passes to the corresponding difference of sums. -/
private theorem abs_tsum_sub_le_of_termwise {f g u v : ℕ → ℝ}
    (hf : Summable f) (hg : Summable g) (hu : Summable u) (hv : Summable v)
    (h : ∀ n, |f n - g n| ≤ u n - v n) :
    |(∑' n, f n) - ∑' n, g n| ≤ (∑' n, u n) - ∑' n, v n := by
  rw [← hf.tsum_sub hg, ← hu.tsum_sub hv]
  exact tsum_of_norm_bounded (f := fun n => f n - g n) (hu.sub hv).hasSum h

/-- Multiplying a summably bounded sequence by a uniformly bounded one preserves summability. -/
theorem summable_mul_of_abs_le {b c d : ℕ → ℝ} {C : ℝ} (hb : Summable b)
    (hc : ∀ n, |c n| ≤ b n) (hd : ∀ n, |d n| ≤ C) :
    Summable (fun n => c n * d n) := by
  refine (hb.mul_right C).of_norm_bounded fun n => ?_
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hc n) (hd n) (abs_nonneg _) ((abs_nonneg _).trans (hc n))

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
  refine (abs_tsum_sub_le_of_termwise (hs y) (hs x) (ht y) (ht x) fun n => ?_).trans (le_abs_self _)
  have hdelta := sub_nonneg.mpr (hmono n h)
  have hcomp : |f n (X n y) - f n (X n x)| ≤ X n y - X n x := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul, abs_of_nonneg hdelta] using
      (hlip n).dist_le_mul (X n y) (X n x)
  rw [← mul_sub, abs_mul, ← mul_sub]
  exact mul_le_mul (ha n) hcomp (abs_nonneg _) (hb₀ n)

end GlobeFlattening
