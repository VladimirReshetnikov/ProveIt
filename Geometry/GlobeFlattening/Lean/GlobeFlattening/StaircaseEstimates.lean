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

/-- Successive drops of a decreasing sequence tending to zero sum to its initial value. -/
theorem hasSum_antitone_drop {e : ℕ → ℝ} (he : Antitone e)
    (hzero : Tendsto e atTop (𝓝 0)) : HasSum (fun n => e n - e (n + 1)) (e 0) := by
  refine (hasSum_iff_tendsto_nat_of_nonneg (fun n => sub_nonneg.mpr (he (Nat.le_succ n))) _).2 ?_
  have ht : Tendsto (fun n => e 0 - e n) atTop (𝓝 (e 0)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hzero
  simpa only [sum_range_sub'] using ht

/-- An absolute termwise difference bound passes to the corresponding difference of sums. -/
theorem abs_tsum_sub_le_of_termwise {f g u v : ℕ → ℝ}
    (hf : Summable f) (hg : Summable g) (hu : Summable u) (hv : Summable v)
    (h : ∀ n, |f n - g n| ≤ u n - v n) :
    |(∑' n, f n) - ∑' n, g n| ≤ (∑' n, u n) - ∑' n, v n := by
  rw [← hf.tsum_sub hg, ← hu.tsum_sub hv]
  exact tsum_of_norm_bounded (f := fun n => f n - g n) (hu.sub hv).hasSum h

/-- Multiplying a summably bounded real sequence by a uniformly bounded one preserves summability. -/
theorem summable_mul_of_abs_le {b c d : ℕ → ℝ} {C : ℝ} (hb : Summable b)
    (hc : ∀ n, |c n| ≤ C) (hd : ∀ n, |d n| ≤ b n) :
    Summable (fun n => c n * d n) := by
  refine (hb.mul_left C).of_norm_bounded fun n => ?_
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hc n) (hd n) (abs_nonneg _) ((abs_nonneg _).trans (hc n))

theorem summable_add_cos_mul {ξ b a Y : ℕ → ℝ} {A : ℝ}
    (hb : Summable b) (hξ : ∀ n, |ξ n| ≤ b n) (ha : ∀ n, |a n| ≤ A) :
    Summable (fun n => (a n + Real.cos (Y n)) * ξ n) :=
  summable_mul_of_abs_le hb
    (fun n => (abs_add_le _ _).trans (add_le_add (ha n) (Real.abs_cos_le_one _))) hξ

/-- Compare absolute increments of two series using an ordered bound on each term. -/
private theorem abs_tsum_increment_le {f g : ℕ → ℝ → ℝ}
    (hf : ∀ x, Summable (fun n => f n x)) (hg : ∀ x, Summable (fun n => g n x))
    (hstep : ∀ x y : ℝ, x ≤ y → ∀ n, |f n y - f n x| ≤ g n y - g n x)
    (x y : ℝ) :
    |(∑' n, f n y) - ∑' n, f n x| ≤ |(∑' n, g n y) - ∑' n, g n x| := by
  wlog h : x ≤ y generalizing x y
  · rw [abs_sub_comm (∑' n, f n y), abs_sub_comm (∑' n, g n y)]
    exact this y x (le_of_not_ge h)
  exact (abs_tsum_sub_le_of_termwise (hf y) (hf x) (hg y) (hg x) (hstep x y h)).trans
    (le_abs_self _)

/-- Changes of latitude are bounded by increments of the monotone comparison series. -/
theorem abs_tsum_cos_sub_le_of_bounded {ξ b a : ℕ → ℝ} {Y : ℕ → ℝ → ℝ} {A B : ℝ}
    (hb : Summable b) (hξ : ∀ n, |ξ n| ≤ b n) (ha : ∀ n, |a n| ≤ A)
    (hmono : ∀ n, Monotone (Y n)) (hY : ∀ n y, |Y n y| ≤ B) (y y' : ℝ) :
    |(∑' n, (a n + Real.cos (Y n y')) * ξ n) - ∑' n, (a n + Real.cos (Y n y)) * ξ n| ≤
      |(∑' n, b n * Y n y') - ∑' n, b n * Y n y| := by
  have hnonneg (n : ℕ) : 0 ≤ b n := (abs_nonneg _).trans (hξ n)
  have hf (t : ℝ) : Summable (fun n => (a n + Real.cos (Y n t)) * ξ n) :=
    summable_add_cos_mul hb hξ ha
  have hg (t : ℝ) : Summable (fun n => b n * Y n t) := by
    simpa only [mul_comm] using
      summable_mul_of_abs_le hb (fun n => hY n t) (fun n => (abs_of_nonneg (hnonneg n)).le)
  refine abs_tsum_increment_le hf hg (fun x x' h n => ?_) y y'
  have hdelta := sub_nonneg.mpr (hmono n h)
  rw [← sub_mul, add_sub_add_left_eq_sub, abs_mul, ← mul_sub, mul_comm (b n)]
  exact mul_le_mul ((Real.abs_cos_sub_cos_le _ _).trans_eq (abs_of_nonneg hdelta))
    (hξ n) (abs_nonneg _) hdelta

/-- Increasing summands with smaller nonnegative weights have smaller absolute increments. -/
theorem abs_tsum_weighted_sub_le {a b : ℕ → ℝ} {X : ℕ → ℝ → ℝ} {B : ℝ}
    (hb : Summable b) (ha : ∀ n, 0 ≤ a n ∧ a n ≤ b n)
    (hmono : ∀ n, Monotone (X n)) (hX : ∀ n x, |X n x| ≤ B) (x x' : ℝ) :
    |(∑' n, a n * X n x') - ∑' n, a n * X n x| ≤
      |(∑' n, b n * X n x') - ∑' n, b n * X n x| := by
  have hs (c : ℕ → ℝ) (hc : ∀ n, |c n| ≤ b n) (t : ℝ) :
      Summable (fun n => c n * X n t) := by
    simpa only [mul_comm] using summable_mul_of_abs_le hb (fun n => hX n t) hc
  have hf := hs a (fun n => (abs_of_nonneg (ha n).1).le.trans (ha n).2)
  have hg := hs b (fun n => (abs_of_nonneg ((ha n).1.trans (ha n).2)).le)
  refine abs_tsum_increment_le hf hg (fun y y' h n => ?_) x x'
  have hdelta := sub_nonneg.mpr (hmono n h)
  rw [← mul_sub, abs_of_nonneg (mul_nonneg (ha n).1 hdelta), ← mul_sub]
  exact mul_le_mul_of_nonneg_right (ha n).2 hdelta

end GlobeFlattening
