import GRHArticle.ProgressionFree.PolynomialDeficitWeight
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# A positive convolution coefficient for the polynomial deficit replacement
-/

namespace GRHArticle.ProgressionFree

open scoped BigOperators

/-- A positive evaluation of the absolutely convergent weighted deficit series gives
a positive integer coefficient after convolution with any absolutely summable
nonnegative counting series of positive constant term. -/
theorem exists_positive_weighted_convolution {H : ℕ → ℕ} {J : ℕ → ℤ} {z : ℝ}
    (hz : 0 < z) (h0 : 0 < H 0)
    (hH : Summable (fun n ↦ (H n : ℝ) * z ^ n))
    (hJ : Summable (fun n ↦ ‖(J n : ℝ) * z ^ n‖))
    (hgain : 0 < ∑' n, (J n : ℝ) * z ^ n) :
    ∃ R, 1 ≤ ∑ k ∈ Finset.range (R + 1), (H k : ℤ) * J (R - k) := by
  let f : ℕ → ℝ := fun n ↦ (H n : ℝ) * z ^ n
  let g : ℕ → ℝ := fun n ↦ (J n : ℝ) * z ^ n
  have hfn (n : ℕ) : 0 ≤ f n := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hz.le _)
  have hf0 : 0 < f 0 := by
    simpa [f] using (Nat.cast_pos.mpr h0 : (0 : ℝ) < H 0)
  have hle : (∑ n ∈ ({0} : Finset ℕ), f n) ≤ ∑' n, f n :=
    hH.sum_le_tsum _ (fun n _ ↦ hfn n)
  have hF : 0 < ∑' n, f n := hf0.trans_le (by simpa using hle)
  have hHnorm : Summable (fun n ↦ ‖f n‖) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hfn _)] using hH
  have hprod : 0 < ∑' n, ∑ k ∈ Finset.range (n + 1), f k * g (n - k) := by
    rw [← tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hHnorm hJ]
    exact mul_pos hF hgain
  obtain ⟨R, hR⟩ : ∃ R, 0 < ∑ k ∈ Finset.range (R + 1), f k * g (R - k) := by
    by_contra! hn
    exact (not_lt_of_ge (tsum_nonpos hn)) hprod
  have hscale : (∑ k ∈ Finset.range (R + 1), f k * g (R - k)) =
      ((∑ k ∈ Finset.range (R + 1), (H k : ℤ) * J (R - k) : ℤ) : ℝ) * z ^ R := by
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    have hkR := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hp : z ^ k * z ^ (R - k) = z ^ R := by rw [← pow_add, Nat.add_sub_of_le hkR]
    dsimp [f, g]
    rw [← hp]
    ring
  rw [hscale] at hR
  have hpositive := pos_of_mul_pos_left hR (pow_nonneg hz.le R)
  exact ⟨R, Int.add_one_le_iff.mpr (Int.cast_pos.mp hpositive)⟩

/-- The signed coefficient of the explicit replacement series relative to the ternary rule. -/
noncomputable def polynomialDeficitDifference (n : ℕ) : ℤ := by
  classical
  exact (if n ∈ polynomialDeficitWitness then 1 else 0) -
    (if n ∈ greedyExponents then 1 else 0)

private theorem polynomialDeficitDifference_weight (z : ℝ) (n : ℕ) :
    (polynomialDeficitDifference n : ℝ) * z ^ n =
      (polynomialDeficitWitness : Set ℕ).indicator (fun d ↦ z ^ d) n -
      greedyExponents.indicator (fun d ↦ z ^ d) n := by
  classical
  by_cases hB : n ∈ polynomialDeficitWitness <;> by_cases hA : n ∈ greedyExponents <;>
    simp [polynomialDeficitDifference, hB, hA]

theorem summable_norm_polynomialDeficitDifference {z : ℝ} (hz₀ : 0 ≤ z) (hz₁ : z < 1) :
    Summable (fun n ↦ ‖(polynomialDeficitDifference n : ℝ) * z ^ n‖) := by
  classical
  refine (summable_geometric_of_lt_one hz₀ hz₁).of_nonneg_of_le
    (fun n ↦ norm_nonneg _) (fun n ↦ ?_)
  rw [polynomialDeficitDifference_weight]
  by_cases hB : n ∈ polynomialDeficitWitness <;> by_cases hA : n ∈ greedyExponents <;>
    simp [hB, hA, Real.norm_eq_abs, abs_of_nonneg hz₀,
      pow_nonneg hz₀ n]

/-- A positive convolution coefficient for the concrete witness at the fixed tilt. -/
theorem polynomialDeficitDifference_exists_positive_convolution {H : ℕ → ℕ}
    (h0 : 0 < H 0)
    (hH : Summable (fun n ↦ (H n : ℝ) * ((127 : ℝ) / 128) ^ n)) :
    ∃ R, 1 ≤ ∑ k ∈ Finset.range (R + 1), (H k : ℤ) * polynomialDeficitDifference (R - k) := by
  classical
  let z : ℝ := 127 / 128
  have hz₀ : 0 < z := by norm_num [z]
  have hz₁ : z < 1 := by norm_num [z]
  refine exists_positive_weighted_convolution hz₀ h0 hH
    (summable_norm_polynomialDeficitDifference hz₀.le hz₁) ?_
  let f : ℕ → ℝ := (polynomialDeficitWitness : Set ℕ).indicator (fun d ↦ z ^ d)
  let g : ℕ → ℝ := greedyExponents.indicator (fun d ↦ z ^ d)
  have hgeom := summable_geometric_of_lt_one hz₀.le hz₁
  have hbound (A : Set ℕ) (n : ℕ) :
      0 ≤ A.indicator (fun d ↦ z ^ d) n ∧ A.indicator (fun d ↦ z ^ d) n ≤ z ^ n := by
    by_cases h : n ∈ A <;> simp [h, pow_nonneg hz₀.le n]
  have hf : Summable f :=
    hgeom.of_nonneg_of_le (fun n ↦ (hbound _ n).1) (fun n ↦ (hbound _ n).2)
  have hg : Summable g :=
    hgeom.of_nonneg_of_le (fun n ↦ (hbound _ n).1) (fun n ↦ (hbound _ n).2)
  have hfin : (∑' n, f n) = ∑ n ∈ polynomialDeficitWitness, z ^ n := by
    rw [tsum_eq_sum (s := polynomialDeficitWitness)]
    · apply Finset.sum_congr rfl
      intro n hn
      simp [f, hn]
    · intro n hn
      simp [f, hn]
  simp_rw [polynomialDeficitDifference_weight]
  change 0 < (∑' n, (f n - g n))
  rw [hf.tsum_sub hg, hfin]
  exact (by norm_num : (0 : ℝ) < 3 / 200).trans polynomialDeficitWeight_gain_over_greedy

end GRHArticle.ProgressionFree
