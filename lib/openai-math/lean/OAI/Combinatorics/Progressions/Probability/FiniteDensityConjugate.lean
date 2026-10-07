import OAI.Combinatorics.Progressions.Estimates.FiniteSectionPermutation

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X : Type*} [Fintype X]

theorem conjugate_lp_exp_bound (μ : FiniteProbabilityWeights X) (q : ℝ) (hq : 1 < q)
    (f : X → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hfcap : ∀ x, f x ≤ Real.exp q)
    (hm : μ.mean f ≤ 1) :
    finiteWeightedLp μ.weight (q / (q - 1)) f ≤ Real.exp 1 := by
  let s := q / (q - 1)
  have hq1 : 0 < q - 1 := by linarith
  have hs : 0 < s := div_pos (by linarith) hq1
  have hs1 : 0 ≤ s - 1 := by
    dsimp [s]
    have h : 1 ≤ q / (q - 1) := (le_div_iff₀ hq1).mpr (by linarith)
    linarith
  have he : q * (s - 1) = s := by
    dsimp [s]
    field_simp
    ring
  have hp (x : X) : |f x| ^ s ≤ (Real.exp 1) ^ s * f x := by
    rw [abs_of_nonneg (hf0 x)]
    calc
      f x ^ s = f x ^ (s - 1) * f x := by
        simpa only [sub_add_cancel] using
          Real.rpow_add_one' (hf0 x) (show s - 1 + 1 ≠ 0 by linarith)
      _ ≤ (Real.exp q) ^ (s - 1) * f x :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (hf0 x) (hfcap x) hs1) (hf0 x)
      _ = (Real.exp 1) ^ s * f x := by
        rw [← Real.exp_mul, he, ← Real.exp_mul, one_mul]
  apply (Real.rpow_le_rpow_iff (finiteWeightedLp_nonneg μ.weight μ.nonneg s f)
    (Real.exp_pos 1).le hs).mp
  rw [finiteWeightedLp_rpow_self μ.weight μ.nonneg hs f]
  calc
    (∑ x, μ.weight x * |f x| ^ s) ≤ ∑ x, μ.weight x * ((Real.exp 1) ^ s * f x) :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hp x) (μ.nonneg x))
    _ = (Real.exp 1) ^ s * μ.mean f := by
      unfold mean
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ ≤ (Real.exp 1) ^ s := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg (Real.exp_pos 1).le s)

end Erdos3.FiniteProbabilityWeights

end

end OAI
