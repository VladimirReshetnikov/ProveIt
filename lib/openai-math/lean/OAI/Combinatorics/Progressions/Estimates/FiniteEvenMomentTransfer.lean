import OAI.Combinatorics.Progressions.Estimates.FiniteSectionPermutation

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

theorem finiteWeightedLp_le_of_nat_moment (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (q : ℕ) (hq : 0 < q) (f : X → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hm : (∑ x, w x * |f x| ^ q) ≤ B ^ q) :
    finiteWeightedLp w (q : ℝ) f ≤ B := by
  have hqr : 0 < (q : ℝ) := Nat.cast_pos.mpr hq
  apply (Real.rpow_le_rpow_iff (finiteWeightedLp_nonneg w hw _ f) hB hqr).mp
  rw [finiteWeightedLp_rpow_self w hw hqr f]
  simpa only [Real.rpow_natCast] using hm

theorem FiniteProbabilityWeights.even_moment_lp_le (p : FiniteProbabilityWeights X)
    (q : ℕ) (hq : 0 < q) (heven : Even q) (f : X → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hm : |p.mean (fun x => f x ^ q)| ≤ B ^ q) :
    finiteWeightedLp p.weight (q : ℝ) f ≤ B := by
  apply finiteWeightedLp_le_of_nat_moment p.weight p.nonneg q hq f B hB
  have he : (∑ x, p.weight x * |f x| ^ q) = p.mean (fun x => f x ^ q) := by
    simp only [heven.pow_abs, FiniteProbabilityWeights.mean]
  exact he.trans_le ((le_abs_self _).trans hm)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

theorem finiteWeightedLp_le_of_moment_error (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (q : ℕ) (hq : 0 < q) (f : X → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hm : (∑ x, w x * |f x| ^ q) ≤ B ^ q + 1) :
    finiteWeightedLp w (q : ℝ) f ≤ B + 1 := by
  apply finiteWeightedLp_le_of_nat_moment w hw q hq f (B + 1) (by linarith)
  apply hm.trans
  simpa only [one_pow] using pow_add_pow_le hB (by norm_num : (0 : ℝ) ≤ 1) hq.ne'

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

theorem finiteWeightedLp_transfer_even (w v : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (q : ℕ) (hq : 0 < q) (heven : Even q) (f : X → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hm : |∑ x, v x * f x ^ q| ≤ B ^ q)
    (herr : |(∑ x, w x * f x ^ q) - ∑ x, v x * f x ^ q| ≤ 1) :
    finiteWeightedLp w (q : ℝ) f ≤ B + 1 := by
  apply finiteWeightedLp_le_of_moment_error w hw q hq f B hB
  simp only [heven.pow_abs]
  have hdiff := (abs_le.mp herr).2
  have hmain := (le_abs_self (∑ x, v x * f x ^ q)).trans hm
  linarith

end Erdos3

end

end OAI
