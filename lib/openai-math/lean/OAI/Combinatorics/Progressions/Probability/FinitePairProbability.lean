import OAI.Combinatorics.Progressions.Estimates.ComplexFiniteMeans

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem good_pair_expect_ge {ι κ : Type*} (A : Finset ι) (B : Finset κ)
    (hA : A.Nonempty) (hB : B.Nonempty) (bad : ι → κ → Bool) {epsilon : ℝ}
    (hbad : (∑ a ∈ A, ∑ b ∈ B, if bad a b then (1 : ℝ) else 0) ≤
      epsilon * (A.card : ℝ) * B.card) :
    1 - epsilon ≤ 𝔼 a ∈ A, 𝔼 b ∈ B, if bad a b then (0 : ℝ) else 1 := by
  have hAc : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hBc : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  have hbadmean : (𝔼 a ∈ A, 𝔼 b ∈ B, if bad a b then (1 : ℝ) else 0) ≤ epsilon := by
    simp_rw [Finset.expect_eq_sum_div_card]
    rw [← Finset.sum_div, div_div]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [hbad]
  have hpoint (a : ι) (b : κ) : (if bad a b then (0 : ℝ) else 1) =
      1 - (if bad a b then (1 : ℝ) else 0) := by
    cases bad a b <;> norm_num
  simp_rw [hpoint, Finset.expect_sub_distrib, Finset.expect_const hB, Finset.expect_const hA]
  linarith

end Erdos3

end

end OAI
