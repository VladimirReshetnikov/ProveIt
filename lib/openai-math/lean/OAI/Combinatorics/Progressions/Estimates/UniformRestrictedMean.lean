import OAI.Combinatorics.Progressions.Probability.IntervalDivisorProbability

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem uniformFinset_restricted_mean {Ω : Type*} (S : Finset Ω) (hS : S.Nonempty)
    (P : Ω → Prop) [DecidablePred P] (f : Ω → ℝ) :
    (FiniteProbabilityWeights.uniformFinset S hS).mean (fun z => if P z.val then f z.val else 0) =
      ((S.filter P).card : ℝ) / S.card * (𝔼 z : S.filter P, f z.val) := by
  classical
  rw [FiniteProbabilityWeights.uniformFinset_mean S hS (fun z => if P z then f z else 0)]
  rw [Finset.expect_eq_sum_div_card]
  calc
    (∑ z ∈ S, if P z then f z else 0) / (S.card : ℝ) =
        (∑ z : S.filter P, f z.val) / (S.card : ℝ) := by
      rw [Finset.sum_coe_sort, Finset.sum_filter]
    _ = ((S.filter P).card : ℝ) / S.card * (𝔼 z : S.filter P, f z.val) := by
      have h := Fintype.card_mul_expect (fun z : S.filter P => f z.val)
      rw [Fintype.card_coe] at h
      rw [← h]
      ring

end Erdos3

end

end OAI
