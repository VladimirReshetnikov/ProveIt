/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Probability.IntervalDivisorProbability

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def integerBoxUniformWeights {J : Type*} [Fintype J] [DecidableEq J]
    (lo hi : J → ℤ) (hlen : ∀ j, lo j < hi j) :
    FiniteProbabilityWeights (∀ j, Finset.Ico (lo j) (hi j)) :=
  FiniteProbabilityWeights.pi (fun j => intervalUniformWeights (lo j) (hi j) (hlen j))

theorem integer_box_divisor_probability {J : Type*} [Fintype J] [DecidableEq J]
    (lo hi : J → ℤ) (hlen : ∀ j, lo j < hi j) (m : ℤ) (hm : 0 < m) (v : J → ℤ) :
    (integerBoxUniformWeights lo hi hlen).eventProbability
        (fun y => ∀ j, m ∣ (y j : ℤ) - v j) ≤
      ∏ j, (1 / (m : ℝ) + 1 / ((hi j - lo j : ℤ) : ℝ)) := by
  rw [integerBoxUniformWeights, FiniteProbabilityWeights.eventProbability_pi
    (fun j => intervalUniformWeights (lo j) (hi j) (hlen j))
    (fun j (y : Finset.Ico (lo j) (hi j)) => m ∣ (y : ℤ) - v j)]
  apply Finset.prod_le_prod₀
  · intro j _
    exact FiniteProbabilityWeights.eventProbability_nonneg _ _
  · intro j _
    exact interval_divisor_probability (lo j) (hi j) m (v j) (hlen j) hm

theorem integer_box_pair_divisor_probability {J : Type*} [Fintype J] [DecidableEq J]
    (lo hi : J → ℤ) (hlen : ∀ j, lo j < hi j) (m : ℤ) (hm : 0 < m) :
    ((integerBoxUniformWeights lo hi hlen).prod (integerBoxUniformWeights lo hi hlen)).eventProbability
        (fun xy => ∀ j, m ∣ (xy.2 j : ℤ) - (xy.1 j : ℤ)) ≤
      ∏ j, (1 / (m : ℝ) + 1 / ((hi j - lo j : ℤ) : ℝ)) := by
  unfold FiniteProbabilityWeights.eventProbability
  rw [FiniteProbabilityWeights.mean_prod]
  apply (FiniteProbabilityWeights.mean_mono _ ?_).trans_eq (FiniteProbabilityWeights.mean_const _ _)
  intro x
  exact integer_box_divisor_probability lo hi hlen m hm (fun j => (x j : ℤ))

theorem integer_box_pair_divisor_probability_of_lengths {J : Type*}
    [Fintype J] [DecidableEq J] (lo hi : J → ℤ) (hlen : ∀ j, lo j < hi j)
    (m : ℤ) (hm : 0 < m) {L : ℝ} (hL : 0 < L)
    (hside : ∀ j, L ≤ ((hi j - lo j : ℤ) : ℝ)) :
    ((integerBoxUniformWeights lo hi hlen).prod (integerBoxUniformWeights lo hi hlen)).eventProbability
        (fun xy => ∀ j, m ∣ (xy.2 j : ℤ) - (xy.1 j : ℤ)) ≤
      (1 / (m : ℝ) + 1 / L) ^ Fintype.card J := by
  apply (integer_box_pair_divisor_probability lo hi hlen m hm).trans
  calc
    _ ≤ ∏ _j : J, (1 / (m : ℝ) + 1 / L) := by
      apply Finset.prod_le_prod₀
      · intro j _
        have hmR : (0 : ℝ) < m := by exact_mod_cast hm
        have hj : (0 : ℝ) < ((hi j - lo j : ℤ) : ℝ) := hL.trans_le (hside j)
        positivity
      · intro j _
        exact add_le_add le_rfl (one_div_le_one_div_of_le hL (hside j))
    _ = _ := by simp

end Erdos3

end

end OAI
