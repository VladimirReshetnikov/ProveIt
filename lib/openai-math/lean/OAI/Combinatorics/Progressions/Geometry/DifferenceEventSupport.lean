-- Modified for ProveIt: added `import OAI.Compat.*` lines (backported names); see lib/openai-math/README.md.
import OAI.Combinatorics.Progressions.Probability.DifferenceEventProbability
import OAI.Compat.Core

namespace OAI

section

namespace Erdos3.CyclicCrootSisask

open scoped BigOperators Pointwise

variable {N : ℕ}

theorem differenceEventProbability_self_zero (A : Finset (ZMod N)) (hA : A.Nonempty) :
    differenceEventProbability A A (A - A) 0 = 1 := by
  unfold differenceEventProbability
  have hone : ∀ a ∈ A, ∀ b ∈ A, realSetIndicator (A - A) (a - b + 0) = 1 := by
    intro a ha b hb
    simp only [add_zero, realSetIndicator, ite_eq_left (Finset.mem_sub.mpr ⟨a, ha, b, hb, rfl⟩)]
  calc
    (𝔼 a ∈ A, 𝔼 b ∈ A, realSetIndicator (A - A) (a - b + 0)) =
        𝔼 _a ∈ A, 𝔼 _b ∈ A, (1 : ℝ) := by
      apply Finset.expect_congr rfl
      intro a ha
      apply Finset.expect_congr rfl
      intro b hb
      exact hone a ha b hb
    _ = 1 := by rw [Finset.expect_const hA, Finset.expect_const hA]

theorem exists_difference_event_of_probability_pos
    (A₁ A₂ K : Finset (ZMod N)) (t : ZMod N)
    (h : 0 < differenceEventProbability A₁ A₂ K t) :
    ∃ a ∈ A₁, ∃ b ∈ A₂, a - b + t ∈ K := by
  classical
  by_contra hnone
  push Not at hnone
  have hz : differenceEventProbability A₁ A₂ K t = 0 := by
    unfold differenceEventProbability
    calc
      (𝔼 a ∈ A₁, 𝔼 b ∈ A₂, realSetIndicator K (a - b + t)) =
          𝔼 _a ∈ A₁, 𝔼 _b ∈ A₂, (0 : ℝ) := by
        apply Finset.expect_congr rfl
        intro a ha
        apply Finset.expect_congr rfl
        intro b hb
        simp only [realSetIndicator, ite_eq_right (hnone a ha b hb)]
      _ = 0 := by simp
  linarith

theorem mem_fourfold_difference_of_probability_pos (A : Finset (ZMod N)) (t : ZMod N)
    (h : 0 < differenceEventProbability A A (A - A) t) : t ∈ 2 • A - 2 • A := by
  obtain ⟨a, ha, b, hb, hab⟩ := exists_difference_event_of_probability_pos A A (A - A) t h
  obtain ⟨c, hc, d, hd, hcd⟩ := Finset.mem_sub.mp hab
  have htwo : 2 • A = A + A := two_nsmul A
  rw [htwo]
  apply Finset.mem_sub.mpr
  refine ⟨c + b, Finset.mem_add.mpr ⟨c, hc, b, hb, rfl⟩,
    d + a, Finset.mem_add.mpr ⟨d, hd, a, ha, rfl⟩, ?_⟩
  calc
    (c + b) - (d + a) = (c - d) - (a - b) := by abel
    _ = (a - b + t) - (a - b) := by rw [hcd]
    _ = t := by abel

end Erdos3.CyclicCrootSisask

end

end OAI
