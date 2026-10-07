import OAI.Combinatorics.Progressions.Probability.FiniteConditionedMass

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

theorem eventProbability_or_le {Ω : Type*} [Fintype Ω]
    (p : FiniteProbabilityWeights Ω) (E F : Ω → Prop) :
    p.eventProbability (fun x => E x ∨ F x) ≤ p.eventProbability E + p.eventProbability F := by
  classical
  unfold eventProbability
  calc
    _ ≤ p.mean (fun x => (if E x then 1 else 0) + (if F x then 1 else 0)) := by
      apply p.mean_mono
      intro x
      by_cases hE : E x <;> by_cases hF : F x <;> simp [hE, hF]
    _ = _ := p.mean_add _ _

end Erdos3.FiniteProbabilityWeights

end

end OAI
