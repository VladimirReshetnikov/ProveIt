/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Probability.FiniteConditionedMass

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem pi_weight_le {J : Type*} [Fintype J] [DecidableEq J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)]
    (p q : ∀ j, FiniteProbabilityWeights (Ω j)) (C : J → ℝ)
    (hw : ∀ j x, (p j).weight x ≤ C j * (q j).weight x) (x : ∀ j, Ω j) :
    (pi p).weight x ≤ (∏ j, C j) * (pi q).weight x := by
  change (∏ j, (p j).weight (x j)) ≤ (∏ j, C j) * (∏ j, (q j).weight (x j))
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod₀ (fun j _ => (p j).nonneg (x j)) (fun j _ => hw j (x j))

theorem pi_eventProbability_le {J : Type*} [Fintype J] [DecidableEq J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)]
    (p q : ∀ j, FiniteProbabilityWeights (Ω j)) (C : J → ℝ)
    (hw : ∀ j x, (p j).weight x ≤ C j * (q j).weight x) (E : (∀ j, Ω j) → Prop) :
    (pi p).eventProbability E ≤ (∏ j, C j) * (pi q).eventProbability E :=
  eventProbability_le_of_weight_le _ _ _ (pi_weight_le p q C hw) E

end Erdos3.FiniteProbabilityWeights

end

end OAI
