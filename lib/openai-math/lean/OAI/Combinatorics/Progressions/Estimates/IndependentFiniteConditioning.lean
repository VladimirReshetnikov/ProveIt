/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Probability.FiniteConditionedMass

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem ext_weight {Ω : Type*} [Fintype Ω] {p q : FiniteProbabilityWeights Ω}
    (h : p.weight = q.weight) : p = q := by
  cases p
  cases q
  cases h
  rfl

theorem mass_inter_pos_of_condition {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (p : FiniteProbabilityWeights Ω) (G R : Finset Ω) (hG : 0 < p.mass G)
    (hR : 0 < (p.condition G hG).mass R) : 0 < p.mass (G ∩ R) := by
  rw [condition_mass] at hR
  exact (div_pos_iff_of_pos_right hG).mp hR

theorem condition_condition {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (p : FiniteProbabilityWeights Ω) (G R : Finset Ω) (hG : 0 < p.mass G)
    (hR : 0 < (p.condition G hG).mass R) :
    (p.condition G hG).condition R hR =
      p.condition (G ∩ R) (mass_inter_pos_of_condition p G R hG hR) := by
  have hw : ((p.condition G hG).condition R hR).weight =
      (p.condition (G ∩ R) (mass_inter_pos_of_condition p G R hG hR)).weight := by
    funext x
    change (if x ∈ R then (if x ∈ G then p.weight x else 0) / p.mass G else 0) /
        (p.condition G hG).mass R =
      (if x ∈ G ∩ R then p.weight x else 0) / p.mass (G ∩ R)
    rw [condition_mass]
    by_cases hxG : x ∈ G <;> by_cases hxR : x ∈ R <;>
      simp [hxG, hxR, div_div_div_cancel_right₀ hG.ne']
  exact ext_weight hw

theorem uniform_condition_condition_mean {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    [Nonempty Ω] (G R : Finset Ω) (hG : 0 < (uniform Ω).mass G)
    (hR : 0 < ((uniform Ω).condition G hG).mass R) (f : Ω → ℝ) :
    (((uniform Ω).condition G hG).condition R hR).mean f = 𝔼 x : ↥(G ∩ R), f x := by
  rw [condition_condition]
  exact uniform_condition_mean _ _ f

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem eventProbability_mem {X : Type*} [Fintype X] [DecidableEq X]
    (p : FiniteProbabilityWeights X) (G : Finset X) :
    p.eventProbability (fun x => x ∈ G) = p.mass G := by
  classical
  simp [eventProbability, mean, mass, mul_ite]

variable {J : Type*} [Fintype J] [DecidableEq J]
  {Ω : J → Type*} [∀ j, Fintype (Ω j)] [∀ j, DecidableEq (Ω j)]

def piRestrictionSet (G : ∀ j, Finset (Ω j)) : Finset (∀ j, Ω j) :=
  Finset.univ.filter (fun x => ∀ j, x j ∈ G j)

theorem mem_piRestrictionSet (G : ∀ j, Finset (Ω j)) (x : ∀ j, Ω j) :
    x ∈ piRestrictionSet G ↔ ∀ j, x j ∈ G j := by
  simp only [piRestrictionSet, Finset.mem_filter, Finset.mem_univ, true_and]

theorem piRestriction_mass (p : ∀ j, FiniteProbabilityWeights (Ω j))
    (G : ∀ j, Finset (Ω j)) : (pi p).mass (piRestrictionSet G) = ∏ j, (p j).mass (G j) := by
  classical
  rw [← eventProbability_mem]
  have hE : (fun x : ∀ j, Ω j => x ∈ piRestrictionSet G) =
      (fun x => ∀ j, x j ∈ G j) := by
    funext x
    exact propext (mem_piRestrictionSet G x)
  rw [hE, eventProbability_pi]
  exact Finset.prod_congr rfl (fun j _ => eventProbability_mem (p j) (G j))

theorem piRestriction_mass_pos (p : ∀ j, FiniteProbabilityWeights (Ω j))
    (G : ∀ j, Finset (Ω j)) (hG : ∀ j, 0 < (p j).mass (G j)) :
    0 < (pi p).mass (piRestrictionSet G) := by
  rw [piRestriction_mass]
  exact Finset.prod_pos (fun j _ => hG j)

theorem pi_condition (p : ∀ j, FiniteProbabilityWeights (Ω j))
    (G : ∀ j, Finset (Ω j)) (hG : ∀ j, 0 < (p j).mass (G j)) :
    pi (fun j => (p j).condition (G j) (hG j)) =
      (pi p).condition (piRestrictionSet G) (piRestriction_mass_pos p G hG) := by
  classical
  apply ext_weight
  funext x
  change (∏ j, (if x j ∈ G j then (p j).weight (x j) else 0) / (p j).mass (G j)) =
    (if x ∈ piRestrictionSet G then ∏ j, (p j).weight (x j) else 0) /
      (pi p).mass (piRestrictionSet G)
  rw [piRestriction_mass, Finset.prod_div_distrib]
  congr 1
  by_cases hx : ∀ j, x j ∈ G j
  · simp only [hx, ite_true, (mem_piRestrictionSet G x).mpr hx]
  · rw [ite_eq_right ((mem_piRestrictionSet G x).not.mpr hx)]
    obtain ⟨j, hj⟩ := not_forall.mp hx
    exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)

end Erdos3.FiniteProbabilityWeights

end

end OAI
