/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.FiniteReciprocalTenthTail
import OAI.Combinatorics.Progressions.Probability.FiniteConditionedMass

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

private theorem abs_sub_min_identity (x y : ℝ) :
    |x - y| = x + y - 2 * min x y := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

theorem pi_weight_l1_le_sum {J : Type*} [Fintype J] [DecidableEq J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)]
    (p q : ∀ j, FiniteProbabilityWeights (Ω j)) :
    (∑ x, |(pi p).weight x - (pi q).weight x|) ≤
      ∑ j, ∑ x, |(p j).weight x - (q j).weight x| := by
  classical
  let h : ∀ j, Ω j → ℝ := fun j x => min ((p j).weight x) ((q j).weight x)
  let a : J → ℝ := fun j => ∑ x, h j x
  have hh (j) (x : Ω j) : 0 ≤ h j x := le_min ((p j).nonneg x) ((q j).nonneg x)
  have ha0 (j) : 0 ≤ a j := Finset.sum_nonneg (fun x _ => hh j x)
  have ha1 (j) : a j ≤ 1 := by
    calc
      a j ≤ ∑ x, (p j).weight x := Finset.sum_le_sum (fun x _ => min_le_left _ _)
      _ = 1 := (p j).total
  have hlower := one_sub_sum_le_positive_prod Finset.univ a (fun j => 1 - a j)
    (fun j _ => ha0 j) (fun j _ => ⟨sub_nonneg.mpr (ha1 j), by linarith [ha0 j]⟩)
    (fun j _ => by simp)
  have hpoint (x : ∀ j, Ω j) :
      |(pi p).weight x - (pi q).weight x| ≤
        (pi p).weight x + (pi q).weight x - 2 * ∏ j, h j (x j) := by
    rw [abs_sub_min_identity]
    have hp : (∏ j, h j (x j)) ≤ (pi p).weight x :=
      Finset.prod_le_prod₀ (fun j _ => hh j (x j)) (fun j _ => min_le_left _ _)
    have hq : (∏ j, h j (x j)) ≤ (pi q).weight x :=
      Finset.prod_le_prod₀ (fun j _ => hh j (x j)) (fun j _ => min_le_right _ _)
    linarith [le_min hp hq]
  have hsum := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hpoint x)
  have hprod : (∑ x : ∀ j, Ω j, ∏ j, h j (x j)) = ∏ j, a j :=
    (Fintype.prod_sum h).symm
  have hcoord (j) : (∑ x, |(p j).weight x - (q j).weight x|) = 2 * (1 - a j) := by
    simp_rw [abs_sub_min_identity]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      (p j).total, (q j).total]
    change 1 + 1 - 2 * a j = _
    ring
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    (pi p).total, (pi q).total, hprod] at hsum
  simp_rw [hcoord]
  rw [← Finset.mul_sum]
  linarith

theorem abs_eventProbability_sub_le_weight_l1 {Ω : Type*} [Fintype Ω]
    (p q : FiniteProbabilityWeights Ω) (E : Ω → Prop) :
    |p.eventProbability E - q.eventProbability E| ≤
      ∑ x, |p.weight x - q.weight x| := by
  classical
  unfold eventProbability mean
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : E x
  · simp [hx]
  · simp [hx, abs_nonneg]

theorem abs_eventProbability_pi_sub_le_sum {J : Type*} [Fintype J] [DecidableEq J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)]
    (p q : ∀ j, FiniteProbabilityWeights (Ω j)) (E : (∀ j, Ω j) → Prop) :
    |(pi p).eventProbability E - (pi q).eventProbability E| ≤
      ∑ j, ∑ x, |(p j).weight x - (q j).weight x| :=
  (abs_eventProbability_sub_le_weight_l1 (pi p) (pi q) E).trans
    (pi_weight_l1_le_sum p q)

end Erdos3.FiniteProbabilityWeights

end

end OAI
