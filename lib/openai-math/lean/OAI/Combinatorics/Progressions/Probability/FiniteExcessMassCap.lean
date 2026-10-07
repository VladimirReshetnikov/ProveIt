import Mathlib.Analysis.SpecialFunctions.Exp
import OAI.Combinatorics.Progressions.Estimates.FiniteFiberTest

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

noncomputable def excessMass {X : Type*} [Fintype X]
    (p q : FiniteProbabilityWeights X) (C : ℝ) : ℝ :=
  ∑ x, max (q.weight x - C * p.weight x) 0

theorem excessMass_nonneg {X : Type*} [Fintype X]
    (p q : FiniteProbabilityWeights X) (C : ℝ) : 0 ≤ p.excessMass q C :=
  Finset.sum_nonneg (fun _ _ => le_max_right _ _)

theorem mass_le_of_excessMass {X : Type*} [Fintype X]
    (p q : FiniteProbabilityWeights X) (C : ℝ) (G : Finset X) :
    q.mass G ≤ C * p.mass G + p.excessMass q C := by
  have h : q.mass G - C * p.mass G ≤ p.excessMass q C := by
    calc
      _ = ∑ x ∈ G, (q.weight x - C * p.weight x) := by
        simp only [mass, Finset.sum_sub_distrib, Finset.mul_sum]
      _ ≤ ∑ x ∈ G, max (q.weight x - C * p.weight x) 0 :=
        Finset.sum_le_sum (fun _ _ => le_max_left _ _)
      _ ≤ p.excessMass q C := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ G)
        (fun _ _ _ => le_max_right _ _)
  linarith

theorem excessMass_le_of_mass_le {X : Type*} [Fintype X]
    (p q : FiniteProbabilityWeights X) {C ε : ℝ}
    (h : ∀ G : Finset X, q.mass G ≤ C * p.mass G + ε) : p.excessMass q C ≤ ε := by
  let G := Finset.univ.filter (fun x => 0 < q.weight x - C * p.weight x)
  have he : p.excessMass q C = q.mass G - C * p.mass G := by
    have hsum : (∑ x, max (q.weight x - C * p.weight x) 0) =
        ∑ x ∈ G, (q.weight x - C * p.weight x) := by
      simp only [G, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : 0 < q.weight x - C * p.weight x
      · simp only [hx, ite_true, max_eq_left hx.le]
      · simp only [hx, ite_false, max_eq_right (le_of_not_gt hx)]
    rw [excessMass, hsum, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rfl
  rw [he]
  linarith [h G]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

theorem excessMass_antitone_cap {X : Type*} [Fintype X]
    (reference law : FiniteProbabilityWeights X) :
    Antitone (reference.excessMass law) := by
  intro C D hCD
  apply Finset.sum_le_sum
  intro x _
  exact max_le_max (sub_le_sub_left
    (mul_le_mul_of_nonneg_right hCD (reference.nonneg x)) _) le_rfl

theorem excessMass_max_one_le {X : Type*} [Fintype X]
    (reference law : FiniteProbabilityWeights X) (C : ℝ) :
    reference.excessMass law (max 1 C) ≤ reference.excessMass law C :=
  reference.excessMass_antitone_cap law (le_max_right _ _)

end Erdos3.FiniteProbabilityWeights

namespace Erdos3

theorem marginalCap_max_one_exp_bound {C p : ℝ} (hp : 0 ≤ p)
    (hC : C ≤ Real.exp p) :
    1 ≤ max 1 C ∧ max 1 C ≤ Real.exp p :=
  ⟨le_max_left _ _, max_le (Real.one_le_exp hp) hC⟩

end Erdos3

end

end OAI
