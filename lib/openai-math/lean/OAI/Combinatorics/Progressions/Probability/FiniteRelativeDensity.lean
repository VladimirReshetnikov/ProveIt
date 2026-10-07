import OAI.Combinatorics.Progressions.Estimates.AnchoredReferenceDomination

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {Ω : Type*} [Fintype Ω]

noncomputable def relativeDensity (p q : FiniteProbabilityWeights Ω) (x : Ω) : ℝ :=
  q.weight x / p.weight x

theorem relativeDensity_nonneg (p q : FiniteProbabilityWeights Ω) (x : Ω) :
    0 ≤ p.relativeDensity q x := div_nonneg (q.nonneg x) (p.nonneg x)

theorem mean_relativeDensity (p q : FiniteProbabilityWeights Ω) (hp : ∀ x, 0 < p.weight x)
    (f : Ω → ℝ) : p.mean (fun x => p.relativeDensity q x * f x) = q.mean f := by
  unfold mean relativeDensity
  apply Finset.sum_congr rfl
  intro x _
  field_simp [(hp x).ne']

theorem relativeDensity_tail_mass (p q : FiniteProbabilityWeights Ω) (hp : ∀ x, 0 < p.weight x)
    (C : ℝ) :
    p.mean (fun x => if x ∈ Finset.univ.filter (fun y => p.relativeDensity q y ≤ C)
      then 0 else p.relativeDensity q x) =
      q.mass (Finset.univ.filter (fun x => C*p.weight x < q.weight x)) := by
  simp only [mean, mass, Finset.sum_filter, Finset.mem_filter, Finset.mem_univ, true_and]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : C*p.weight x < q.weight x
  · have hd : ¬p.relativeDensity q x ≤ C := by
      simpa only [relativeDensity, div_le_iff₀ (hp x), not_le] using hx
    simp only [hd, ite_false, hx, ite_true]
    change p.weight x * (q.weight x / p.weight x) = q.weight x
    field_simp [(hp x).ne']
  · have hd : p.relativeDensity q x ≤ C := (div_le_iff₀ (hp x)).mpr (le_of_not_gt hx)
    simp only [hd, ite_true, mul_zero, hx, ite_false]

end Erdos3.FiniteProbabilityWeights

end

end OAI
