import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! A mathlib-only version of CurrentCellLabels2011.sum_le_one_cases. -/
namespace DiophantineConsistency.RefactorOneHot

open scoped BigOperators

def Selected {ι : Type*} (f : ι → ℕ) (i : ι) : Prop :=
  f i = 1 ∧ ∀ j, j ≠ i → f j = 0

theorem sum_le_one_cases {ι : Type*} [Fintype ι] (f : ι → ℕ)
    (hf : (∑ i, f i) ≤ 1) : (∀ i, f i = 0) ∨ ∃ i, Selected f i := by
  classical
  have hs : ∀ i j, f i ≠ 0 → f j ≠ 0 → i = j ∧ f i = 1 := by
    simpa using Finset.sum_le_one_iff.mp hf
  by_cases h : ∀ i, f i = 0
  · exact Or.inl h
  · obtain ⟨i, hi⟩ := not_forall.mp h
    exact Or.inr ⟨i, (hs i i hi hi).2,
      fun j hji => Classical.byContradiction fun hj => hji (hs j i hj hi).1⟩

#print axioms sum_le_one_cases

end DiophantineConsistency.RefactorOneHot
