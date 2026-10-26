import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace DiophantineConsistency.ProofSimplification.OneHot

open scoped BigOperators

-- Exact definition from CurrentCellLabels2011.
def Selected {ι : Type*} (f : ι → ℕ) (i : ι) : Prop :=
  f i = 1 ∧ ∀ j, j ≠ i → f j = 0

-- Exact theorem statement, shortened using Mathlib's existing support theorem.
theorem sum_le_one_cases {ι : Type*} [Fintype ι] (f : ι → ℕ)
    (hf : (∑ i, f i) ≤ 1) : (∀ i, f i = 0) ∨ ∃ i, Selected f i := by
  classical
  have h := Finset.sum_le_one_iff.mp hf
  by_cases hz : ∀ i, f i = 0
  · exact Or.inl hz
  · obtain ⟨i, hi⟩ := not_forall.mp hz
    refine Or.inr ⟨i, (h i i (by simp) (by simp) hi hi).2, ?_⟩
    intro j hji
    by_contra hj
    exact hji (h j i (by simp) (by simp) hj hi).1

#print axioms sum_le_one_cases

end DiophantineConsistency.ProofSimplification.OneHot
