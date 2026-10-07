import OAI.Combinatorics.Progressions.Polynomial.PolynomialDensityBudget

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem exists_bounded_subproduct {I : Type*} (S : Finset I) (f : I → ℕ) {R : ℕ}
    (hR : 1 ≤ R) (hf : ∀ i ∈ S, f i ≤ R) (hprod : R < ∏ i ∈ S, f i) :
    ∃ T ⊆ S, R < ∏ i ∈ T, f i ∧ (∏ i ∈ T, f i) ≤ R ^ 2 := by
  induction S using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, not_lt_of_ge hR] at hprod
  | @insert i S hi ih =>
    by_cases htail : R < ∏ j ∈ S, f j
    · obtain ⟨T, hT, hlo, hhi⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)) htail
      exact ⟨T, hT.trans (Finset.subset_insert _ _), hlo, hhi⟩
    · refine ⟨insert i S, Finset.Subset.refl _, hprod, ?_⟩
      rw [Finset.prod_insert hi, pow_two]
      exact Nat.mul_le_mul (hf i (Finset.mem_insert_self _ _)) (Nat.le_of_not_gt htail)

theorem finite_product_witness {I : Type*} (S : Finset I) (f : I → ℕ) {R : ℕ}
    (hR : 1 ≤ R) (hprod : R < ∏ i ∈ S, f i) :
    (∃ i ∈ S, R < f i) ∨
      ∃ T ⊆ S, R < ∏ i ∈ T, f i ∧ (∏ i ∈ T, f i) ≤ R ^ 2 := by
  by_cases hlarge : ∃ i ∈ S, R < f i
  · exact Or.inl hlarge
  · right
    apply exists_bounded_subproduct S f hR _ hprod
    intro i hi
    exact Nat.le_of_not_gt (fun h => hlarge ⟨i, hi, h⟩)

end Erdos3

end

end OAI
