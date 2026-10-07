import OAI.Combinatorics.Progressions.Linear.RankQuotientHeightBudget

namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open Module
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)
  (b : ∀ a, Basis (Fin (finrank ℚ (F.layer a))) ℚ (F.layer a))

theorem ordinaryLayer_eq_span_multidegree_bases (n : ℕ) :
    F.ordinary.layer n = Submodule.span ℚ
      (Set.range (fun z : Σ a : {a : σ → ℕ // n ≤ ∑ i, a i},
          Fin (finrank ℚ (F.layer a.val)) => ((b z.1.val) z.2).val)) := by
  rw [F.degree_eq]
  apply le_antisymm
  · apply iSup_le
    intro a
    apply iSup_le
    intro ha
    rw [← span_submodule_basis (F.layer a) (b a)]
    apply Submodule.span_le.mpr
    rintro x ⟨j, rfl⟩
    exact Submodule.subset_span ⟨⟨⟨a, ha⟩, j⟩, rfl⟩
  · apply Submodule.span_le.mpr
    rintro x ⟨⟨a, j⟩, rfl⟩
    have hle : F.layer a.val ≤ ⨆ (u : σ → ℕ) (_hu : n ≤ ∑ i, u i), F.layer u :=
      le_iSup_of_le a.val (le_iSup_of_le a.property le_rfl)
    exact hle ((b a.val) j).property

theorem exists_bounded_ordinaryLayer_basis {ι : Type*} [Fintype ι]
    (e : Basis ι ℚ L) {H : ℕ}
    (hb : ∀ a i j, RationalHeightLE (e.repr ((b a) i).val j) H) (n : ℕ) :
    ∃ c : Basis (Fin (finrank ℚ (F.ordinary.layer n))) ℚ (F.ordinary.layer n),
      ∀ i j, RationalHeightLE (e.repr (c i).val j) H := by
  apply exists_bounded_submodule_basis_from_spanning e (F.ordinary.layer n)
    (fun z : Σ a : {a : σ → ℕ // n ≤ ∑ i, a i},
      Fin (finrank ℚ (F.layer a.val)) => ((b z.1.val) z.2).val)
    (F.ordinaryLayer_eq_span_multidegree_bases b n).symm
  exact fun z j => hb z.1.val z.2 j

end Erdos3.MultidegreeLieFiltration

end

end OAI
