/- Modified for ProveIt: adapt import paths to Mathlib v4.32.0.
Mathematical statements and proofs unchanged. -/
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Basis.Submodule
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace OAI

section

namespace Erdos3

open Module

theorem exists_basis_of_span_subset {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] (S : Set E) :
    ∃ d : ℕ, ∃ b : Basis (Fin d) ℝ (Submodule.span ℝ S),
      d = finrank ℝ (Submodule.span ℝ S) ∧ ∀ i, (b i).val ∈ S := by
  classical
  obtain ⟨s, hs, hspan, hli⟩ := exists_linearIndependent ℝ S
  let : Fintype s := hli.setFinite.fintype
  have he : Submodule.span ℝ (Set.range ((↑) : s → E)) = Submodule.span ℝ S := by
    simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using hspan
  let b₀ : Basis s ℝ (Submodule.span ℝ S) := (Basis.span hli).map (LinearEquiv.ofEq _ _ he)
  let b := b₀.reindex (Fintype.equivFin s)
  refine ⟨Fintype.card s, b, ?_, ?_⟩
  · simpa only [Fintype.card_fin] using (finrank_eq_card_basis b).symm
  intro i
  have hb : (b i).val = ((Fintype.equivFin s).symm i).val := by
    simp only [b, Basis.reindex_apply, b₀, Basis.map_apply]
    exact Basis.coe_span_apply hli _
  rw [hb]
  exact hs ((Fintype.equivFin s).symm i).property

end Erdos3

end

end OAI
