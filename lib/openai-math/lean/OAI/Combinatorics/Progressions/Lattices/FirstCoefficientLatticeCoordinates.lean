import OAI.Combinatorics.Progressions.Estimates.FastCoefficientImage
import OAI.Combinatorics.Progressions.Linear.SortedBasisTriangular

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_lattice_ready_firstCoefficient_basis
    {σ ι E : Type*} [AddCommGroup E] [Module ℝ E] {d : ℕ}
    (ω : ι → ℕ) (rows : Fin d → FirstCoefficientIndex (fun _ : σ => 1) ω)
    (b : Basis (Fin d) ℝ E) :
    ∃ (e : Equiv.Perm (Fin d)) (a : ℕ), a ≤ d ∧
      (∀ i, i.val < a ↔ (rows (e i)).val.1 = 0) ∧
      ∀ (f : E ≃ₗ[ℝ] E),
        (∀ i j, ω (rows i).val.2 ≤ ω (rows j).val.2 →
          LinearMap.toMatrix b b f.toLinearMap i j = (1 : Matrix (Fin d) (Fin d) ℝ) i j) →
        let b' := b.reindex e.symm
        let A := b'.equivFun.symm.trans (f.trans b'.equivFun)
        (∀ i j, i < j → (LinearMap.toMatrix' A.toLinearMap) i j = 0) ∧
        (∀ i, (LinearMap.toMatrix' A.toLinearMap) i i = 1) ∧
        (∀ i j, i.val < a → j.val < a →
          (LinearMap.toMatrix' A.toLinearMap) i j = (1 : Matrix (Fin d) (Fin d) ℝ) i j) := by
  obtain ⟨e, a, ha, hm, hz⟩ := exists_sorted_firstCoefficient_rows ω rows
  refine ⟨e, a, ha, hz, ?_⟩
  intro f hf
  dsimp only
  simp only [basis_coordinate_linearEquiv_matrix]
  have hfirst (i) (hi : i.val < a) : ω (rows (e i)).val.2 = 1 :=
    (firstCoefficientIndex_zero_iff_grade_one ω (rows (e i))).mp ((hz i).mp hi)
  exact ⟨sorted_basis_upper_zero b (fun i => ω (rows i).val.2) f.toLinearMap hf e hm,
    sorted_basis_diagonal_one b (fun i => ω (rows i).val.2) f.toLinearMap hf e,
    sorted_basis_initial_identity b (fun i => ω (rows i).val.2) f.toLinearMap hf e hfirst⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
