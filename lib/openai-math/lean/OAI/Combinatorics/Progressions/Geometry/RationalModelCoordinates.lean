import OAI.Combinatorics.Progressions.Estimates.RationalPowerHeight

namespace OAI

section

namespace Erdos3

open Module

abbrev RationalModelCoordinateIndex (s d : ℕ) :=
  (Fin d × Fin d × Fin d) ⊕ (Fin (s + 1) × Fin d × Fin d)

namespace RationalFilteredNilmanifold

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

noncomputable def paddedLayerVector (i : Fin (s + 1)) (k : Fin d) : L :=
  if h : k.val < finrank ℚ (D.filtration.layer (i.val + 1)) then
    (D.layerBasis i ⟨k.val, h⟩ : L) else 0

theorem paddedLayerVector_span (i : Fin (s + 1)) :
    Submodule.span ℚ (Set.range (D.paddedLayerVector i)) = D.filtration.layer (i.val + 1) := by
  classical
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  have hd : finrank ℚ (D.filtration.layer (i.val + 1)) ≤ d := by
    simpa only [finrank_eq_card_basis D.basis, Fintype.card_fin] using
      (D.filtration.layer (i.val + 1)).finrank_le
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    dsimp only [paddedLayerVector]
    split_ifs
    · exact (D.layerBasis i _).property
    · exact Submodule.zero_mem _
  · intro x hx
    have hb (k : Fin (finrank ℚ (D.filtration.layer (i.val + 1)))) :
        (D.layerBasis i k : L) ∈ Submodule.span ℚ (Set.range (D.paddedLayerVector i)) := by
      apply Submodule.subset_span
      refine ⟨⟨k.val, k.isLt.trans_le hd⟩, ?_⟩
      simp only [paddedLayerVector, k.isLt, dite_true]
    have heq : (∑ k, (D.layerBasis i).repr ⟨x, hx⟩ k • (D.layerBasis i k : L)) = x := by
      simpa only [Submodule.coe_sum, Submodule.coe_smul] using
        congrArg Subtype.val ((D.layerBasis i).sum_repr ⟨x, hx⟩)
    rw [← heq]
    exact Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ (hb k))

theorem paddedLayerVector_height {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p)
    (i : Fin (s + 1)) (j k : Fin d) :
    rationalLogHeight (D.basis.repr (D.paddedLayerVector i j) k) ≤ p := by
  dsimp only [paddedLayerVector]
  split_ifs
  · exact hD.2.2.2 i _ k
  · simpa [rationalLogHeight] using hp

noncomputable def rationalModelCoordinates : RationalModelCoordinateIndex s d → ℚ
  | .inl z => lieStructureConstants D.basis z.1 z.2.1 z.2.2
  | .inr z => D.basis.repr (D.paddedLayerVector z.1 z.2.1) z.2.2

theorem rationalModelCoordinates_height {p : ℝ} (hp : 0 ≤ p)
    (hD : D.GeometryComplexityLE p) (z : RationalModelCoordinateIndex s d) :
    rationalLogHeight (D.rationalModelCoordinates z) ≤ p := by
  rcases z with z | z
  · exact hD.2.2.1 z.1 z.2.1 z.2.2
  · exact D.paddedLayerVector_height hp hD z.1 z.2.1 z.2.2

end RationalFilteredNilmanifold
end Erdos3

end

end OAI
