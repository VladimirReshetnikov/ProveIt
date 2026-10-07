import OAI.Combinatorics.Progressions.Lattices.NormalizedLatticeSheet

namespace OAI

section

namespace Erdos3

open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

def latticeSmallLiftRegion (Λ : Submodule ℤ E) (W : Submodule ℝ E) (Ω : Set E) :
    Set (W ⧸ (latticeSection Λ W).toAddSubgroup) :=
  {q | ∃ y ∈ Ω, ∃ u : W, QuotientAddGroup.mk u = q ∧ y - u.val ∈ Λ}

theorem latticeSmallLiftRegion_eq_sheets (Λ : Submodule ℤ E) (W : Submodule ℝ E) (Ω : Set E) :
    latticeSmallLiftRegion Λ W Ω = ⋃ z : orthogonalLatticeImage Λ Wᗮ,
      latticeSheetQuotient Λ W z '' {u | latticeSheetPoint W z.val u ∈ Ω} := by
  ext q
  constructor
  · rintro ⟨y, hy, u, hu, hyu⟩
    let z : orthogonalLatticeImage Λ Wᗮ := ⟨Wᗮ.orthogonalProjectionOnto y,
      y - u.val, hyu, by
        change Wᗮ.orthogonalProjectionOnto (y - u.val) = Wᗮ.orthogonalProjectionOnto y
        rw [map_sub, W.orthogonalProjectionOnto_orthogonal_apply_eq_zero u.property, sub_zero]⟩
    let v := W.orthogonalProjectionOnto y
    have hp : latticeSheetPoint W z.val v = y :=
      W.starProjection_add_starProjection_orthogonal y
    refine mem_iUnion.mpr ⟨z, v, ?_, ?_⟩
    · change latticeSheetPoint W z.val v ∈ Ω
      rwa [hp]
    · apply Eq.trans _ hu
      apply QuotientAddGroup.eq_iff_sub_mem.mpr
      change ((v - projectedLatticeShift Λ W z) - u).val ∈ Λ
      have hr := latticeSheetPoint_reconstruction Λ W z v
      rw [hp] at hr
      have hs : ((v - projectedLatticeShift Λ W z) - u).val =
          (y - u.val) - (projectedLatticeLift Λ W z).val := by
        rw [hr]
        simp only [Submodule.coe_sub]
        abel
      rw [hs]
      exact Λ.sub_mem hyu (projectedLatticeLift Λ W z).property
  · intro hq
    obtain ⟨z, v, hv, he⟩ := mem_iUnion.mp hq
    refine ⟨latticeSheetPoint W z.val v, hv, v - projectedLatticeShift Λ W z, he, ?_⟩
    rw [latticeSheetPoint_reconstruction]
    simpa only [add_sub_cancel_left] using (projectedLatticeLift Λ W z).property

end Erdos3

end

end OAI
