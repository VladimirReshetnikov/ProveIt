import OAI.Combinatorics.Progressions.Lattices.StandardLatticeCoordinates

namespace OAI

section

namespace Erdos3

open Module Submodule

theorem latticeSheetQuotient_eq_of_lift {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Λ : Submodule ℤ E) (W : Submodule ℝ E) (z : orthogonalLatticeImage Λ Wᗮ)
    (ell : Λ) (hell : Wᗮ.orthogonalProjectionOnto ell.val = z.val) (u : W) :
    latticeSheetQuotient Λ W z u =
      QuotientAddGroup.mk (u - W.orthogonalProjectionOnto ell.val) := by
  have hz : Wᗮ.orthogonalProjectionOnto (ell.val - (projectedLatticeLift Λ W z).val) = 0 := by
    rw [map_sub, hell, projectedLatticeLift_projection, sub_self]
  have hs := W.starProjection_add_starProjection_orthogonal
    (ell.val - (projectedLatticeLift Λ W z).val)
  change (W.orthogonalProjectionOnto (ell.val - (projectedLatticeLift Λ W z).val)).val +
    (Wᗮ.orthogonalProjectionOnto (ell.val - (projectedLatticeLift Λ W z).val)).val = _ at hs
  rw [hz, Submodule.coe_zero, add_zero, map_sub, Submodule.coe_sub] at hs
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  change ((u - projectedLatticeShift Λ W z) - (u - W.orthogonalProjectionOnto ell.val)).val ∈ Λ
  have he : ((u - projectedLatticeShift Λ W z) - (u - W.orthogonalProjectionOnto ell.val)).val =
      ell.val - (projectedLatticeLift Λ W z).val := by
    change u.val - (W.orthogonalProjectionOnto (projectedLatticeLift Λ W z).val).val -
      (u.val - (W.orthogonalProjectionOnto ell.val).val) = _
    calc
      _ = (W.orthogonalProjectionOnto ell.val).val -
          (W.orthogonalProjectionOnto (projectedLatticeLift Λ W z).val).val := by abel
      _ = _ := hs
  rw [he]
  exact Λ.sub_mem ell.property (projectedLatticeLift Λ W z).property

theorem standardLatticeIntegerLift_sheet {D J : Type*} [Fintype D] [Fintype J]
    (W : Submodule ℝ (EuclideanSpace ℝ D)) (bP : Basis J ℝ Wᗮ)
    (hP : span ℤ (Set.range bP) = projectedIntegerLattice W) (z : J → ℤ) (u : W) :
    latticeSheetQuotient (standardEuclideanLattice D) W
      (latticeBasisEquiv (projectedIntegerLattice W) bP hP z) u =
      QuotientAddGroup.mk (u - W.orthogonalProjectionOnto (standardLatticeIntegerLift W bP hP z).val) := by
  apply latticeSheetQuotient_eq_of_lift
  exact (standardLatticeIntegerLift_projection W bP hP z).trans
    (latticeBasisEquiv_synthesis (projectedIntegerLattice W) bP hP z).symm

theorem standardLatticeCoordinates_transverse_of_projection {D I J : Type*}
    [Fintype D] [Fintype I] [Fintype J]
    (W : Submodule ℝ (EuclideanSpace ℝ D))
    (bW : Basis I ℤ (latticeSection (standardEuclideanLattice D) W))
    (bP : Basis J ℝ Wᗮ) (hP : span ℤ (Set.range bP) = projectedIntegerLattice W)
    (β : D → ℤ) (z : J → ℤ)
    (hβ : Wᗮ.orthogonalProjectionOnto (standardEuclideanPoint D β).val =
      -bP.equivFun.symm (fun j => (z j : ℝ))) :
    (fun j => standardLatticeCoordinates W bW bP hP β (Sum.inl j)) = z := by
  have h := (standardLatticeCoordinates_projection W bW bP hP β).symm.trans hβ
  have hs := neg_injective h
  funext j
  have he := congrArg (fun x => bP.equivFun x j) hs
  simp only [LinearEquiv.apply_symm_apply] at he
  exact Int.cast_injective (α := ℝ) he

end Erdos3

end

end OAI
