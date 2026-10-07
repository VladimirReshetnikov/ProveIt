import OAI.Combinatorics.Progressions.Estimates.NativeOptionFixedSourceQuotientMarkStrong

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {L QL ML : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing QL] [LieAlgebra ℚ QL] [LieRing ML] [LieAlgebra ℚ ML]
    {s t r d e f : ℕ}
    {D : RationalFilteredNilmanifold L s d}
    {Q : RationalFilteredNilmanifold QL t e}
    {Mmark : RationalFilteredNilmanifold ML r f}
    {ψ : L →ₗ⁅ℚ⁆ QL} {φ : QL →ₗ⁅ℚ⁆ ML}
    {pg qg pm qm p0 : ℝ}

namespace AdaptedMapGeometryData

theorem ordinaryResetGeometry
    (geometry : D.AdaptedMapGeometryData Q ψ pg qg)
    (markGeometry : Q.FixedSourceAdaptedMarkGeometryData Mmark geometry.target φ pm qm)
    (hp0 : 0 ≤ p0) (hgeom : qg ≤ p0) (hmark : qm ≤ p0) (hgen : pg ≤ p0) :
    geometry.target.model.GeometryComplexityLE p0 ∧
    markGeometry.target.model.GeometryComplexityLE p0 ∧
    (∀ i j, rationalLogHeight
      (markGeometry.target.model.basis.repr (markGeometry.target.basis j) i) ≤ p0) ∧
    (∀ i j, rationalLogHeight
      (markGeometry.target.basis.repr (φ (geometry.target.basis j)) i) ≤ p0) ∧
    (∀ i j, rationalLogHeight
      (markGeometry.target.model.basis.repr (φ (geometry.target.model.basis j)) i) ≤ p0) ∧
    (Fintype.card (Fin (finrank ℚ L)) : ℝ) ≤ p0 ∧
    (Fintype.card (Fin (finrank ℚ QL)) : ℝ) ≤ p0 ∧
    (Fintype.card (Fin (finrank ℚ ML)) : ℝ) ≤ p0 := by
  have hsourceGeometry := geometry.target_geometry.mono geometry.target.model hgeom
  have hmarkedGeometry := markGeometry.target_geometry.mono markGeometry.target.model hmark
  refine ⟨hsourceGeometry, hmarkedGeometry, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    change rationalLogHeight (markGeometry.target.basis.repr
      (markGeometry.target.basis j) i) ≤ p0
    rw [Basis.repr_self]
    simp only [Finsupp.single_apply]
    split_ifs <;> simpa [rationalLogHeight] using hp0
  · exact fun i j => (markGeometry.entries_logHeight i j).trans hmark
  · exact fun i j => (markGeometry.entries_logHeight i j).trans hmark
  · simpa only [Fintype.card_fin] using geometry.source_dimension.trans hgen
  · simpa only [Fintype.card_fin] using geometry.target_dimension.trans hgen
  · simpa only [Fintype.card_fin] using hmarkedGeometry.1

end AdaptedMapGeometryData
end Erdos3.RationalFilteredNilmanifold

end

end OAI
