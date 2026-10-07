import OAI.Combinatorics.Progressions.Linear.RankPreparationProjectedAxisBudget

namespace OAI

section

namespace Erdos3.RankPreparationFamily

open Module Submodule VectorPolynomial

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

theorem PreparedHeights.euclideanLayerTorus_compact
    {p : ℝ} {R : ℕ} (hL : L.PreparedHeights p R)
    (hp : 0 ≤ p) (hR : 1 ≤ R) (j : Fin m) :
    CompactSpace (euclideanSubspace (L j).space ⧸
      (latticeSection (standardEuclideanLattice (L j).Coord)
        (euclideanSubspace (L j).space)).toAddSubgroup) := by
  let Λ := latticeSection (standardEuclideanLattice (L j).Coord)
    (euclideanSubspace (L j).space)
  let : IsZLattice ℝ Λ := hL.lattice_full L hp hR j
  have hc := IsZLattice.isCompact_range_of_periodic Λ
    (QuotientAddGroup.mk' Λ.toAddSubgroup)
    (QuotientAddGroup.isQuotientMap_mk Λ.toAddSubgroup).continuous (by
      intro x z hz
      rw [map_add]
      have hz0 : QuotientAddGroup.mk' Λ.toAddSubgroup z = 0 :=
        (QuotientAddGroup.eq_zero_iff z).mpr hz
      rw [hz0, add_zero])
  rw [Set.range_eq_univ.mpr (QuotientAddGroup.mk'_surjective Λ.toAddSubgroup)] at hc
  exact ⟨hc⟩

end Erdos3.RankPreparationFamily

end

end OAI
