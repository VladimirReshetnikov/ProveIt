/- Modified for ProveIt: Use older set-comprehension and discrete-subgroup names; statements unchanged. -/
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.MeasureTheory.Measure.Haar.Unique
import OAI.Combinatorics.Progressions.Estimates.LinearQuotientCoverAverage

namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

theorem latticeQuotient_compact : CompactSpace (E ⧸ Λ.toAddSubgroup) := by
  have hc := IsZLattice.isCompact_range_of_periodic Λ
    (QuotientAddGroup.mk' Λ.toAddSubgroup) QuotientAddGroup.continuous_mk (by
      intro x z hz
      have hz0 : QuotientAddGroup.mk' Λ.toAddSubgroup z = 0 :=
        (QuotientAddGroup.eq_zero_iff z).mpr hz
      rw [map_add, hz0, add_zero])
  rw [Set.range_eq_univ.mpr (QuotientAddGroup.mk'_surjective _)] at hc
  exact ⟨hc⟩

variable [MeasurableSpace E] [BorelSpace E]

theorem latticeCover_measurePreserving
    (μ : Measure (E ⧸ Λ.toAddSubgroup)) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (d : ℕ) (hd : 0 < d) :
    MeasurePreserving (quotientIntegerCover Λ.toAddSubgroup d) μ μ := by
  let : IsClosed (Λ.toAddSubgroup : Set E) := AddSubgroup.isClosed_of_discrete
  let : CompactSpace (E ⧸ Λ.toAddSubgroup) := latticeQuotient_compact Λ
  let : BorelSpace (E ⧸ Λ.toAddSubgroup) := QuotientAddGroup.borelSpace
  let : μ.IsAddHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsAddLeftInvariant := inferInstance
      toIsOpenPosMeasure := isOpenPosMeasure_of_addLeftInvariant_of_compact
        (μ := μ) Set.univ isCompact_univ (by simp) }
  exact AddMonoidHom.measurePreserving
    (quotientIntegerCover_continuous Λ.toAddSubgroup d)
    (quotientIntegerCover_surjective Λ.toAddSubgroup d hd) rfl

end Erdos3

end

end OAI
