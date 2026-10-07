/- Modified for ProveIt: Use older set-comprehension and discrete-subgroup names; statements unchanged. -/
import OAI.Combinatorics.Progressions.Lattices.ProjectedLatticeSheetCover
import OAI.Combinatorics.Progressions.Lattices.StandardLatticeCoordinates

namespace OAI

section

namespace Erdos3

open MeasureTheory Module

theorem smallLift_haar_formula {J : Type*} [Fintype J]
    (W : Submodule ℝ (EuclideanSpace ℝ J))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice J) W)]
    (μ : Measure (W ⧸ (latticeSection (standardEuclideanLattice J) W).toAddSubgroup))
    [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    {Ω : Set (EuclideanSpace ℝ J)} (hΩm : MeasurableSet Ω)
    (hΩ : Ω ⊆ standardLatticeSmallBox J) :
    μ (latticeSmallLiftRegion (standardEuclideanLattice J) W Ω) =
      (∑' z : orthogonalLatticeImage (standardEuclideanLattice J) Wᗮ,
        volume {u : W | latticeSheetPoint W z.val u ∈ Ω}) /
          ENNReal.ofReal (ZLattice.covolume (latticeSection (standardEuclideanLattice J) W)) := by
  rw [latticeSmallLiftRegion_eq_sheets]
  apply lattice_sheet_haar_formula (standardEuclideanLattice J) W
    (Free.chooseBasis ℤ (latticeSection (standardEuclideanLattice J) W)) μ hΩm
  intro x hx y hy hxy
  exact standardLatticeSmallBox_separates J (hΩ hx) (hΩ hy) hxy

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module Submodule
open scoped ENNReal

theorem smallLiftRegion_measurable {J : Type*} [Fintype J]
    (W : Submodule ℝ (EuclideanSpace ℝ J))
    {Ω : Set (EuclideanSpace ℝ J)} (hΩm : MeasurableSet Ω)
    (hΩ : Ω ⊆ standardLatticeSmallBox J) :
    MeasurableSet (latticeSmallLiftRegion (standardEuclideanLattice J) W Ω) := by
  let : Countable (orthogonalLatticeImage (standardEuclideanLattice J) Wᗮ) :=
    (orthogonalLatticeProjection_surjective (standardEuclideanLattice J) Wᗮ).countable
  let : DiscreteTopology (latticeSection (standardEuclideanLattice J) W).toAddSubgroup :=
    latticeSection_discrete (standardEuclideanLattice J) W
  let : IsClosed ((latticeSection (standardEuclideanLattice J) W).toAddSubgroup : Set W) :=
    AddSubgroup.isClosed_of_discrete
  rw [latticeSmallLiftRegion_eq_sheets]
  apply MeasurableSet.iUnion
  intro z
  have hm : MeasurableSet {u : W | latticeSheetPoint W z.val u ∈ Ω} :=
    hΩm.preimage (continuous_subtype_val.add continuous_const).measurable
  have hq : Continuous (latticeSheetQuotient (standardEuclideanLattice J) W z) :=
    continuous_quotient_mk'.comp (continuous_id.sub continuous_const)
  apply hm.image_of_continuousOn_injOn hq.continuousOn
  intro u hu v hv he
  exact (latticeSheetQuotient_injective_on_region (standardEuclideanLattice J) W
    (fun x hx y hy hxy => standardLatticeSmallBox_separates J (hΩ hx) (hΩ hy) hxy)
    hu hv he).2

theorem normalized_smallLift_haar_formula {J : Type*} {n : ℕ} [Fintype J]
    (W : Submodule ℝ (EuclideanSpace ℝ J))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice J) W)]
    (b : Basis (Fin n) ℝ Wᗮ) (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    (μ : Measure (W ⧸ (latticeSection (standardEuclideanLattice J) W).toAddSubgroup))
    [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    {Ω : Set (EuclideanSpace ℝ J)} (hΩm : MeasurableSet Ω)
    (hΩ : Ω ⊆ standardLatticeSmallBox J) :
    μ (latticeSmallLiftRegion (standardEuclideanLattice J) W Ω) =
      (∑' z : Fin n → ℤ, volume {u : W |
        (normalizedOrthogonalChart W b).symm
          (u, fun i => (z i : ℝ) / (basisAxisScale b i : ℝ)) ∈ Ω}) /
        ENNReal.ofReal (ZLattice.covolume (latticeSection (standardEuclideanLattice J) W)) := by
  have h := smallLift_haar_formula W μ hΩm hΩ
  have hs := normalizedLatticeSheet_tsum_volume W (projectedIntegerLattice W) b hb Ω
  change (∑' z : orthogonalLatticeImage (standardEuclideanLattice J) Wᗮ,
    volume {u : W | latticeSheetPoint W z.val u ∈ Ω}) = _ at hs
  rw [hs] at h
  exact h

end Erdos3

end

end OAI
