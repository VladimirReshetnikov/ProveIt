import OAI.Combinatorics.Progressions.Estimates.CanonicalCoefficientCoverLift
import OAI.Combinatorics.Progressions.Linear.KernelLiftChart

namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped Classical

variable {D R : Type*} [Fintype D] [Fintype R] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
variable (bW : Basis R ℤ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup)
variable (d : ℕ) [NeZero d]

noncomputable def normalizedCoveredChart (p : (W × (Fin n → ℤ)) × (R → ZMod d)) :
    W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup :=
  normalizedCoverLift W b hb d p.1 +
    (coverKernelBasisEquiv (latticeSection (standardEuclideanLattice D) W).toAddSubgroup
      bW d (Nat.pos_of_ne_zero (NeZero.ne d)) p.2).val

theorem normalizedCoveredChart_continuous :
    Continuous (normalizedCoveredChart W b hb bW d) := by
  have hk : Continuous (fun r : R → ZMod d =>
      (coverKernelBasisEquiv (latticeSection (standardEuclideanLattice D) W).toAddSubgroup
        bW d (Nat.pos_of_ne_zero (NeZero.ne d)) r).val) := continuous_of_discreteTopology
  exact ((normalizedCoverLift_continuous W b hb d).comp continuous_fst).add
    (hk.comp continuous_snd)

theorem normalizedCoveredChart_injOn
    {Ω : Set (EuclideanSpace ℝ D)} (hΩ : Ω ⊆ standardLatticeSmallBox D) :
    Set.InjOn (normalizedCoveredChart W b hb bW d)
      ((normalizedLatticePoint W b ⁻¹' Ω) ×ˢ Set.univ) :=
  kernelLiftChart_relabel_injOn _ _ _
    (coverKernelBasisEquiv _ bW d (Nat.pos_of_ne_zero (NeZero.ne d))).toEquiv
    (normalizedCoverLift_projection W b hb d (Nat.pos_of_ne_zero (NeZero.ne d)))
    (normalizedLatticeQuotient_injOn W b hb hΩ)

theorem normalizedCoveredChart_image (Ω : Set (EuclideanSpace ℝ D)) :
    normalizedCoveredChart W b hb bW d ''
      ((normalizedLatticePoint W b ⁻¹' Ω) ×ˢ Set.univ) =
    quotientIntegerCover (latticeSection (standardEuclideanLattice D) W).toAddSubgroup d ⁻¹'
      normalizedChartRegion W b hb Ω :=
  kernelLiftChart_relabel_image _ _ _
    (coverKernelBasisEquiv _ bW d (Nat.pos_of_ne_zero (NeZero.ne d))).toEquiv
    (normalizedCoverLift_projection W b hb d (Nat.pos_of_ne_zero (NeZero.ne d))) _

theorem normalizedCoveredChart_embedding
    {Ω : Set (EuclideanSpace ℝ D)} (hΩm : MeasurableSet Ω)
    (hΩ : Ω ⊆ standardLatticeSmallBox D) :
    MeasurableEmbedding (fun p : (normalizedLatticePoint W b ⁻¹' Ω) ×ˢ
      (Set.univ : Set (R → ZMod d)) => normalizedCoveredChart W b hb bW d p.val) := by
  let Λ := latticeSection (standardEuclideanLattice D) W
  let : DiscreteTopology Λ.toAddSubgroup := latticeSection_discrete (standardEuclideanLattice D) W
  let : IsClosed (Λ.toAddSubgroup : Set W) := AddSubgroup.isClosed_of_discreteTopology
  let : BorelSpace (W ⧸ Λ.toAddSubgroup) := QuotientAddGroup.borelSpace
  exact ContinuousOn.measurableEmbedding
    ((hΩm.preimage (normalizedLatticePoint_continuous W b).measurable).prod MeasurableSet.univ)
    (normalizedCoveredChart_continuous W b hb bW d).continuousOn
    (normalizedCoveredChart_injOn W b hb bW d hΩ)

end Erdos3

end

end OAI
