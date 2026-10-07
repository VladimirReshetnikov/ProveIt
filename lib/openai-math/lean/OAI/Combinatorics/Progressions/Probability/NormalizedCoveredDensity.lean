/- Modified for ProveIt: Use older set-comprehension and discrete-subgroup names; statements unchanged. -/
import OAI.Combinatorics.Progressions.Geometry.NormalizedCoveredChart

namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped Classical

variable {D R : Type*} [Fintype D] [Fintype R] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D))

noncomputable def normalizedCoveredReference (d : ℕ) [NeZero d] :
    Measure ((W × (Fin n → ℤ)) × (R → ZMod d)) :=
  ((ENNReal.ofReal (ZLattice.covolume (latticeSection (standardEuclideanLattice D) W)))⁻¹ •
    (volume.prod (Measure.count : Measure (Fin n → ℤ)))).prod
      (PMF.uniformOfFintype (R → ZMod d)).toMeasure

variable (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
variable (bW : Basis R ℤ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup)
variable (d : ℕ) [NeZero d]

theorem normalizedCoveredReference_restrict (Ω : Set (EuclideanSpace ℝ D)) :
    (normalizedCoveredReference (R := R) (n := n) W d).restrict
      ((normalizedLatticePoint W b ⁻¹' Ω) ×ˢ Set.univ) =
    (normalizedChartReference W b Ω).prod (PMF.uniformOfFintype (R → ZMod d)).toMeasure := by
  rw [normalizedCoveredReference, ← Measure.restrict_prod_eq_prod_univ, Measure.restrict_smul]
  rfl

variable [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
variable (μ : Measure (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup))
variable [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]

theorem normalizedCoveredChart_reference_map
    {Ω : Set (EuclideanSpace ℝ D)} (hΩm : MeasurableSet Ω)
    (hΩ : Ω ⊆ standardLatticeSmallBox D) :
    ((normalizedCoveredReference (R := R) (n := n) W d).restrict
      ((normalizedLatticePoint W b ⁻¹' Ω) ×ˢ Set.univ)).map
        (normalizedCoveredChart W b hb bW d) =
    μ.restrict (normalizedCoveredChart W b hb bW d ''
      ((normalizedLatticePoint W b ⁻¹' Ω) ×ˢ Set.univ)) := by
  rw [normalizedCoveredReference_restrict W b d Ω, normalizedCoveredChart_image]
  exact normalizedCoverResidues_reference W b hb μ bW d hΩm hΩ

theorem normalizedCoveredChart_density_law
    {Ω : Set (EuclideanSpace ℝ D)} (hΩm : MeasurableSet Ω)
    (hΩ : Ω ⊆ standardLatticeSmallBox D)
    (f : (W × (Fin n → ℤ)) × (R → ZMod d) → ℝ)
    (hf : ∀ x ∉ (normalizedLatticePoint W b ⁻¹' Ω) ×ˢ Set.univ, f x = 0) :
    (realDensityMeasure (normalizedCoveredReference W d) f).map
      (normalizedCoveredChart W b hb bW d) =
    realDensityMeasure μ (restrictedChartDensity (normalizedCoveredChart W b hb bW d)
      ((normalizedLatticePoint W b ⁻¹' Ω) ×ˢ Set.univ) 1 f) := by
  let Λ := latticeSection (standardEuclideanLattice D) W
  let : DiscreteTopology Λ.toAddSubgroup := latticeSection_discrete (standardEuclideanLattice D) W
  let : IsClosed (Λ.toAddSubgroup : Set W) := AddSubgroup.isClosed_of_discrete
  let : BorelSpace (W ⧸ Λ.toAddSubgroup) := QuotientAddGroup.borelSpace
  apply restrictedChartDensity_law _ (normalizedCoveredChart_continuous W b hb bW d).measurable
    ((hΩm.preimage (normalizedLatticePoint_continuous W b).measurable).prod MeasurableSet.univ)
    (normalizedCoveredChart_embedding W b hb bW d hΩm hΩ) _ μ (by norm_num) _ f hf
  simpa only [ENNReal.ofReal_one, one_smul] using
    normalizedCoveredChart_reference_map W b hb bW d μ hΩm hΩ

end Erdos3

end

end OAI
