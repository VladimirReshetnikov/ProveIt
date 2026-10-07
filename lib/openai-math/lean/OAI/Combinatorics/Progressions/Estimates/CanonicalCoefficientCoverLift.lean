/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Measurable
import OAI.Combinatorics.Progressions.Lattices.LatticeCoverMeasure
import OAI.Combinatorics.Progressions.Linear.FiniteKernelRestriction
import OAI.Combinatorics.Progressions.Probability.EmptyCoefficientDensity

namespace OAI

section

namespace Erdos3

open Module Submodule

variable {D : Type*} [Fintype D] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)

noncomputable def normalizedLatticeRepresentative (x : W × (Fin n → ℤ)) : W :=
  x.1 - W.orthogonalProjectionOnto (standardLatticeIntegerLift W b hb x.2).val

theorem normalizedLatticeRepresentative_continuous :
    Continuous (normalizedLatticeRepresentative W b hb) := by
  have hc : Continuous (standardLatticeIntegerLift W b hb) := continuous_of_discreteTopology
  exact continuous_fst.sub (W.orthogonalProjectionOnto.continuous.comp
    (continuous_subtype_val.comp (hc.comp continuous_snd)))

theorem normalizedLatticeRepresentative_mk (x : W × (Fin n → ℤ)) :
    (QuotientAddGroup.mk (normalizedLatticeRepresentative W b hb x) :
      W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup) =
      normalizedLatticeQuotient W b hb x :=
  (normalizedLatticeQuotient_linear_lift W b hb x).symm

noncomputable def normalizedCoverLift (d : ℕ) (x : W × (Fin n → ℤ)) :
    W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup :=
  QuotientAddGroup.mk ((d : ℝ)⁻¹ • normalizedLatticeRepresentative W b hb x)

theorem normalizedCoverLift_continuous (d : ℕ) :
    Continuous (normalizedCoverLift W b hb d) := by
  have hc : Continuous (fun _ : W × (Fin n → ℤ) => (d : ℝ)⁻¹) := continuous_const
  exact QuotientAddGroup.continuous_mk.comp
    (hc.smul (normalizedLatticeRepresentative_continuous W b hb))

theorem normalizedCoverLift_projection (d : ℕ) (hd : 0 < d) (x : W × (Fin n → ℤ)) :
    quotientIntegerCover (latticeSection (standardEuclideanLattice D) W).toAddSubgroup d
        (normalizedCoverLift W b hb d x) = normalizedLatticeQuotient W b hb x := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  change quotientIntegerCover _ d (QuotientAddGroup.mk' _
    ((d : ℝ)⁻¹ • normalizedLatticeRepresentative W b hb x)) = _
  rw [quotientIntegerCover_mk, smul_smul, mul_inv_cancel₀ hd0, one_smul]
  exact normalizedLatticeRepresentative_mk W b hb x

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module Submodule
open scoped Classical

variable {D R : Type*} [Fintype D] [Fintype R] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
variable [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
variable (μ : Measure (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup))
variable [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]

theorem normalizedCoverLift_reference (d : ℕ) (hd : 0 < d)
    [Fintype (quotientIntegerCover (latticeSection (standardEuclideanLattice D) W).toAddSubgroup d).ker]
    {Ω : Set (EuclideanSpace ℝ D)} (hΩm : MeasurableSet Ω)
    (hΩ : Ω ⊆ standardLatticeSmallBox D) :
    finiteKernelLiftLaw
      (quotientIntegerCover (latticeSection (standardEuclideanLattice D) W).toAddSubgroup d)
      (normalizedChartReference W b Ω) (normalizedCoverLift W b hb d) =
    μ.restrict (quotientIntegerCover
      (latticeSection (standardEuclideanLattice D) W).toAddSubgroup d ⁻¹'
        normalizedChartRegion W b hb Ω) := by
  let Λ := latticeSection (standardEuclideanLattice D) W
  let : DiscreteTopology Λ.toAddSubgroup := latticeSection_discrete (standardEuclideanLattice D) W
  let : IsClosed (Λ.toAddSubgroup : Set W) := AddSubgroup.isClosed_of_discreteTopology
  let : CompactSpace (W ⧸ Λ.toAddSubgroup) := latticeQuotient_compact Λ
  let : BorelSpace (W ⧸ Λ.toAddSubgroup) := QuotientAddGroup.borelSpace
  let : IsFiniteMeasure (normalizedChartReference W b Ω) :=
    normalizedChartReference_finite W b hb μ hΩm hΩ
  apply finiteKernelLift_restrict _ (quotientIntegerCover_continuous _ d)
    (quotientIntegerCover_surjective _ d hd) μ μ
    (latticeCover_measurePreserving Λ μ d hd)
    (normalizedChartRegion_measurable W b hb hΩm hΩ) _ _
    (normalizedCoverLift_continuous W b hb d).measurable
  have he : (quotientIntegerCover Λ.toAddSubgroup d ∘ normalizedCoverLift W b hb d) =
      normalizedLatticeQuotient W b hb := by
    funext x
    exact normalizedCoverLift_projection W b hb d hd x
  rw [he]
  exact normalizedChartReference_map W b hb μ hΩm hΩ

theorem normalizedCoverResidues_reference
    (bW : Basis R ℤ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup)
    (d : ℕ) [NeZero d]
    {Ω : Set (EuclideanSpace ℝ D)} (hΩm : MeasurableSet Ω)
    (hΩ : Ω ⊆ standardLatticeSmallBox D) :
    ((normalizedChartReference W b Ω).prod
      (PMF.uniformOfFintype (R → ZMod d)).toMeasure).map
        (fun p => normalizedCoverLift W b hb d p.1 +
          (coverKernelBasisEquiv (latticeSection (standardEuclideanLattice D) W).toAddSubgroup
            bW d (Nat.pos_of_ne_zero (NeZero.ne d)) p.2).val) =
    μ.restrict (quotientIntegerCover
      (latticeSection (standardEuclideanLattice D) W).toAddSubgroup d ⁻¹'
        normalizedChartRegion W b hb Ω) := by
  let Λ := latticeSection (standardEuclideanLattice D) W
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  let : Fintype (quotientIntegerCover Λ.toAddSubgroup d).ker :=
    Fintype.ofEquiv (R → ZMod d) (coverKernelBasisEquiv Λ.toAddSubgroup bW d hd).toEquiv
  let : DiscreteTopology Λ.toAddSubgroup := latticeSection_discrete (standardEuclideanLattice D) W
  let : IsClosed (Λ.toAddSubgroup : Set W) := AddSubgroup.isClosed_of_discreteTopology
  let : BorelSpace (W ⧸ Λ.toAddSubgroup) := QuotientAddGroup.borelSpace
  let : IsFiniteMeasure (normalizedChartReference W b Ω) :=
    normalizedChartReference_finite W b hb μ hΩm hΩ
  rw [finiteKernelLiftLaw_basisResidues Λ.toAddSubgroup bW d _ _
    (normalizedCoverLift_continuous W b hb d).measurable]
  exact normalizedCoverLift_reference W b hb μ d hd hΩm hΩ

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {K : Type*} [Fintype K] {m : ℕ} {J I : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

noncomputable def canonicalCoefficientCoverLift (d : ℕ)
    (x : CoefficientSamplerArrays (K := K) I n) : CoefficientTorus (K := K) U :=
  (euclideanCoefficientEquiv U).symm (fun j e =>
    normalizedCoverLift (euclideanSubspace (U j)) (b j) (hb j) d
      (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _ (x j) e)))

omit [Fintype K] in
theorem canonicalCoefficientCoverLift_projection (d : ℕ) (hd : 0 < d)
    (x : CoefficientSamplerArrays (K := K) I n) :
    quotientIntegerCover (coefficientIntegerLattice U) d
        (canonicalCoefficientCoverLift U b hb o d x) = canonicalCoefficientSample U b hb o x := by
  apply (euclideanCoefficientEquiv U).injective
  change euclideanCoefficientEquiv U (d • canonicalCoefficientCoverLift U b hb o d x) = _
  rw [map_nsmul, canonicalCoefficientCoverLift, AddEquiv.apply_symm_apply,
    canonicalCoefficientSample, AddEquiv.apply_symm_apply]
  funext j e
  exact normalizedCoverLift_projection (euclideanSubspace (U j)) (b j) (hb j) d hd _

theorem canonicalCoefficientCoverLift_measurable
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (d : ℕ) : Measurable (canonicalCoefficientCoverLift (K := K) U b hb o d) := by
  apply (euclideanCoefficientMeasurableEquiv U).symm.measurable.comp
  apply Measurable.of_eval
  intro j
  apply Measurable.of_eval
  intro e
  exact (normalizedCoverLift_continuous (euclideanSubspace (U j)) (b j) (hb j) d).measurable.comp
    ((orthonormalMixedChart (o j)).measurable.comp ((measurable_pi_apply e).comp
      ((mixedArrayRegroup _ _ _).measurable.comp (measurable_pi_apply j))))

end Erdos3.VectorPolynomial

end

end OAI
