/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalRetainedResidual

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

omit [Fintype X] in

theorem allocatedExternalCandidateWidths_eq (N : X → ℕ) (τ ξ : ℝ) :
    allocatedExternalCandidateWidths B U b S N τ ξ =
      narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n))
        (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N := by
  rw [allocatedExternalCandidateWidths, allocatedExternalCandidateRootBudget_eq]

variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    (τ ξ : ℝ) (stride : X → ℕ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)

namespace AllocatedExternalCandidateSampler

variable {B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

theorem law_eq_selectedJointFiniteLaw
    (hbases : (trimmedIntegerBox N (spatialTrimMargin τ N)).Nonempty)
    (hW : ∀ z, 0 < allocatedExternalCandidateWidths B U b S N τ ξ z)
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells
      (allocatedExternalCandidateWidths B U b S N τ ξ) z)
    (hcenter : 0 < selectedJointDensityMass (trimmedIntegerBox N (spatialTrimMargin τ N))
      stride cells (allocatedExternalCandidateWidths B U b S N τ ξ)
      (allocatedCenteredJointDensity B U b hb o hR hσ S poly hm center)) :
    A.law = selectedJointFiniteLaw (trimmedIntegerBox N (spatialTrimMargin τ N)) hbases
      stride cells (allocatedExternalCandidateWidths B U b S N τ ξ) hW hmass
      (allocatedCenteredJointDensity B U b hb o hR hσ S poly hm center)
      (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hm center) hcenter := rfl

end AllocatedExternalCandidateSampler

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

namespace AllocatedExternalCandidateSamplerFamily

variable (A : AllocatedExternalCandidateSamplerFamily B U b S hb o hR hσ N poly hm τ ξ stride cells)

private theorem law_heq_of_parameters
    (V : (Option (LayerSamplerVariables G I n B) × X → ℝ)) (bases : Finset (X → ℤ))
    (hV : (allocatedExternalCandidateWidths B U b S N τ ξ) = V) (hBases : (A 0).bases = bases)
    (hbases : bases.Nonempty) (hwidth : ∀ z, 0 < V z)
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z)
    (hcenter : ∀ center : (CoefficientTorus (K := LayerSamplerVariables G I n B) U), 0 < selectedJointDensityMass bases stride cells V ((allocatedCenteredJointDensity B U b hb o hR hσ S poly hm) center)) :
    HEq A.law (fun center => selectedJointFiniteLaw bases hbases stride cells V hwidth hmass
      ((allocatedCenteredJointDensity B U b hb o hR hσ S poly hm) center) ((allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hm) center) (hcenter center)) := by
  subst V
  subst bases
  rfl

private theorem good_of_parameters
    (Good : ∀ (V : (Option (LayerSamplerVariables G I n B) × X → ℝ)) (bases : Finset (X → ℤ)),
      ((CoefficientTorus (K := LayerSamplerVariables G I n B) U) → FiniteProbabilityWeights (bases × rectangularWeightIndices 0 V 1)) → Prop)
    (V : (Option (LayerSamplerVariables G I n B) × X → ℝ)) (bases : Finset (X → ℤ))
    (hV : (allocatedExternalCandidateWidths B U b S N τ ξ) = V) (hBases : (A 0).bases = bases)
    (hbases : bases.Nonempty) (hwidth : ∀ z, 0 < V z)
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z)
    (hcenter : ∀ center : (CoefficientTorus (K := LayerSamplerVariables G I n B) U), 0 < selectedJointDensityMass bases stride cells V ((allocatedCenteredJointDensity B U b hb o hR hσ S poly hm) center))
    (hGood : Good V bases (fun center => selectedJointFiniteLaw bases hbases stride cells V hwidth hmass
      ((allocatedCenteredJointDensity B U b hb o hR hσ S poly hm) center) ((allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hm) center) (hcenter center))) :
    Good (allocatedExternalCandidateWidths B U b S N τ ξ) (A 0).bases A.law := by
  subst V
  subst bases
  exact hGood

variable [sourceDecidableEq : DecidableEq X]

omit [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] in

theorem bases_eq_prepared : (A 0).bases = trimmedIntegerBox N (spatialTrimMargin τ N) := by
  change @trimmedIntegerBox X _ (Classical.decEq X) N (spatialTrimMargin τ N) = _
  rw [show Classical.decEq X = sourceDecidableEq from Subsingleton.elim _ _]

variable
    (hbases : (trimmedIntegerBox N (spatialTrimMargin τ N)).Nonempty)
    (hwidth : ∀ z, 0 < (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) z)
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) z)
    (hcenter : ∀ center : (CoefficientTorus (K := LayerSamplerVariables G I n B) U),
      0 < selectedJointDensityMass (trimmedIntegerBox N (spatialTrimMargin τ N))
        stride cells (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) ((allocatedCenteredJointDensity B U b hb o hR hσ S poly hm) center))

theorem law_heq_prepared : HEq A.law (fun center => selectedJointFiniteLaw
  (trimmedIntegerBox N (spatialTrimMargin τ N)) hbases stride cells (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) hwidth hmass
  ((allocatedCenteredJointDensity B U b hb o hR hσ S poly hm) center) ((allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hm) center) (hcenter center)) :=
  A.law_heq_of_parameters _ _ (allocatedExternalCandidateWidths_eq B U b S N τ ξ)
    A.bases_eq_prepared hbases hwidth hmass hcenter

theorem good_of_prepared
    (Good : ∀ (V : (Option (LayerSamplerVariables G I n B) × X → ℝ)) (bases : Finset (X → ℤ)),
      ((CoefficientTorus (K := LayerSamplerVariables G I n B) U) → FiniteProbabilityWeights (bases × rectangularWeightIndices 0 V 1)) → Prop)
    (hGood : Good (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) (trimmedIntegerBox N (spatialTrimMargin τ N)) (fun center => selectedJointFiniteLaw
  (trimmedIntegerBox N (spatialTrimMargin τ N)) hbases stride cells (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) hwidth hmass
  ((allocatedCenteredJointDensity B U b hb o hR hσ S poly hm) center) ((allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hm) center) (hcenter center))) :
    Good (allocatedExternalCandidateWidths B U b S N τ ξ) (A 0).bases A.law :=
  A.good_of_parameters Good _ _ (allocatedExternalCandidateWidths_eq B U b S N τ ξ)
    A.bases_eq_prepared hbases hwidth hmass hcenter hGood

variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]

theorem measurable_good_of_prepared
    (Good : ∀ (V : (Option (LayerSamplerVariables G I n B) × X → ℝ)) (bases : Finset (X → ℤ)),
      ((CoefficientTorus (K := LayerSamplerVariables G I n B) U) → FiniteProbabilityWeights (bases × rectangularWeightIndices 0 V 1)) → Prop)
    (hweight : ∀ z, Measurable (fun center => ((fun center => selectedJointFiniteLaw
  (trimmedIntegerBox N (spatialTrimMargin τ N)) hbases stride cells (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) hwidth hmass
  ((allocatedCenteredJointDensity B U b hb o hR hσ S poly hm) center) ((allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hm) center) (hcenter center)) center).weight z))
    (hGood : Good (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) (trimmedIntegerBox N (spatialTrimMargin τ N)) (fun center => selectedJointFiniteLaw
  (trimmedIntegerBox N (spatialTrimMargin τ N)) hbases stride cells (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) hwidth hmass
  ((allocatedCenteredJointDensity B U b hb o hR hσ S poly hm) center) ((allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hm) center) (hcenter center))) :
    (∀ z, Measurable (fun center => (A.law center).weight z)) ∧
      Good (allocatedExternalCandidateWidths B U b S N τ ξ) (A 0).bases A.law := by
  exact A.good_of_prepared hbases hwidth hmass hcenter
    (fun V bases law => (∀ z, Measurable (fun center => (law center).weight z)) ∧ Good V bases law)
    ⟨hweight, hGood⟩

end AllocatedExternalCandidateSamplerFamily
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

noncomputable def allocatedExternalConditionalExcessExponent (m : ℕ) : ℕ :=
  (exists_allocated_centered_narrow_prescribed_marginal_pointwise.{0,0,0,0,0,0} m).choose

theorem allocatedExternalConditionalExcessExponent_spec (m : ℕ) :
    2 ≤ allocatedExternalConditionalExcessExponent m ∧
      AllocatedCenteredNarrowPrescribedMarginalPointwiseStatement.{0,0,0,0,0,0}
        m (allocatedExternalConditionalExcessExponent m) :=
  (exists_allocated_centered_narrow_prescribed_marginal_pointwise.{0,0,0,0,0,0} m).choose_spec

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {J : Fin m → Type} [∀ j, Fintype (J j)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U basis R σ}
    {hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}

namespace AllocatedExternalCandidateSampler

variable {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    (A : AllocatedExternalCandidateSampler B U basis S hb o hR hσ N poly hm τ ξ stride cells center)

theorem site_nonempty : Nonempty A.Site :=
  (allocatedParameterBox_nonempty B U basis S).to_subtype

noncomputable def physicalBox (hξ1 : ξ ≤ 1)
    (hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x) :
    A.Path → A.Site → integerBox N :=
  narrowPhysicalSiteMap (allocatedExternalCandidateRootBudget_nonneg B U basis S)
    A.trim_pos hξ1 N A.size_pos hmargin (fun t => t.val)
    (fun t => (allocatedParameterSite_sum_bound B U basis S t).trans_eq
      (allocatedExternalCandidateRootBudget_eq B U basis S).symm)

@[simp] theorem physicalBox_val (hξ1 : ξ ≤ 1)
    (hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x) (z : A.Path) (t : A.Site) :
    (A.physicalBox hξ1 hmargin z t).val = A.physical z t := rfl

end AllocatedExternalCandidateSampler

namespace AllocatedExternalCandidateSamplerFamily

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]

theorem conditional_excess
    (A : AllocatedExternalCandidateSamplerFamily B U basis S hb o hR hσ N poly hm τ ξ stride cells)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hσ1 : ∀ j, σ j ≤ 1) (C V : Fin m → ℝ≥0)
    (hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {P E : ℝ} (hP : 0 ≤ P) (hmSize : (m : ℝ) ≤ P)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (hX : (Fintype.card X : ℝ) ≤ P)
    (hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (hLP : (S.value : ℝ) ≤ Real.exp P)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hsP : ∀ x, (stride x : ℝ) ≤ Real.exp P)
    (hWP : allocatedExternalCandidateRootBudget B U basis S ≤ Real.exp P)
    (hτP : τ⁻¹ ≤ Real.exp P) (hτhalf : τ ≤ 1 / 2)
    (hτdim : (Fintype.card X : ℝ) * τ ≤ 1 / 2)
    (hξ1 : ξ ≤ 1) (hξP : ξ⁻¹ ≤ Real.exp P)
    (hsize : ∀ x, Real.exp ((max P E + allocatedExternalConditionalExcessExponent m) ^
      allocatedExternalConditionalExcessExponent m) ≤ (N x : ℝ))
    {rank : ℝ}
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun x => (N x : ℝ)) rank (U j) (poly j))
    (hRank : Real.exp ((max P E + allocatedExternalConditionalExcessExponent m) ^
      allocatedExternalConditionalExcessExponent m) ≤ rank)
    (hCells : cells.Nonempty) :
    ∃ (hbox : (integerBox N).Nonempty)
      (hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x),
      ∀ center : CoefficientTorus (K := LayerSamplerVariables G I n B) U,
      letI : Nonempty (A center).Site := (A center).site_nonempty
      (FiniteProbabilityWeights.uniformFinset (integerBox N) hbox).excessMass
        ((A center).law.siteLaw ((A center).physicalBox hξ1 hmargin))
        (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j)) ≤
          6 * positiveProjectionAccuracy E := by
  obtain ⟨hN, hbases, hbox, hmass, hmargin, hnormalizer, hsite⟩ :=
    (allocatedExternalConditionalExcessExponent_spec m).2 B U basis S hb o μ ν
      hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall hP hmSize hK hX hdim
      hRP hσP hcount hI hn hJ hAP hLP hCP hVP poly hp hm stride (A 0).stride_pos hsP
      (allocatedExternalCandidateRootBudget_nonneg B U basis S) hWP
      (A 0).trim_pos hτP hτhalf hτdim (A 0).narrow_pos hξ1 hξP N hsize hrank hRank cells hCells
  refine ⟨hbox, hmargin, ?_⟩
  intro center
  let : Nonempty (A center).Site := (A center).site_nonempty
  exact hsite (fun t : (A center).Site => t.val)
    (fun t k => (allocatedParameterSite_bound B U basis S t k).trans hLP)
    (fun t => (allocatedParameterSite_sum_bound B U basis S t).trans_eq
      (allocatedExternalCandidateRootBudget_eq B U basis S).symm) center

end AllocatedExternalCandidateSamplerFamily

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateProblem

variable {A} {L M : Type} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {outputCost outputMass outputScore : ℝ}

namespace Conclusion

variable (out : P.Conclusion outputCost outputMass outputScore)

local instance : Nonempty A.Site := A.site_nonempty

noncomputable def allSiteLaw (z : A.Path) : FiniteProbabilityWeights A.Site :=
  if hz : z ∈ out.retained then out.siteLaw ⟨z, hz⟩
  else FiniteProbabilityWeights.uniform A.Site

@[simp] theorem allSiteLaw_retained (z : out.retained) :
    out.allSiteLaw z.val = out.siteLaw z := by
  simp only [allSiteLaw, dite_eq_left z.property]

@[simp] theorem allSiteLaw_of_mem (z : A.Path) (hz : z ∈ out.retained) :
    out.allSiteLaw z = out.siteLaw ⟨z, hz⟩ := by
  exact out.allSiteLaw_retained ⟨z, hz⟩

theorem allSiteLaw_restricted_residual_eq
    {Ω : Type} (physical : A.Path → A.Site → Ω) (err : Ω → ℂ) :
    A.law.mean (fun z => if z ∈ out.retained then
      ‖(out.allSiteLaw z).complexMean (fun t => err (physical z t))‖ else 0) =
    A.law.mean (fun z => if hz : z ∈ out.retained then
      ‖(out.siteLaw ⟨z, hz⟩).complexMean (fun t => err (physical z t))‖ else 0) := by
  apply congrArg A.law.mean
  funext z
  by_cases hz : z ∈ out.retained
  · simp only [ite_eq_left hz, dite_eq_left hz, out.allSiteLaw_of_mem z hz]
  · simp only [ite_eq_right hz, dite_eq_right hz]

theorem allSiteLaw_productive_residual_le_retained
    {Ω : Type} (physical : A.Path → A.Site → Ω) (err : Ω → ℂ)
    (productive : Finset A.Path) (hproductive : productive ⊆ out.retained) :
    A.law.mean (fun z => if z ∈ productive then
      ‖(out.allSiteLaw z).complexMean (fun t => err (physical z t))‖ else 0) ≤
    A.law.mean (fun z => if hz : z ∈ out.retained then
      ‖(out.siteLaw ⟨z, hz⟩).complexMean (fun t => err (physical z t))‖ else 0) := by
  rw [← out.allSiteLaw_restricted_residual_eq physical err]
  apply A.law.mean_mono
  intro z
  by_cases hz : z ∈ productive
  · simp only [ite_eq_left hz, ite_eq_left (hproductive hz), le_refl]
  · simp only [ite_eq_right hz]
    split_ifs <;> positivity

theorem allSiteLaw_productive_residual_le
    {Ω : Type} (physical : A.Path → A.Site → Ω) (err : Ω → ℂ)
    (productive : Finset A.Path) (hproductive : productive ⊆ out.retained) {ε : ℝ}
    (hresidual : A.law.mean (fun z => if hz : z ∈ out.retained then
      ‖(out.siteLaw ⟨z, hz⟩).complexMean (fun t => err (physical z t))‖ else 0) ≤ ε) :
    A.law.mean (fun z => if z ∈ productive then
      ‖(out.allSiteLaw z).complexMean (fun t => err (physical z t))‖ else 0) ≤ ε :=
  (out.allSiteLaw_productive_residual_le_retained physical err productive hproductive).trans hresidual

end Conclusion
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
