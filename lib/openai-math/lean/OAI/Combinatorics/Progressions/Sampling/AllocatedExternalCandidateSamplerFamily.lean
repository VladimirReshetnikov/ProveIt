import OAI.Combinatorics.Progressions.Estimates.AllocatedCenteredNarrowPrescribedMarginal

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

noncomputable def allocatedExternalCandidateSides : LayerSamplerVariables G I n B → ℕ :=
  Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)

noncomputable def allocatedExternalCandidateRootBudget : ℝ :=
  Fintype.card (LayerSamplerVariables G I n B) * (S.value : ℝ)

theorem allocatedExternalCandidateRootBudget_eq :
    allocatedExternalCandidateRootBudget B U b S =
      allocatedPhysicalRootBudget B U b S (fun _ => 0) := by
  simp only [allocatedExternalCandidateRootBudget, allocatedPhysicalRootBudget,
    Int.cast_zero, abs_zero, Finset.sum_const_zero, zero_add]

theorem allocatedExternalCandidateRootBudget_nonneg :
    0 ≤ allocatedExternalCandidateRootBudget B U b S :=
  mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

noncomputable def allocatedExternalCandidateWidths (N : X → ℕ) (τ ξ : ℝ) :
    Option (LayerSamplerVariables G I n B) × X → ℝ :=
  narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n))
    (allocatedExternalCandidateRootBudget B U b S) τ ξ N

variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    (τ ξ : ℝ) (stride : X → ℕ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)

structure AllocatedExternalCandidateSampler : Prop where
  size_pos : ∀ x, 0 < N x
  trim_pos : 0 < τ
  narrow_pos : 0 < ξ
  stride_pos : ∀ x, 0 < stride x
  bases_nonempty : (trimmedIntegerBox N (spatialTrimMargin τ N)).Nonempty
  smooth_mass_pos : 0 < ∑' z, selectedResidueSmoothWeight stride cells
    (allocatedExternalCandidateWidths B U b S N τ ξ) z
  center_mass_pos : 0 < selectedJointDensityMass (trimmedIntegerBox N (spatialTrimMargin τ N))
    stride cells (allocatedExternalCandidateWidths B U b S N τ ξ)
    (allocatedCenteredJointDensity B U b hb o hR hσ S poly hm center)

namespace AllocatedExternalCandidateSampler

variable {B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

noncomputable abbrev sides (_A : AllocatedExternalCandidateSampler B U b S hb o hR hσ
    N poly hm τ ξ stride cells center) : LayerSamplerVariables G I n B → ℕ :=
  allocatedExternalCandidateSides B U b S

noncomputable abbrev widths (_A : AllocatedExternalCandidateSampler B U b S hb o hR hσ
    N poly hm τ ξ stride cells center) : Option (LayerSamplerVariables G I n B) × X → ℝ :=
  allocatedExternalCandidateWidths B U b S N τ ξ

noncomputable abbrev bases (_A : AllocatedExternalCandidateSampler B U b S hb o hR hσ
    N poly hm τ ξ stride cells center) : Finset (X → ℤ) :=
  trimmedIntegerBox N (spatialTrimMargin τ N)

abbrev Path (_A : AllocatedExternalCandidateSampler B U b S hb o hR hσ
    N poly hm τ ξ stride cells center) : Type _ :=
  trimmedIntegerBox N (spatialTrimMargin τ N) ×
    rectangularWeightIndices 0 (allocatedExternalCandidateWidths B U b S N τ ξ) 1

abbrev Site (_A : AllocatedExternalCandidateSampler B U b S hb o hR hσ
    N poly hm τ ξ stride cells center) : Type _ :=
  integerBox (allocatedExternalCandidateSides B U b S)

include A in
theorem widths_pos (i) : 0 < allocatedExternalCandidateWidths B U b S N τ ξ i :=
  narrowTrimmedSpatialWidths_pos (allocatedExternalCandidateRootBudget_nonneg B U b S)
    A.trim_pos A.narrow_pos N A.size_pos i

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

noncomputable def law : FiniteProbabilityWeights A.Path :=
  selectedJointFiniteLaw (trimmedIntegerBox N (spatialTrimMargin τ N)) A.bases_nonempty
    stride cells (allocatedExternalCandidateWidths B U b S N τ ξ) A.widths_pos A.smooth_mass_pos
    (allocatedCenteredJointDensity B U b hb o hR hσ S poly hm center)
    (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hm center) A.center_mass_pos

omit [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] in
def physical (z : A.Path) (site : A.Site) : X → ℤ :=
  jointIntegerPhysicalSite site.val (z.1.val, z.2.val)

omit [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] in
@[simp] theorem physical_eq (z : A.Path) (site : A.Site) :
    A.physical z site = jointIntegerPhysicalSite site.val (z.1.val, z.2.val) := rfl

theorem law_support (z : A.Path) (hz : 0 < A.law.weight z) :
    columnResiduePattern stride z.2.val ∈ cells ∧
    0 < allocatedCenteredJointDensity B U b hb o hR hσ S poly hm center z.1.val z.2.val :=
  selectedJointFiniteLaw_support (trimmedIntegerBox N (spatialTrimMargin τ N)) A.bases_nonempty
    stride cells (allocatedExternalCandidateWidths B U b S N τ ξ) A.widths_pos A.smooth_mass_pos
    (allocatedCenteredJointDensity B U b hb o hR hσ S poly hm center)
    (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hm center) A.center_mass_pos z hz

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    (τ ξ : ℝ) (stride : X → ℕ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))

abbrev AllocatedExternalCandidateSamplerFamily : Prop :=
  ∀ center : CoefficientTorus (K := LayerSamplerVariables G I n B) U,
    AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center

namespace AllocatedExternalCandidateSamplerFamily

variable {B U b S hb o hR hσ N poly hm τ ξ stride cells}
    (A : AllocatedExternalCandidateSamplerFamily B U b S hb o hR hσ N poly hm τ ξ stride cells)

abbrev Path := (A 0).Path

abbrev Site := (A 0).Site

def physical (z : A.Path) (site : A.Site) : X → ℤ :=
  (A 0).physical z site

theorem physical_eq_center
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (z : A.Path) (site : A.Site) :
    A.physical z site = (A center).physical z site := rfl

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

noncomputable def law (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U) :
    FiniteProbabilityWeights A.Path :=
  (A center).law

theorem law_eq_center
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U) :
    A.law center = (A center).law := rfl

variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]

theorem weight_measurable (z : A.Path) :
    Measurable (fun center => (A.law center).weight z) :=
  allocatedCenteredJointFiniteLaw_weight_measurable B U b hb o hR hσ S poly hm
    (trimmedIntegerBox N (spatialTrimMargin τ N)) (A 0).bases_nonempty
    stride cells (allocatedExternalCandidateWidths B U b S N τ ξ)
    (A 0).widths_pos (A 0).smooth_mass_pos (fun center => (A center).center_mass_pos) z

noncomputable def averagedLaw
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [IsProbabilityMeasure μ] : FiniteProbabilityWeights A.Path :=
  centeredFiniteMarginal μ A.law A.weight_measurable

theorem averagedLaw_weight
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [IsProbabilityMeasure μ] (z : A.Path) :
    (A.averagedLaw μ).weight z = ∫ center, (A.law center).weight z ∂μ := rfl

theorem averagedLaw_mean
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [IsProbabilityMeasure μ] (f : A.Path → ℝ) :
    (A.averagedLaw μ).mean f = ∫ center, (A.law center).mean f ∂μ :=
  centeredFiniteMarginal_mean μ A.law A.weight_measurable f

end AllocatedExternalCandidateSamplerFamily

end Erdos3.VectorPolynomial

end

end OAI
