import OAI.Combinatorics.Progressions.Geometry.SupportMaskComplexMean
import OAI.Combinatorics.Progressions.Sampling.AllocatedFullGridRecenteredCover

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type uG} [Fintype G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

variable (q : ℕ) [NeZero q]

variable (δ : ℝ)
variable (witnesses : (r : AllocatedPositiveResidue (dim := dim) B U b S q) →
  AllocatedFullGridResidueWitness (dim := dim) B U b S q r.val)
variable (hWitness : ∀ r, AllocatedFullGridResidueSampling.{uG,uI,uB,uJ,uQ,uX}
  B U b hR hσ S q (witnesses r) δ)

include hWitness in
theorem allocated_full_grid_weighted_sampled_error :
  ∀ {K : ℕ}, AllocatedBooleanRowsSampling.{uX,uJ,uG,uI,uB,uQ} m dim K (rowTypes) (rows) → ∀
    (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Q : Fin m → Type uQ} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d]
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

    (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset (Fin dim) // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)
    (CM Cf : ℝ≥0) (_hCM : 1 ≤ (CM : ℝ)) (_hfb : ∀ v, |f v| ≤ Cf)
    (_hmask : ∀ y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim)
      (allocatedPrincipalSides B U b S), ∀ j z, 0 ≤ allocatedIntegerKernelMask (O := rowTypes) B U b S x
    (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix (O := rowTypes) B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask (O := rowTypes) B U b S x
    (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix (O := rowTypes) B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ CM)
    (_hperiod : ∀ j, integerScalarLattice (rowTypes j) (q : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    {X : Type uX} [Fintype X] [DecidableEq X]
    {P₀ : ℝ} (_hP : 0 ≤ P₀) (_hn : (Fintype.card X : ℝ) ≤ P₀)
    (_hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P₀)
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hmp : ∀ j e, coefficients (p j) e ∈ U j)
    (stride : X → ℕ) (_hs : ∀ x, 0 < stride x)
    {R₁ S₀ ρ ε : ℝ} (_hS : 0 ≤ S₀) (_hSP : S₀ ≤ Real.exp P₀) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P₀) (_hεP : 1 / ε ≤ Real.exp P₀)
    (_hstride : ∀ x, (stride x : ℝ) ≤ S₀)
    (H : X → ℝ) (_hsize : ∀ x, Real.exp ((P₀ + K) ^ K) ≤ H x)
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H R₁ (U j) (p j))
    (_hR : Real.exp ((P₀ + K) ^ K) ≤ R₁)
    (cells : Finset (ColumnResiduePattern (Option (Fin dim)) X stride)) (_hcells : cells.Nonempty)
    (W : Option (Fin dim) × X → ℝ) (hW : ∀ z, 0 < W z) (_hwidth : ∀ z, ρ * H z.2 ≤ W z)
    {δFourier LFourier : ℝ} (_hδFourier : 0 < δFourier) (_hLFourier : 0 ≤ LFourier)
    (_hamb : (Fintype.card (JetAmbientIndex (rowTypes) J) : ℝ) ≤ LFourier)
    (_hδL : δFourier⁻¹ ≤ Real.exp LFourier),
    let A := Real.toNNReal (coefficientDeckPeriodCap (rowTypes) Q q) *
      CM ^ Fintype.card (LayerSamplerAxis I n) * Cf
    (allocatedErrorKernelLip B U b S (O := rowTypes) (Real.toNNReal δ) A C V : ℝ) ≤ Real.exp LFourier →
    Real.exp ((2 * LFourier + 2) ^ 4) ≤ Real.exp P₀ →
    Real.exp (2 * LFourier * (2 * LFourier + 2) ^ 4) *
      allocatedErrorKernelCap B U b S (O := rowTypes) (Real.toNNReal δ) A V ≤ Real.exp P₀ →
    let law := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let target := allocatedSupportedFullGridResidueProfile B U b hR hσ S q x hb o bW d f witnesses
    let mass := δ * A *
      (2 * (∑ j, (C j : ℝ) * ((Fintype.card (J j) : ℝ) + 1)) + 1) ^
        Fintype.card (Σ a : LayerSamplerAxis I n, (rowTypes) a.1)
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells W z,
      ∀ (Cweight : ℝ), 0 ≤ Cweight →
      ∀ weight : (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod q) →
          (Option (Fin dim) × X → ℤ) → ℂ,
      (∀ r z, ‖weight r z‖ ≤ Cweight) →
      let sample := fun z : Option (Fin dim) × X → ℤ =>
        physicalCubeRowSample (O := rowTypes) U d (rows) p hmp (standardPhysicalCubeOutput z)
      let error := fun z : Option (Fin dim) × X → ℤ =>
        law.complexMean (fun y₀ => weight (principalResidueLabel q y₀) z *
          (allocatedWholeMaskedCoveredProfile (O := rowTypes) B U b hR hσ S x (rows) hb o bW d y₀ q f (sample z) : ℂ)) -
        (law.fiberLaw (principalResidueLabel q)).complexMean (fun r => weight r z * target r (sample z))
      selectedResidueDensityMass stride cells W (fun z => ‖error z‖) ≤ Cweight * (mass + 2 * δFourier + ε) ∧
      ∀ φ : (Option (Fin dim) × X → ℤ) → ℂ, (∀ z, ‖φ z‖ ≤ 1) →
        ‖∑' z, ((selectedResidueSmoothPMF stride cells W hW hZ z).toReal : ℂ) *
          (error z * φ z)‖ ≤ Cweight * (mass + 2 * δFourier + ε) := by
  intro K hSampling x hb o Q _ bW d _ _ f CM Cf hCM hfb hmask hperiod C V hC hV
    X _ _ P₀ hP₀ hn hdim _ _ _ μ _ _ ν _ _ p hp hmp stride hs R₁ S₀ ρ ε
    hS hSP hρ hε hρP hεP hstride H hsize₁ hrank hR₁ cells hcells W hW hwidth
    δFourier LFourier hδFourier hLFourier hamb hδL A hLip hfreqP hcoeffP law target mass
  let sample := fun z : Option (Fin dim) × X → ℤ =>
    physicalCubeRowSample (O := rowTypes) U d (rows) p hmp (standardPhysicalCubeOutput z)
  let source := fun (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim)
      (allocatedPrincipalSides B U b S)) (z : Option (Fin dim) × X → ℤ) =>
    (allocatedWholeMaskedCoveredProfile (O := rowTypes) B U b hR hσ S x (rows) hb o bW d y₀ q f (sample z) : ℂ)
  let targetSample := fun r (z : Option (Fin dim) × X → ℤ) => target r (sample z)
  have hlocal (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod q)
      (hr : 0 < law.mass (Finset.univ.filter (fun y => principalResidueLabel q y = r))) :
      ∃ _hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells W z,
        selectedResidueDensityMass stride cells W
          (fun z => ‖(law.condition _ hr).complexMean (fun y => source y z) - targetSample r z‖)
          ≤ mass + 2 * δFourier + ε := by
    let rr : AllocatedPositiveResidue (dim := dim) B U b S q := ⟨r, hr⟩
    have hc := @hWitness rr
    dsimp only [AllocatedFullGridResidueSampling] at hc
    obtain ⟨hZ, hbound⟩ := @hc K hSampling x hb o Q _ bW d _ _ f CM Cf hCM hfb
      (hmask (witnesses rr).representative) hperiod C V hC hV
      X _ _ P₀ hP₀ hn hdim _ _ _ μ _ _ ν _ _ p hp hmp stride hs R₁ S₀ ρ ε
      hS hSP hρ hε hρP hεP hstride H hsize₁ hrank hR₁ cells hcells W hW hwidth
      δFourier LFourier hδFourier hLFourier hamb hδL hLip hfreqP hcoeffP
    refine ⟨hZ, ?_⟩
    have hid := allocatedSupportedFullGridResidueProfile_error B U b hR hσ S q x hb o bW d f witnesses rr
    have hfun :
        (fun z => ‖(law.condition _ hr).complexMean (fun y => source y z) - targetSample r z‖) =
        (fun z => ‖allocatedSelectedConditionalError (O := rowTypes) B U b hR hσ S x (rows)
          hb o bW d q (witnesses rr).representative (witnesses rr).positive
          (fun _ => True) f
          (allocatedFullGridSelectedApproximation B U b S rowSets (witnesses rr).expansion)
          (allocatedFullGridNaturalVolume B U b S rowSets) (sample z)‖) := by
      funext z
      exact congrArg norm (congrFun hid (sample z))
    rw [hfun]
    exact hbound
  obtain ⟨r₀, hr₀⟩ := (law.fiberLaw (principalResidueLabel q)).exists_weight_pos
  rw [law.fiberLaw_weight_eq_mass] at hr₀
  obtain ⟨hZ, _⟩ := hlocal r₀ hr₀
  have heach r hr := (hlocal r hr).choose_spec
  refine ⟨hZ, ?_⟩
  intro Cweight hCweight weight hweight sample' error
  refine ⟨?_, ?_⟩
  · have h := selectedResidue_supported_fiber_weighted_error law (principalResidueLabel q)
      stride cells W hW hZ source targetSample weight hCweight hweight
      (fun _ => mass + 2 * δFourier + ε) heach
    simpa only [FiniteProbabilityWeights.mean_const] using h
  · intro φ hφ
    have h := selectedResidue_supported_fiber_weighted_test_error law (principalResidueLabel q)
      stride cells W hW hZ source targetSample weight hCweight hweight
      (fun _ => mass + 2 * δFourier + ε) heach φ hφ
    simpa only [FiniteProbabilityWeights.mean_const] using h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type uG} [Fintype G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

variable (q : ℕ) [NeZero q]

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type uQ} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset (Fin dim) // t ∈ boundedBooleanJetRows (Fin dim) ((Sigma.fst (Subtype.val a)).val + 1)}) → ℝ) → ℝ)
variable (witnesses : (r : AllocatedPositiveResidue (dim := dim) B U b S q) →
  AllocatedFullGridResidueWitness (dim := dim) B U b S q r.val)
variable (T : Fin m → ℝ)

local notation "labelType" => PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod q
local notation "law" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
local notation "mask" => allocatedPhysicalGridMask B U b S (rowTypes) T hb o bW d
local notation "rawProfile" => allocatedSupportedFullGridResidueProfile B U b hR hσ S q x hb o bW d f witnesses

noncomputable def allocatedClippedFullGridResidueProfile (r : labelType) (y : EuclideanJetLayers U (rowTypes)) : ℂ :=
  mask y * rawProfile r y

noncomputable def allocatedFullGridWeightedProfileError (weight : labelType → ℂ)
    (y : EuclideanJetLayers U (rowTypes)) : ℂ :=
  (law).complexMean (fun y₀ => weight (principalResidueLabel q y₀) *
    (allocatedWholeMaskedCoveredProfile B U b hR hσ S x (rows) hb o bW d y₀ q f y : ℂ)) -
    ((law).fiberLaw (principalResidueLabel q)).complexMean (fun r => weight r * rawProfile r y)

noncomputable def allocatedClippedFullGridWeightedError (weight : labelType → ℂ)
    (y : EuclideanJetLayers U (rowTypes)) : ℂ :=
  (law).complexMean (fun y₀ => weight (principalResidueLabel q y₀) *
    (allocatedWholeMaskedCoveredProfile B U b hR hσ S x (rows) hb o bW d y₀ q f y : ℂ)) -
    ((law).fiberLaw (principalResidueLabel q)).complexMean (fun r => weight r *
      allocatedClippedFullGridResidueProfile B U b hR hσ S q x hb o bW d f witnesses T r y)

variable (hT : ∀ j, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
  ((2 : ℝ) ^ Fintype.card (Fin dim) * ((Fintype.card (Fin dim) : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
variable (hσ1 : ∀ j, σ j ≤ 1)

include hT hσ1 in
theorem allocatedClippedFullGridWeightedError_eq (weight : labelType → ℂ)
    (y : EuclideanJetLayers U (rowTypes)) :
    allocatedClippedFullGridWeightedError B U b hR hσ S q x hb o bW d f witnesses T weight y =
      mask y * allocatedFullGridWeightedProfileError B U b hR hσ S q x hb o bW d f witnesses weight y := by
  exact supportMask_weighted_complexMean_difference (law) ((law).fiberLaw (principalResidueLabel q))
    (principalResidueLabel q) weight
    (fun y₀ => (allocatedWholeMaskedCoveredProfile B U b hR hσ S x (rows) hb o bW d y₀ q f y : ℂ))
    (fun r => rawProfile r y) (mask y)
    (fun y₀ => allocatedPhysicalGridMask_fixes_source B U b S (rowTypes) T hb o bW d hR hσ x
      (rows) hT hσ1 y₀ q f y)

include hT hσ1 in
theorem allocatedClippedFullGridWeightedError_norm (weight : labelType → ℂ)
    (y : EuclideanJetLayers U (rowTypes)) :
    ‖allocatedClippedFullGridWeightedError B U b hR hσ S q x hb o bW d f witnesses T weight y‖ ≤
      ‖allocatedFullGridWeightedProfileError B U b hR hσ S q x hb o bW d f witnesses weight y‖ := by
  rw [allocatedClippedFullGridWeightedError_eq B U b hR hσ S q x hb o bW d f witnesses T hT hσ1,
    norm_mul]
  exact (mul_le_mul_of_nonneg_right (allocatedPhysicalGridMask_norm B U b S (rowTypes) T hb o bW d y)
    (norm_nonneg _)).trans_eq (one_mul _)

variable {X : Type uX} [Fintype X] [DecidableEq X]
variable (stride : X → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (Fin dim)) X stride))
variable (widths : Option (Fin dim) × X → ℝ) (hwidths : ∀ z, 0 < widths z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells widths z)
variable (sample : (Option (Fin dim) × X → ℤ) → EuclideanJetLayers U
  (fun j : Fin m => (boundedBooleanJetRows (Fin dim) (j.val + 1) : Type)))
variable (weight : (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod q) →
  (Option (Fin dim) × X → ℤ) → ℂ)

omit [DecidableEq X] in
include hT hσ1 hwidths hZ in
theorem allocatedClippedFullGridWeightedError_sampled {η : ℝ}
    (hraw : selectedResidueDensityMass stride cells widths (fun z =>
      ‖allocatedFullGridWeightedProfileError B U b hR hσ S q x hb o bW d f witnesses
        (fun r => weight r z) (sample z)‖) ≤ η) :
    selectedResidueDensityMass stride cells widths (fun z =>
      ‖allocatedClippedFullGridWeightedError B U b hR hσ S q x hb o bW d f witnesses T
        (fun r => weight r z) (sample z)‖) ≤ η := by
  exact (selectedResidueDensityMass_mono stride cells widths hwidths hZ
    (fun z => allocatedClippedFullGridWeightedError_norm B U b hR hσ S q x hb o bW d f witnesses T
      hT hσ1 (fun r => weight r z) (sample z))).trans hraw

omit [DecidableEq X] in
include hT hσ1 in
theorem allocatedClippedFullGridWeightedError_test {η : ℝ}
    (hraw : ∀ φ : (Option (Fin dim) × X → ℤ) → ℂ, (∀ z, ‖φ z‖ ≤ 1) →
      ‖∑' z, ((selectedResidueSmoothPMF stride cells widths hwidths hZ z).toReal : ℂ) *
        (allocatedFullGridWeightedProfileError B U b hR hσ S q x hb o bW d f witnesses
          (fun r => weight r z) (sample z) * φ z)‖ ≤ η)
    (φ : (Option (Fin dim) × X → ℤ) → ℂ) (hφ : ∀ z, ‖φ z‖ ≤ 1) :
    ‖∑' z, ((selectedResidueSmoothPMF stride cells widths hwidths hZ z).toReal : ℂ) *
      (allocatedClippedFullGridWeightedError B U b hR hσ S q x hb o bW d f witnesses T
        (fun r => weight r z) (sample z) * φ z)‖ ≤ η := by
  have hmask (z : Option (Fin dim) × X → ℤ) : ‖mask (sample z) * φ z‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (allocatedPhysicalGridMask_norm B U b S (rowTypes) T hb o bW d (sample z))).trans (hφ z)
  have h := hraw (fun z => mask (sample z) * φ z) hmask
  convert h using 1
  congr 1
  apply tsum_congr
  intro z
  rw [allocatedClippedFullGridWeightedError_eq B U b hR hσ S q x hb o bW d f witnesses T hT hσ1]
  ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type uG} [Fintype G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

variable (q : ℕ) [NeZero q]

variable (δ : ℝ)
variable (witnesses : (r : AllocatedPositiveResidue (dim := dim) B U b S q) →
  AllocatedFullGridResidueWitness (dim := dim) B U b S q r.val)
variable (hWitness : ∀ r, AllocatedFullGridResidueSampling.{uG,uI,uB,uJ,uQ,uX}
  B U b hR hσ S q (witnesses r) δ)

include hWitness in
theorem allocated_full_grid_spatial_weighted_error :
  ∀ {K : ℕ}, AllocatedBooleanRowsSampling.{uX,uJ,uG,uI,uB,uQ} m dim K (rowTypes) (rows) → ∀
    (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Q : Fin m → Type uQ} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d]
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

    (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset (Fin dim) // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)
    (CM Cf : ℝ≥0) (_hCM : 1 ≤ (CM : ℝ)) (_hfb : ∀ v, |f v| ≤ Cf)
    (_hmask : ∀ y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim)
      (allocatedPrincipalSides B U b S), ∀ j z, 0 ≤ allocatedIntegerKernelMask (O := rowTypes) B U b S x
    (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix (O := rowTypes) B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask (O := rowTypes) B U b S x
    (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix (O := rowTypes) B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ CM)
    (_hperiod : ∀ j, integerScalarLattice (rowTypes j) (q : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    {X : Type uX} [Fintype X] [DecidableEq X]
    {P₀ : ℝ} (_hP : 0 ≤ P₀) (_hn : (Fintype.card X : ℝ) ≤ P₀)
    (_hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P₀)
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hmp : ∀ j e, coefficients (p j) e ∈ U j)
    (stride : X → ℕ) (_hs : ∀ x, 0 < stride x)
    {R₁ S₀ ρ ε : ℝ} (_hS : 0 ≤ S₀) (_hSP : S₀ ≤ Real.exp P₀) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P₀) (_hεP : 1 / ε ≤ Real.exp P₀)
    (_hstride : ∀ x, (stride x : ℝ) ≤ S₀)
    (H : X → ℝ) (_hsize : ∀ x, Real.exp ((P₀ + K) ^ K) ≤ H x)
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H R₁ (U j) (p j))
    (_hR : Real.exp ((P₀ + K) ^ K) ≤ R₁)
    (cells : Finset (ColumnResiduePattern (Option (Fin dim)) X stride)) (_hcells : cells.Nonempty)
    (W : Option (Fin dim) × X → ℝ) (hW : ∀ z, 0 < W z) (_hwidth : ∀ z, ρ * H z.2 ≤ W z)
    {δFourier LFourier : ℝ} (_hδFourier : 0 < δFourier) (_hLFourier : 0 ≤ LFourier)
    (_hamb : (Fintype.card (JetAmbientIndex (rowTypes) J) : ℝ) ≤ LFourier)
    (_hδL : δFourier⁻¹ ≤ Real.exp LFourier),
    let A := Real.toNNReal (coefficientDeckPeriodCap (rowTypes) Q q) *
      CM ^ Fintype.card (LayerSamplerAxis I n) * Cf
    (allocatedErrorKernelLip B U b S (O := rowTypes) (Real.toNNReal δ) A C V : ℝ) ≤ Real.exp LFourier →
    Real.exp ((2 * LFourier + 2) ^ 4) ≤ Real.exp P₀ →
    Real.exp (2 * LFourier * (2 * LFourier + 2) ^ 4) *
      allocatedErrorKernelCap B U b S (O := rowTypes) (Real.toNNReal δ) A V ≤ Real.exp P₀ →
    let law := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let target := allocatedSupportedFullGridResidueProfile B U b hR hσ S q x hb o bW d f witnesses
    let mass := δ * A *
      (2 * (∑ j, (C j : ℝ) * ((Fintype.card (J j) : ℝ) + 1)) + 1) ^
        Fintype.card (Σ a : LayerSamplerAxis I n, (rowTypes) a.1)
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells W z,
      ∀ (Mkernel : ℕ) (hMkernel : 0 < Mkernel) (selection : Fin dim ↪ G)
        (hx : GoodScalarKernelTuple selection (1 / (Mkernel : ℝ)) Mkernel x)
        (Hsp : X → ℝ) (_hHsp : ∀ t, 0 < Hsp t)
        (Wsp : ℝ) (hWsp : 0 ≤ Wsp)
        (_hRoot : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ Wsp)
        (mesh : ℝ) (_hmesh : 0 < mesh)
        (_hSp : integerScalarLattice (Unit ⊕ Fin dim) (q : ℤ) ≤
          pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
            (scalarCubeDifferenceMatrix x) selection)
            (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ))
              (scalarCubeDifferenceMatrix x) selection)),
      let Cweight := ((q : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
        anisotropicSpatialDensityCap selection (1 / (Mkernel : ℝ))) ^ Fintype.card X
      let weight := fun r (z : Option (Fin dim) × X → ℤ) =>
        allocatedResidueSpatialWindowWeight B U b S x X hMkernel selection hx q Hsp hWsp mesh r
          (standardPhysicalCubeOutput z)
      let sample := fun z : Option (Fin dim) × X → ℤ =>
        physicalCubeRowSample (O := rowTypes) U d (rows) p hmp (standardPhysicalCubeOutput z)
      let error := fun z : Option (Fin dim) × X → ℤ =>
        law.complexMean (fun y₀ => weight (principalResidueLabel q y₀) z *
          (allocatedWholeMaskedCoveredProfile (O := rowTypes) B U b hR hσ S x (rows) hb o bW d y₀ q f (sample z) : ℂ)) -
        (law.fiberLaw (principalResidueLabel q)).complexMean (fun r => weight r z * target r (sample z))
      selectedResidueDensityMass stride cells W (fun z => ‖error z‖) ≤ Cweight * (mass + 2 * δFourier + ε) ∧
      ∀ φ : (Option (Fin dim) × X → ℤ) → ℂ, (∀ z, ‖φ z‖ ≤ 1) →
        ‖∑' z, ((selectedResidueSmoothPMF stride cells W hW hZ z).toReal : ℂ) *
          (error z * φ z)‖ ≤ Cweight * (mass + 2 * δFourier + ε) := by
  intro K hSampling x hb o Q _ bW d _ _ f CM Cf hCM hfb hmask hperiod C V hC hV
    X _ _ P₀ hP₀ hn hdim _ _ _ μ _ _ ν _ _ p hp hmp stride hs R₁ S₀ ρ ε
    hS hSP hρ hε hρP hεP hstride H hsize₁ hrank hR₁ cells hcells W hW hwidth
    δFourier LFourier hδFourier hLFourier hamb hδL A hLip hfreqP hcoeffP law target mass
  have hprevious := allocated_full_grid_weighted_sampled_error B U b hR hσ S q δ witnesses hWitness (K := K)
  obtain ⟨hZ, hbound⟩ := @hprevious hSampling x hb o Q _ bW d _ _ f CM Cf hCM hfb hmask hperiod C V hC hV
    X _ _ P₀ hP₀ hn hdim _ _ _ μ _ _ ν _ _ p hp hmp stride hs R₁ S₀ ρ ε
    hS hSP hρ hε hρP hεP hstride H hsize₁ hrank hR₁ cells hcells W hW hwidth
    δFourier LFourier hδFourier hLFourier hamb hδL hLip hfreqP hcoeffP
  refine ⟨hZ, ?_⟩
  intro Mkernel hMkernel selection hx Hsp hHsp Wsp hWsp hRoot mesh hmesh hSp Cweight weight sample error
  have hCweight : 0 ≤ Cweight :=
    pow_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg q) _)
      (anisotropicSpatialDensityCap_nonneg selection (one_div_nonneg.mpr (Nat.cast_nonneg Mkernel)))) _
  exact hbound Cweight hCweight weight (fun r z =>
    allocatedResidueSpatialWindowWeight_norm_le B U b S x X hMkernel selection hx q Hsp hWsp mesh
      hHsp hRoot hmesh hSp r (standardPhysicalCubeOutput z))

end Erdos3.VectorPolynomial

end

end OAI
