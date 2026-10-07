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
theorem allocated_full_grid_reconstructed_separated_comparison
    {pAccuracy pSampling w v E : ℝ} (hpAccuracy : 0 ≤ pAccuracy)
    (hAccuracySampling : pAccuracy ≤ pSampling) (hw : 0 ≤ w) (hv : 0 ≤ v) (hE : 0 ≤ E)
    (hdimSmall : dim ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pAccuracy)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ pAccuracy) (hn₁ : ∀ j, (n j : ℝ) ≤ pAccuracy)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ pAccuracy)
    (M₀ : ℕ) (hqM : q ≤ M₀ ^ (m + 1)) (hM₀ : (M₀ : ℝ) ≤ Real.exp pAccuracy)
    (hS₁ : (S.value : ℝ) ≤ Real.exp pSampling)
    (hδ : δ ≤ allocatedSitePrimitiveTolerance m pAccuracy w v E) (hEbudget : E + 4 ≤ pAccuracy) :
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
    (_hCMexp : (CM : ℝ) ≤ Real.exp w) (_hCfexp : (Cf : ℝ) ≤ Real.exp v)
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
    (modulus : ℕ) (_hdiv : modulus ∣ q)
    (_hperiod : ∀ j, integerScalarLattice (rowTypes j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hCexp : ∀ j, (C j : ℝ) ≤ Real.exp pAccuracy) (_hVexp : ∀ j, (V j : ℝ) ≤ Real.exp pAccuracy)
    {X : Type uX} [Fintype X] [DecidableEq X]
    {P₀ : ℝ} (_hP : 0 ≤ P₀) (_hn : (Fintype.card X : ℝ) ≤ P₀)
    (_hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P₀)
    (_hbudget : allocatedSiteErrorFourierOutput m pSampling w v ≤ P₀)
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
    {R₁ S₀ ρ : ℝ} (_hS : 0 ≤ S₀) (_hSP : S₀ ≤ Real.exp P₀) (_hρ : 0 < ρ)
    (_hρP : 1 / ρ ≤ Real.exp P₀)
    (_hstride : ∀ x, (stride x : ℝ) ≤ S₀)
    (N : X → ℕ) (_hsize : ∀ x, Real.exp ((P₀ + K) ^ K) ≤ (N x : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) R₁ (U j) (p j))
    (_hR : Real.exp ((P₀ + K) ^ K) ≤ R₁),
    ∀ (W : ℝ), 0 ≤ W →
    let H := trimmedSpatialRootScale ρ N stride
    let T := trimmedSpatialSlopeScale W ρ N stride
    let outputVolume := ∏ t, ∏ i, physicalSpatialOutputScale (Fin dim) (H t) (T t) S.value i
    let point := physicalCubeRowSample (O := rowTypes) U d (rows) p hmp
    let law := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let target := allocatedSupportedFullGridResidueProfile B U b hR hσ S q x hb o bW d f witnesses
    ∀ (reference : (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod q) →
        PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
      (base : X → ℤ)
      (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
      (V₀ : Option (LayerSamplerVariables G I n B) × X → ℝ),
    (∀ z, 0 < V₀ z) → (0 < ∑' z, selectedResidueSmoothWeight stride cells V₀ z) →
    (∀ t, Fintype.card (Option (LayerSamplerVariables G I n B)) *
      allocatedPhysicalEntryBudget B U b S (fun _ => 0) ≤ H t) →
    (∀ t, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H t) →
    ∀ (weight : (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod q) →
        cells → (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) (Cweight Z : ℝ),
    0 ≤ Cweight → 0 < Z →
    (∀ r a v, v ∈ spatialWindow H 4 → ‖weight r a v‖ ≤ Cweight / outputVolume) →
    let reconstruct := fun r (a : cells) => physicalResidueReconstruction
      (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (reference r))
      (allocatedPhysicalCubeDirections B U b S x (reference r)) base
      (boundedColumnResidueRepresentative stride a.val) stride
    let factor := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + W) / (S.value : ℝ)) ^ dim) ^ Fintype.card X
    ‖(law.complexMean (fun y => ∑ a : cells, (selectedResidueCellWeight stride cells V₀ a : ℂ) *
        ∑ v ∈ spatialWindow H 4, weight (principalResidueLabel q y) a v *
          (allocatedWholeMaskedCoveredProfile (O := rowTypes) B U b hR hσ S x (rows)
            hb o bW d y modulus f (point (reconstruct (principalResidueLabel q y) a v)) : ℂ)) -
      (law.fiberLaw (principalResidueLabel q)).complexMean (fun r =>
        ∑ a : cells, (selectedResidueCellWeight stride cells V₀ a : ℂ) *
          ∑ v ∈ spatialWindow H 4, weight r a v * target r (point (reconstruct r a v)))) / (Z : ℂ)‖ ≤
      (Cweight * factor * Real.exp (-E)) / Z := by
  intro K hSampling x hb o Q _ bW d _ _ f CM Cf hCM hfb hCMexp hCfexp hmask modulus hdiv hperiod C V hC hV
    hCexp hVexp X _ _ P₀ hP₀ hn hdim hbudget _ _ _ μ _ _ ν _ _ p hp hmp stride hs R₁ S₀ ρ
    hS hSP hρ hρP hstride N hsize₁ hrank hR₁ W hW H T outputVolume point law target
    reference base cells V₀ hV₀ hZ₀ hrows hscale weight Cweight Z hCweight hZ hweight reconstruct factor
  have hδnn : Real.toNNReal δ ≤ 1 := Real.toNNReal_le_one.mpr
    (hδ.trans (allocatedSitePrimitiveTolerance_le_one m hpAccuracy hw hv hE))
  have hrowdim : Fintype.card (Fin dim) ≤ m + 1 := by
    simpa only [Fintype.card_fin] using hdimSmall
  have hshare : (physicalIdealErrorShare E 1)⁻¹ ≤ Real.exp pSampling := by
    rw [physicalIdealErrorShare_inv]
    exact Real.exp_le_exp.mpr (by linarith)
  obtain ⟨hLF, hpP, hamb, hδL, hLip, hfreq, hcoeff⟩ :=
    allocatedSiteErrorPrimitive_fourier_budget B U b S (rows) hrowdim
      (fun _ => Subtype.val_injective) hb bW M₀ q hqM (Real.toNNReal δ) CM Cf C V
      (hpAccuracy.trans hAccuracySampling) hw hv (hvars.trans hAccuracySampling)
      (fun j => (hI j).trans hAccuracySampling) (fun j => (hn₁ j).trans hAccuracySampling)
      (fun j => (hJ j).trans hAccuracySampling) hδnn
      (hM₀.trans (Real.exp_le_exp.mpr hAccuracySampling)) hS₁
      (fun j => (hCexp j).trans (Real.exp_le_exp.mpr hAccuracySampling))
      (fun j => (hVexp j).trans (Real.exp_le_exp.mpr hAccuracySampling)) hCMexp hCfexp hshare
  have heP := Real.exp_le_exp.mpr hbudget
  have hεP : 1 / physicalIdealErrorShare E 1 ≤ Real.exp P₀ := by
    simpa only [one_div] using hshare.trans (Real.exp_le_exp.mpr (hpP.trans hbudget))
  have hprevious := allocated_full_grid_reconstructed_comparison B U b hR hσ S q δ witnesses
    hWitness (K := K) hSampling
  have hbound := @hprevious x hb o Q _ bW d _ _ f CM Cf hCM hfb hmask modulus hdiv hperiod C V hC hV
    X _ _ P₀ hP₀ hn hdim _ _ _ μ _ _ ν _ _ p hp hmp stride hs R₁ S₀ ρ (physicalIdealErrorShare E 1)
    hS hSP hρ (physicalIdealErrorShare_pos E 1) hρP hεP hstride N hsize₁ hrank hR₁
    (physicalIdealErrorShare E 1) (allocatedSiteErrorFourierInput m pSampling w v)
    (physicalIdealErrorShare_pos E 1) hLF hamb hδL hLip (hfreq.trans heP) (hcoeff.trans heP)
    W hW reference base cells V₀ hV₀ hZ₀ hrows hscale weight Cweight Z hCweight hZ hweight
  have hmass := allocatedSiteSpatial_primitive_error_budget B U b (rows) hrowdim
    (fun _ => Subtype.val_injective) hb bW M₀ q hqM CM Cf C hpAccuracy hw hvars hI hn₁ hJ
    hM₀ hCexp hCMexp hCfexp hδ (le_refl (physicalIdealErrorShare E 1))
    (le_refl (physicalIdealErrorShare E 1))
  have hfactor : 0 ≤ factor := mul_nonneg
    (pow_nonneg (div_nonneg (by norm_num) smoothProbabilityProfile_pos_zero.le) _)
    (pow_nonneg (pow_nonneg (div_nonneg (by linarith) (Nat.cast_nonneg S.value)) _) _)
  exact hbound.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmass (mul_nonneg hCweight hfactor)) hZ.le)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
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

variable {X : Type uX} [Fintype X] [DecidableEq X]
variable (stride : X → ℕ) (hs : ∀ t, 0 < stride t) (modulus : ℕ) [NeZero modulus]
variable [NeZero (residueRefinedPeriod modulus stride)]
local notation "refined" => residueRefinedPeriod modulus stride

variable (δ : ℝ)
variable (witnesses : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus stride)) →
  AllocatedFullGridResidueWitness (dim := dim) B U b S (residueRefinedPeriod modulus stride) r.val)
variable (hWitness : ∀ r, AllocatedFullGridResidueSampling.{uG,uI,uB,uJ,uQ,uX}
  B U b hR hσ S (residueRefinedPeriod modulus stride) (witnesses r) δ)

include hWitness hs in
theorem allocated_full_grid_recentered_separated_comparison
    {pAccuracy pSampling w v E : ℝ} (hpAccuracy : 0 ≤ pAccuracy)
    (hAccuracySampling : pAccuracy ≤ pSampling) (hw : 0 ≤ w) (hv : 0 ≤ v) (hE : 0 ≤ E)
    (hdimSmall : dim ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pAccuracy)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ pAccuracy) (hn₁ : ∀ j, (n j : ℝ) ≤ pAccuracy)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ pAccuracy)
    (M₀ : ℕ) (hqM : refined ≤ M₀ ^ (m + 1)) (hM₀ : (M₀ : ℝ) ≤ Real.exp pAccuracy)
    (hS₁ : (S.value : ℝ) ≤ Real.exp pSampling)
    (hδ : δ ≤ allocatedSitePrimitiveTolerance m pAccuracy w v E) (hEbudget : E + 4 ≤ pAccuracy) :
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
    (_hCMexp : (CM : ℝ) ≤ Real.exp w) (_hCfexp : (Cf : ℝ) ≤ Real.exp v)
    (_hmask : ∀ y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim)
      (allocatedPrincipalSides B U b S), ∀ j z, 0 ≤ allocatedIntegerKernelMask (O := rowTypes) B U b S x
    (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j refined
    (integerResidueMatrix (allocatedNonkernelJetMatrix (O := rowTypes) B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) refined) z ∧
  allocatedIntegerKernelMask (O := rowTypes) B U b S x
    (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j refined
    (integerResidueMatrix (allocatedNonkernelJetMatrix (O := rowTypes) B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) refined) z ≤ CM)
    (_hperiod : ∀ j, integerScalarLattice (rowTypes j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hCexp : ∀ j, (C j : ℝ) ≤ Real.exp pAccuracy) (_hVexp : ∀ j, (V j : ℝ) ≤ Real.exp pAccuracy)
    {P₀ : ℝ} (_hP : 0 ≤ P₀) (_hn : (Fintype.card X : ℝ) ≤ P₀)
    (_hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P₀)
    (_hbudget : allocatedSiteErrorFourierOutput m pSampling w v ≤ P₀)
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hmp : ∀ j e, coefficients (p j) e ∈ U j)
    {R₁ S₀ ρ : ℝ} (_hS : 0 ≤ S₀) (_hSP : S₀ ≤ Real.exp P₀) (_hρ : 0 < ρ)
    (_hρP : 1 / ρ ≤ Real.exp P₀)
    (_hstride : ∀ x, (stride x : ℝ) ≤ S₀)
    (N : X → ℕ) (_hsize : ∀ x, Real.exp ((P₀ + K) ^ K) ≤ (N x : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) R₁ (U j) (p j))
    (_hR : Real.exp ((P₀ + K) ^ K) ≤ R₁),
    ∀ (W : ℝ) (hW : 0 ≤ W),
    let H := trimmedSpatialRootScale ρ N stride
    let point := physicalCubeRowSample (O := rowTypes) U d (rows) p hmp
    let law := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let target := allocatedSupportedFullGridResidueProfile B U b hR hσ S refined x hb o bW d f witnesses
    let reference := allocatedSupportedWholeReference (dim := dim) B U b S refined
    ∀ (base : X → ℤ)
      (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
      (ξ : ℝ), 0 < ξ →
    let V₀ := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W ρ ξ N
    (0 < ∑' z, selectedResidueSmoothWeight stride cells V₀ z) →
    (∀ t, Fintype.card (Option (LayerSamplerVariables G I n B)) *
      allocatedPhysicalEntryBudget B U b S (fun _ => 0) ≤ H t) →
    (∀ t, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H t) →
    ∀ (M : ℕ) (hM : 0 < M) (selection : Fin dim ↪ G)
      (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
      (mesh : ℝ), 0 < mesh →
    (allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W) →
    (integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage
        (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)) →
    ∀ (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ), (∀ v, ‖test v‖ ≤ 1) →
    ∀ (Z : ℝ), 0 < Z →
    let profile := fun y z => (allocatedWholeMaskedCoveredProfile (O := rowTypes)
      B U b hR hσ S x (rows) hb o bW d y modulus f z : ℂ)
    let reconstruct := allocatedWholeResidueReconstruction B U b S X modulus stride reference x base
    let weight := allocatedRecenteredResidueWeight (τ := ρ) B U b S X modulus stride reference x hM selection hx
      N hW mesh base cells test
    let cap := ((modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
      anisotropicSpatialDensityCap selection (1 / (M : ℝ))) ^ Fintype.card X
    let factor := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + W) / (S.value : ℝ)) ^ dim) ^ Fintype.card X
    ‖(law.complexMean (allocatedRecenteredProfileTerm (τ := ρ) (ξ := ξ)
        B U b S X modulus stride reference x hM selection hx N hW mesh base cells point test profile) -
      (law.fiberLaw (principalResidueLabel refined)).complexMean (fun r =>
        ∑ a : cells, (selectedResidueCellWeight stride cells V₀ a : ℂ) *
          ∑ v ∈ spatialWindow H 4, weight r a v * target r (point (reconstruct r a.val v)))) / (Z : ℂ)‖ ≤
      (cap * factor * Real.exp (-E)) / Z := by
  intro K hSampling x hb o Q _ bW d _ _ f CM Cf hCM hfb hCMexp hCfexp hmask hperiod C V hC hV
    hCexp hVexp P₀ hP₀ hn hdim hbudget _ _ _ μ _ _ ν _ _ p hp hmp R₁ S₀ ρ
    hS hSP hρ hρP hstride N hsize₁ hrank hR₁ W hW H point law target reference
    base cells ξ hξ V₀ hZ₀ hrows hscale M hM selection hx mesh hmesh hroot hspatial test htest Z hZ
    profile reconstruct weight cap factor
  have hN (t : X) : 0 < N t := Nat.cast_pos.mp ((Real.exp_pos _).trans_le (hsize₁ t))
  have hV₀ : ∀ z, 0 < V₀ z := narrowTrimmedSpatialWidths_pos hW hρ hξ N hN
  have hcap : 0 ≤ cap := pow_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg modulus) _)
    (anisotropicSpatialDensityCap_nonneg selection (one_div_nonneg.mpr (Nat.cast_nonneg M)))) _
  have hweight := allocatedRecenteredResidueWeight_norm_le B U b S X modulus stride reference x
    hM selection hx N hW mesh base cells test hs hN hρ hroot hmesh hspatial htest
  have hprevious := allocated_full_grid_reconstructed_separated_comparison B U b hR hσ S refined δ witnesses
    hWitness hpAccuracy hAccuracySampling hw hv hE hdimSmall hvars hI hn₁ hJ M₀ hqM hM₀ hS₁ hδ hEbudget (K := K) hSampling
  have hbound := @hprevious x hb o Q _ bW d _ _ f CM Cf hCM hfb hCMexp hCfexp hmask
    modulus ⟨∏ t, stride t, rfl⟩ hperiod C V hC hV hCexp hVexp
    X _ _ P₀ hP₀ hn hdim hbudget _ _ _ μ _ _ ν _ _ p hp hmp stride hs R₁ S₀ ρ
    hS hSP hρ hρP hstride N hsize₁ hrank hR₁ W hW reference base cells V₀ hV₀ hZ₀ hrows hscale
    weight cap Z hcap hZ hweight
  have hsource : law.complexMean
      (allocatedRecenteredProfileTerm (τ := ρ) (ξ := ξ)
        B U b S X modulus stride reference x hM selection hx N hW mesh base cells point test profile) =
      law.complexMean (fun y => ∑ a : cells, (selectedResidueCellWeight stride cells V₀ a : ℂ) *
        ∑ v ∈ spatialWindow H 4, weight (principalResidueLabel refined y) a v *
          profile y (point (reconstruct (principalResidueLabel refined y) a.val v))) := by
    apply law.complexMean_congr_support
    intro y hy
    exact allocatedRecenteredProfileTerm_residue_weight B U b S X modulus stride reference x
      hM selection hx N hW mesh base cells point test profile y
      (allocatedSupportedWholeReference_label B U b S refined y hy)
  rw [hsource]
  exact hbound

end Erdos3.VectorPolynomial

end

end OAI
