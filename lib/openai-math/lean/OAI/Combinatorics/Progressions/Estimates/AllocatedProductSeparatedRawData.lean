import OAI.Combinatorics.Progressions.Estimates.AllocatedGenuineCoverFromRaw
import OAI.Combinatorics.Progressions.Estimates.AllocatedProductEarlyCoarsening

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators NNReal

theorem allocatedProductCoarse_error_bound {G X : Type*} [Fintype G] [Fintype X]
    (dim : ℕ) (selection : Fin dim ↪ G)
    {M modulus : ℕ} {P E D W L Z : ℝ}
    (hP : 0 ≤ P) (hM : 0 < M) (hMP : (M : ℝ) ≤ Real.exp P)
    (hmodulus : (modulus : ℝ) ≤ Real.exp (P ^ 2))
    (hdim : ((dim + 1 : ℕ) : ℝ) ≤ P)
    (hG : (Fintype.card G : ℝ) ≤ P) (hX : (Fintype.card X : ℝ) ≤ P)
    (hL : 1 ≤ L) (hW : 0 ≤ W) (hD : D ≤ Real.exp P) (hWL : W ≤ D * L)
    (hZ : 0 < Z) (hZi : Z⁻¹ ≤ 2) :
    let cap := ((modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
      anisotropicSpatialDensityCap selection (1 / (M : ℝ))) ^ Fintype.card X
    let factor := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + W) / L) ^ dim) ^ Fintype.card X
    2 * ((cap * factor * Real.exp (-allocatedOriginalCoverAccuracy P (E + 1))) / Z) +
      Real.exp (-(E + 1)) ≤ Real.exp (-E) := by
  intro cap factor
  have hcap : cap * factor ≤ Real.exp (coefficientErrorSpatialLog P) :=
    (coefficientErrorSpatialFactor_exp_bound dim X selection hP hM hMP hmodulus
      hdim hG hX hL hW hD hWL).2
  have hsmall : cap * factor * Real.exp (-allocatedOriginalCoverAccuracy P (E + 1)) ≤
      Real.exp (-(E + 4)) := by
    calc
      _ ≤ Real.exp (coefficientErrorSpatialLog P) *
          Real.exp (-allocatedOriginalCoverAccuracy P (E + 1)) :=
        mul_le_mul_of_nonneg_right hcap (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; unfold allocatedOriginalCoverAccuracy; ring
  have hmul := mul_le_mul_of_nonneg_right hZi hZ.le
  rw [inv_mul_cancel₀ hZ.ne'] at hmul
  have hZhalf : 1 / 2 ≤ Z := by linarith only [hmul]
  calc
    _ ≤ 2 * (Real.exp (-(E + 4)) / Z) + Real.exp (-(E + 1)) := by gcongr
    _ ≤ (2 * Real.exp (-(E + 4)) + Real.exp (-(E + 4))) / Z +
        Real.exp (-(E + 1)) := by
      rw [← mul_div_assoc]
      gcongr
      exact le_add_of_nonneg_right (Real.exp_pos _).le
    _ ≤ Real.exp (-E) := originalTupleProjectionPrecision_bound hZhalf

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
theorem allocated_product_original_separated_comparison
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

    (δideal : ℝ≥0) (_hδideal : 0 < δideal) (_hδideal1 : δideal ≤ 1)
    (_hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchartinv : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (_hsmall : ∀ j, R j ≤ allocatedProductGridRadius (G := G) B
      (fun k : Fin m => boundedBooleanJetRows (Fin dim) (k.val + 1)) Cinv j)
    (CM Cf : ℝ≥0) (_hCM : 1 ≤ (CM : ℝ)) (_hfb : ∀ v, |(allocatedPhysicalLongIdeal B U b hR S rowSets δideal) v| ≤ Cf)
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
    let target := allocatedProductFullGridResidueProfile B U b hR hσ S refined x hb o bW d witnesses δideal
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
    ∀ (Qratio : ℝ≥0), 1 ≤ Qratio → (1 + W) / (S.value : ℝ) ≤ Qratio →
    ∀ (εshift : ℝ), 0 ≤ εshift → (3 + 2 * mesh) + 2 * εshift ≤ 4 →
    (∀ t, Fintype.card (Option (LayerSamplerVariables G I n B)) *
      (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0)) ≤ εshift * H t) →
    ∀ (longReference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value)
        (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus stride)) →
      PrincipalAxisTuples (α := Fin dim) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
        (allocatedPrincipalSides B U b S)),
    (∀ u r, principalResidueLabel refined (longReference u r) = r) →
    ∀ (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ), (∀ v, ‖test v‖ ≤ 1) →
    ∀ (Z : ℝ), 0 < Z →
    let profile := fun y z => (allocatedWholeMaskedCoveredProfile (O := rowTypes)
      B U b hR hσ S x (rows) hb o bW d y modulus (allocatedPhysicalLongIdeal B U b hR S rowSets δideal) z : ℂ)
    let reconstruct := allocatedWholeResidueReconstruction B U b S X modulus stride reference x base
    let weight := allocatedRecenteredResidueWeight (τ := ρ) B U b S X modulus stride reference x hM selection hx
      N hW mesh base cells test
    let cap := ((modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
      anisotropicSpatialDensityCap selection (1 / (M : ℝ))) ^ Fintype.card X
    let factor := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + W) / (S.value : ℝ)) ^ dim) ^ Fintype.card X
    let mass := law.mean (allocatedRecenteredProfileMass (W := W) (τ := ρ) (ξ := ξ)
      B U b S X modulus stride reference x N base cells point profile)
    let shiftError := Fintype.card X *
      ((modulus : ℝ)^Fintype.card (Unit ⊕ Fin dim) *
        (anisotropicSpatialDensityLip selection (1 / (M : ℝ)) * Qratio) * (8 * mesh + εshift)) *
      (1 + (modulus : ℝ)^Fintype.card (Unit ⊕ Fin dim) *
        anisotropicSpatialDensityCap selection (1 / (M : ℝ)))^Fintype.card X
    ‖(law.complexMean (allocatedResidueWeightedProfileTerm (τ := ρ) (ξ := ξ)
        B U b S x X hM selection hx modulus stride longReference N hW mesh base cells point test profile) -
      (law.fiberLaw (principalResidueLabel refined)).complexMean (fun r =>
        ∑ a : cells, (selectedResidueCellWeight stride cells V₀ a : ℂ) *
          ∑ v ∈ spatialWindow H 4, weight r a v * target r (point (reconstruct r a.val v)))) / (Z : ℂ)‖ ≤
      (shiftError * mass + cap * factor * Real.exp (-E)) / Z := by
  intro K hSampling x hb o Q _ bW d _ _ δideal hδideal hδideal1 hσ1 Cinv hCinv hchartinv hsmall CM Cf hCM hfb hCMexp hCfexp hmask hperiod C V hC hV
    hCexp hVexp P₀ hP₀ hn hdim hbudget _ _ _ μ _ _ ν _ _ p hp hmp R₁ S₀ ρ
    hS hSP hρ hρP hstride N hsize₁ hrank hR₁ W hW H point law target reference
    base cells ξ hξ V₀ hZ₀ hrows hscale M hM selection hx mesh hmesh hroot hspatial
    Qratio hQratio hratio εshift hεshift hmargin hshiftSize longReference href test htest Z hZ
    profile reconstruct weight cap factor mass shiftError
  have hN (t : X) : 0 < N t := Nat.cast_pos.mp ((Real.exp_pos _).trans_le (hsize₁ t))
  have hshift := allocatedResidueWeightedReference_recenter_supported (ξ := ξ) B U b S X modulus stride
    longReference x hM selection hx N hW mesh base cells point test
    hs hN hρ href Qratio hQratio hratio hroot hspatial hmesh hεshift hmargin hshiftSize htest profile Z hZ
  have hprevious := allocated_product_recentered_separated_comparison B U b hR hσ S stride hs modulus δ witnesses
    hWitness hpAccuracy hAccuracySampling hw hv hE hdimSmall hvars hI hn₁ hJ M₀ hqM hM₀ hS₁ hδ hEbudget (K := K) hSampling
  have hcover := @hprevious x hb o Q _ bW d _ _ δideal hδideal hδideal1 hσ1 Cinv hCinv hchartinv hsmall CM Cf hCM hfb hCMexp hCfexp hmask hperiod C V hC hV
    hCexp hVexp P₀ hP₀ hn hdim hbudget _ _ _ μ _ _ ν _ _ p hp hmp R₁ S₀ ρ
    hS hSP hρ hρP hstride N hsize₁ hrank hR₁ W hW
    base cells ξ hξ hZ₀ hrows hscale M hM selection hx mesh hmesh hroot hspatial test htest Z hZ
  dsimp only at hcover
  rw [sub_div] at hcover ⊢
  calc
    _ ≤ ‖law.complexMean (allocatedResidueWeightedProfileTerm (τ := ρ) (ξ := ξ)
          B U b S x X hM selection hx modulus stride longReference N hW mesh base cells point test profile) / (Z : ℂ) -
        law.complexMean (allocatedRecenteredProfileTerm (τ := ρ) (ξ := ξ)
          B U b S X modulus stride reference x hM selection hx N hW mesh base cells point test profile) / (Z : ℂ)‖ +
        ‖law.complexMean (allocatedRecenteredProfileTerm (τ := ρ) (ξ := ξ)
          B U b S X modulus stride reference x hM selection hx N hW mesh base cells point test profile) / (Z : ℂ) -
        (law.fiberLaw (principalResidueLabel refined)).complexMean (fun r =>
          ∑ a : cells, (selectedResidueCellWeight stride cells V₀ a : ℂ) *
            ∑ v ∈ spatialWindow H 4, weight r a v * target r (point (reconstruct r a.val v))) / (Z : ℂ)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ shiftError * mass / Z + (cap * factor * Real.exp (-E)) / Z := add_le_add hshift hcover
    _ = _ := (add_div _ _ _).symm

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
theorem allocated_product_original_separated_bounded_comparison
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

    (δideal : ℝ≥0) (_hδideal : 0 < δideal) (_hδideal1 : δideal ≤ 1)
    (_hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchartinv : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (_hsmall : ∀ j, R j ≤ allocatedProductGridRadius (G := G) B
      (fun k : Fin m => boundedBooleanJetRows (Fin dim) (k.val + 1)) Cinv j)
    (CM Cf : ℝ≥0) (_hCM : 1 ≤ (CM : ℝ)) (_hfb : ∀ v, |(allocatedPhysicalLongIdeal B U b hR S rowSets δideal) v| ≤ Cf)
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
    let target := allocatedProductFullGridResidueProfile B U b hR hσ S refined x hb o bW d witnesses δideal
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
    ∀ (Qratio : ℝ≥0), 1 ≤ Qratio → (1 + W) / (S.value : ℝ) ≤ Qratio →
    ∀ (εshift : ℝ), 0 ≤ εshift → (3 + 2 * mesh) + 2 * εshift ≤ 4 →
    (∀ t, Fintype.card (Option (LayerSamplerVariables G I n B)) *
      (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0)) ≤ εshift * H t) →
    ∀ (longReference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value)
        (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus stride)) →
      PrincipalAxisTuples (α := Fin dim) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
        (allocatedPrincipalSides B U b S)),
    (∀ u r, principalResidueLabel refined (longReference u r) = r) →
    ∀ (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ), (∀ v, ‖test v‖ ≤ 1) →
    ∀ (Z : ℝ), 0 < Z →
    let profile := fun y z => (allocatedWholeMaskedCoveredProfile (O := rowTypes)
      B U b hR hσ S x (rows) hb o bW d y modulus (allocatedPhysicalLongIdeal B U b hR S rowSets δideal) z : ℂ)
    let reconstruct := allocatedWholeResidueReconstruction B U b S X modulus stride reference x base
    let weight := allocatedRecenteredResidueWeight (τ := ρ) B U b S X modulus stride reference x hM selection hx
      N hW mesh base cells test
    let cap := ((modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
      anisotropicSpatialDensityCap selection (1 / (M : ℝ))) ^ Fintype.card X
    let factor := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + W) / (S.value : ℝ)) ^ dim) ^ Fintype.card X
    let shiftError := Fintype.card X *
      ((modulus : ℝ)^Fintype.card (Unit ⊕ Fin dim) *
        (anisotropicSpatialDensityLip selection (1 / (M : ℝ)) * Qratio) * (8 * mesh + εshift)) *
      (1 + (modulus : ℝ)^Fintype.card (Unit ⊕ Fin dim) *
        anisotropicSpatialDensityCap selection (1 / (M : ℝ)))^Fintype.card X
    ‖(law.complexMean (allocatedResidueWeightedProfileTerm (τ := ρ) (ξ := ξ)
        B U b S x X hM selection hx modulus stride longReference N hW mesh base cells point test profile) -
      (law.fiberLaw (principalResidueLabel refined)).complexMean (fun r =>
        ∑ a : cells, (selectedResidueCellWeight stride cells V₀ a : ℂ) *
          ∑ v ∈ spatialWindow H 4, weight r a v * target r (point (reconstruct r a.val v)))) / (Z : ℂ)‖ ≤
      (shiftError * (factor * Real.exp (allocatedSiteSpatialMassLog (allocatedComparisonDimension m pAccuracy) w v + 1)) + cap * factor * Real.exp (-E)) / Z := by
  intro K hSampling x hb o Q _ bW d _ _ δideal hδideal hδideal1 hσ1 Cinv hCinv hchartinv hsmall CM Cf hCM hfb hCMexp hCfexp hmask hperiod C V hC hV
    hCexp hVexp P₀ hP₀ hn hdim hbudget _ _ _ μ _ _ ν _ _ p hp hmp R₁ S₀ ρ
    hS hSP hρ hρP hstride N hsize₁ hrank hR₁ W hW H point law target reference
    base cells ξ hξ V₀ hZ₀ hrows hscale M hM selection hx mesh hmesh hroot hspatial
    Qratio hQratio hratio εshift hεshift hmargin hshiftSize longReference href test htest Z hZ
    profile reconstruct weight cap factor shiftError
  have hprevious := allocated_product_original_separated_comparison B U b hR hσ S stride hs modulus δ witnesses
    hWitness hpAccuracy hAccuracySampling hw hv hE hdimSmall hvars hI hn₁ hJ M₀ hqM hM₀ hS₁ hδ hEbudget (K := K) hSampling
  have hcomparison := @hprevious x hb o Q _ bW d _ _ δideal hδideal hδideal1 hσ1 Cinv hCinv hchartinv hsmall CM Cf hCM hfb hCMexp hCfexp hmask hperiod C V hC hV
    hCexp hVexp P₀ hP₀ hn hdim hbudget _ _ _ μ _ _ ν _ _ p hp hmp R₁ S₀ ρ
    hS hSP hρ hρP hstride N hsize₁ hrank hR₁ W hW
    base cells ξ hξ hZ₀ hrows hscale M hM selection hx mesh hmesh hroot hspatial
    Qratio hQratio hratio εshift hεshift hmargin hshiftSize longReference href test htest Z hZ
  have hdiv : modulus ∣ refined := ⟨∏ t, stride t, rfl⟩
  have hperiodRef (j : Fin m) : integerScalarLattice (rowTypes j) (refined : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range :=
    (integerScalarLattice_nat_refinement (rowTypes j) hdiv).trans (hperiod j)
  have hmaskCoarse (y : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim)
      (allocatedPrincipalSides B U b S)) (j : Fin m) (z : rowTypes j → ℤ) :
      0 ≤ allocatedIntegerKernelMask (O := rowTypes) B U b S x (rows) j modulus
        (integerResidueMatrix (allocatedNonkernelJetMatrix (O := rowTypes) B U b S x
          (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y) (rows) j
          (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y)) modulus) z ∧
      allocatedIntegerKernelMask (O := rowTypes) B U b S x (rows) j modulus
        (integerResidueMatrix (allocatedNonkernelJetMatrix (O := rowTypes) B U b S x
          (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y) (rows) j
          (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y)) modulus) z ≤ CM := by
    have heq := coefficientResidueMultiplier_eq_of_periods (scalarKernelIntegerJet x (j.val + 1) (rows j))
      (allocatedNonkernelJetMatrix (O := rowTypes) B U b S x
        (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y) (rows) j
        (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y))
      modulus refined _ _ (hperiod j) (hperiodRef j) rfl rfl z
    simpa only [allocatedIntegerKernelMask, heq] using hmask y j z
  have hcoarse : modulus ≤ M₀ ^ (m + 1) :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne refined)) hdiv).trans hqM
  have hmassPrevious := allocatedWholeProfile_recentered_separated_mass B U b hR hσ S modulus
    hpAccuracy hAccuracySampling hw hv (by linarith) hdimSmall hvars hI hn₁ hJ M₀ hcoarse hM₀ hS₁ (K := K) hSampling
  have hmass := @hmassPrevious x hb o Q _ bW d _ _ (allocatedPhysicalLongIdeal B U b hR S rowSets δideal) CM Cf hCM hfb hCMexp hCfexp
    hmaskCoarse hperiod C V hC hV hCexp hVexp X _ _ P₀ hP₀ hn hdim hbudget
    _ _ _ μ _ _ ν _ _ p hp hmp stride hs R₁ S₀ ρ hS hSP hρ hρP hstride N hsize₁ hrank hR₁
    W hW ξ hξ reference base cells hZ₀ hrows hscale
  have hshift0 : 0 ≤ shiftError := by
    have hκ : 0 ≤ 1 / (M : ℝ) := one_div_nonneg.mpr (Nat.cast_nonneg M)
    have hLip := anisotropicSpatialDensityLip_nonneg selection hκ
    have hCap := anisotropicSpatialDensityCap_nonneg selection hκ
    positivity
  exact hcomparison.trans (div_le_div_of_nonneg_right
    (add_le_add (mul_le_mul_of_nonneg_left hmass hshift0) le_rfl) hZ.le)

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
theorem allocated_product_original_separated_exponential_mesh
    {pAccuracy pSampling w v E Psp : ℝ} (hpAccuracy : 0 ≤ pAccuracy)
    (hAccuracySampling : pAccuracy ≤ pSampling) (hw : 0 ≤ w) (hv : 0 ≤ v) (hE : 0 ≤ E)
    (hPsp : 0 ≤ Psp) (hdimSp : ((dim + 1 : ℕ) : ℝ) ≤ Psp)
    (hGsp : (Fintype.card G : ℝ) ≤ Psp) (hXsp : (Fintype.card X : ℝ) ≤ Psp)
    (hperiodSp : (modulus : ℝ) ≤ Real.exp (Psp ^ 2))
    (hdimSmall : dim ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pAccuracy)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ pAccuracy) (hn₁ : ∀ j, (n j : ℝ) ≤ pAccuracy)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ pAccuracy)
    (M₀ : ℕ) (hqM : refined ≤ M₀ ^ (m + 1)) (hM₀ : (M₀ : ℝ) ≤ Real.exp pAccuracy)
    (hS₁ : (S.value : ℝ) ≤ Real.exp pSampling)
    (hδ : δ ≤ allocatedSitePrimitiveTolerance m pAccuracy w v (allocatedOriginalCoverAccuracy Psp E))
    (hEbudget : allocatedOriginalCoverAccuracy Psp E + 4 ≤ pAccuracy) :
  let shiftSize := allocatedOriginalCoverMesh m Psp pAccuracy w v E
  ∀ (mesh : ℝ), 0 < mesh → mesh ≤ shiftSize →
  ∀ {K : ℕ}, 2 ≤ K → AllocatedBooleanRowsSampling.{uX,uJ,uG,uI,uB,uQ} m dim K (rowTypes) (rows) → ∀
    (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Q : Fin m → Type uQ} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d]
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

    (δideal : ℝ≥0) (_hδideal : 0 < δideal) (_hδideal1 : δideal ≤ 1)
    (_hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchartinv : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (_hsmall : ∀ j, R j ≤ allocatedProductGridRadius (G := G) B
      (fun k : Fin m => boundedBooleanJetRows (Fin dim) (k.val + 1)) Cinv j)
    (CM Cf : ℝ≥0) (_hCM : 1 ≤ (CM : ℝ)) (_hfb : ∀ v, |(allocatedPhysicalLongIdeal B U b hR S rowSets δideal) v| ≤ Cf)
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
    (_hgeometry : allocatedSeparatedGeometryLog m Psp pAccuracy pSampling w v E ≤ P₀)
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
    ∀ (W : ℝ) (hW : 0 ≤ W) (D : ℝ), D ≤ Real.exp Psp → W ≤ D * S.value →
    let H := trimmedSpatialRootScale ρ N stride
    let point := physicalCubeRowSample (O := rowTypes) U d (rows) p hmp
    let law := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let target := allocatedProductFullGridResidueProfile B U b hR hσ S refined x hb o bW d witnesses δideal
    let reference := allocatedSupportedWholeReference (dim := dim) B U b S refined
    ∀ (base : X → ℤ)
      (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
      (ξ : ℝ), 0 < ξ →
    let V₀ := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W ρ ξ N
    (0 < ∑' z, selectedResidueSmoothWeight stride cells V₀ z) →
    ∀ (M : ℕ) (hM : 0 < M), (M : ℝ) ≤ Real.exp Psp →
    ∀ (selection : Fin dim ↪ G) (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x),
    (allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W) →
    (integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage
        (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)) →
    ∀ (longReference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value)
        (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus stride)) →
      PrincipalAxisTuples (α := Fin dim) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
        (allocatedPrincipalSides B U b S)),
    (∀ u r, principalResidueLabel refined (longReference u r) = r) →
    ∀ (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ), (∀ v, ‖test v‖ ≤ 1) →
    ∀ (Z : ℝ), 0 < Z → Z⁻¹ ≤ 2 →
    let profile := fun y z => (allocatedWholeMaskedCoveredProfile (O := rowTypes)
      B U b hR hσ S x (rows) hb o bW d y modulus (allocatedPhysicalLongIdeal B U b hR S rowSets δideal) z : ℂ)
    let reconstruct := allocatedWholeResidueReconstruction B U b S X modulus stride reference x base
    let weight := allocatedRecenteredResidueWeight (τ := ρ) B U b S X modulus stride reference x hM selection hx
      N hW mesh base cells test
    ‖(law.complexMean (allocatedResidueWeightedProfileTerm (τ := ρ) (ξ := ξ)
        B U b S x X hM selection hx modulus stride longReference N hW mesh base cells point test profile) -
      (law.fiberLaw (principalResidueLabel refined)).complexMean (fun r =>
        ∑ a : cells, (selectedResidueCellWeight stride cells V₀ a : ℂ) *
          ∑ v ∈ spatialWindow H 4, weight r a v * target r (point (reconstruct r a.val v)))) / (Z : ℂ)‖ ≤
      Real.exp (-E) := by
  intro shiftSize mesh hmeshPos hmeshLe K hK hSampling x hb o Q _ bW d _ _ δideal hδideal hδideal1 hσ1 Cinv hCinv hchartinv hsmall CM Cf hCM hfb hCMexp hCfexp hmask hperiod C V hC hV
    hCexp hVexp P₀ hP₀ hn hdim hbudget hgeometry _ _ _ μ _ _ ν _ _ p hp hmp R₁ S₀ ρ
    hS hSP hρ hρP hstride N hsize₁ hrank hR₁ W hW D hD hWD H point law target reference
    base cells ξ hξ V₀ hZ₀ M hM hMP selection hx hroot hspatial
    longReference href test htest Z hZ hZi profile reconstruct weight
  have hmesh := allocatedOriginalCoverMesh_spec m hPsp hpAccuracy hw hv hE
  have hN (t : X) : 0 < N t := Nat.cast_pos.mp ((Real.exp_pos _).trans_le (hsize₁ t))
  have hH (t : X) : 0 < H t :=
    (trimmedSpatial_scales_pos hW hρ N stride t (hN t) (hs t)).1
  have hgeom := allocatedOriginalCover_separated_geometry m (Fintype.card (LayerSamplerVariables G I n B))
    N stride hPsp hpAccuracy hAccuracySampling hw hv hE hgeometry hK hvars (Nat.cast_nonneg S.value) hS₁
    hρ hρP hs (fun t => (hstride t).trans hSP) hsize₁
  have hentry : allocatedPhysicalEntryBudget B U b S (fun _ => 0) =
      1 + ((Fintype.card (LayerSamplerVariables G I n B) : ℝ) + 1) * S.value := by
    simp only [allocatedPhysicalEntryBudget, allocatedPhysicalRootBudget, Int.cast_zero,
      abs_zero, Finset.sum_const_zero, zero_add]
    ring
  have hshiftSize (t : X) : Fintype.card (Option (LayerSamplerVariables G I n B)) *
      (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0)) ≤ shiftSize * H t := by
    simpa only [hentry, Fintype.card_option, Nat.cast_add, Nat.cast_one] using (hgeom t).1
  have hscale (t : X) : 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H t := (hgeom t).2
  have hmesh1 : shiftSize ≤ 1 := by linarith [hmesh.2.1]
  have hrows (t : X) : Fintype.card (Option (LayerSamplerVariables G I n B)) *
      allocatedPhysicalEntryBudget B U b S (fun _ => 0) ≤ H t := by
    have hsmall := mul_le_mul_of_nonneg_right hmesh1 (hH t).le
    nlinarith [hshiftSize t, hH t]
  have hnum := allocatedOriginalCover_error_bound_mesh m dim selection
    hPsp hpAccuracy hw hv hE hM hMP hperiodSp hdimSp hGsp hXsp
    (by exact_mod_cast S.positive) hW hD hWD hZ hZi mesh hmeshPos hmeshLe
  have hEcover : 0 ≤ allocatedOriginalCoverAccuracy Psp E := by
    have := coefficientErrorSpatialLog_nonneg hPsp
    unfold allocatedOriginalCoverAccuracy
    positivity
  have hprevious := allocated_product_original_separated_bounded_comparison B U b hR hσ S stride hs modulus δ witnesses
    hWitness hpAccuracy hAccuracySampling hw hv hEcover hdimSmall hvars hI hn₁ hJ M₀ hqM hM₀ hS₁ hδ hEbudget (K := K) hSampling
  have hcomparison := @hprevious x hb o Q _ bW d _ _ δideal hδideal hδideal1 hσ1 Cinv hCinv hchartinv hsmall CM Cf hCM hfb hCMexp hCfexp hmask hperiod C V hC hV
    hCexp hVexp P₀ hP₀ hn hdim hbudget _ _ _ μ _ _ ν _ _ p hp hmp R₁ S₀ ρ
    hS hSP hρ hρP hstride N hsize₁ hrank hR₁ W hW
    base cells ξ hξ hZ₀ hrows hscale M hM selection hx mesh hmeshPos hroot hspatial
    (Real.toNNReal (1 + D)) hnum.1 hnum.2.1 shiftSize hmesh.1.le
    (show (3 + 2 * mesh) + 2 * shiftSize ≤ 4 by linarith [hmesh.2.1]) hshiftSize
    longReference href test htest Z hZ
  exact hcomparison.trans hnum.2.2

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
theorem allocated_product_ideal_separated_exponential_comparison
    {pAccuracy pSampling w v e E Psp : ℝ} (hpAccuracy : 0 ≤ pAccuracy)
    (hAccuracySampling : pAccuracy ≤ pSampling) (hw : 0 ≤ w) (hv : 0 ≤ v) (he : 0 ≤ e) (hE : 0 ≤ E)
    (hPsp : 0 ≤ Psp) (hdimSp : ((dim + 1 : ℕ) : ℝ) ≤ Psp)
    (hGsp : (Fintype.card G : ℝ) ≤ Psp) (hXsp : (Fintype.card X : ℝ) ≤ Psp)
    (hperiodSp : (modulus : ℝ) ≤ Real.exp (Psp ^ 2))
    (hdimSmall : dim ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pAccuracy)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ pAccuracy) (hn₁ : ∀ j, (n j : ℝ) ≤ pAccuracy)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ pAccuracy)
    (M₀ : ℕ) (hqM : refined ≤ M₀ ^ (m + 1)) (hM₀ : (M₀ : ℝ) ≤ Real.exp pAccuracy)
    (hS₁ : (S.value : ℝ) ≤ Real.exp pSampling)
    (hδ : δ ≤ allocatedSitePrimitiveTolerance m pAccuracy w v (allocatedOriginalCoverAccuracy Psp E))
    (hEbudget : allocatedOriginalCoverAccuracy Psp E + 4 ≤ pAccuracy)
    (hmaskLog : allocatedSiteKernelMaskLog m Psp ≤ w)
    (hidealLog : allocatedIdealProfileLog m pAccuracy e ≤ v) :
  let shiftSize := allocatedOriginalCoverMesh m Psp pAccuracy w v E
  ∀ (mesh : ℝ), 0 < mesh → mesh ≤ shiftSize →
  ∀ {K : ℕ}, 2 ≤ K → AllocatedBooleanRowsSampling.{uX,uJ,uG,uI,uB,uQ} m dim K (rowTypes) (rows) →
    ∀ (δideal : ℝ≥0), 0 < δideal → δideal ≤ 1 → (δideal : ℝ)⁻¹ ≤ Real.exp e →
    (∀ j, (R j)⁻¹ ≤ Real.exp pAccuracy) →
    let _f := allocatedPhysicalLongIdeal B U b hR S rowSets δideal
    ∀ (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Q : Fin m → Type uQ} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d]
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

    (_hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchartinv : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (_hsmall : ∀ j, R j ≤ allocatedProductGridRadius (G := G) B
      (fun k : Fin m => boundedBooleanJetRows (Fin dim) (k.val + 1)) Cinv j)
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
    (_hgeometry : allocatedSeparatedGeometryLog m Psp pAccuracy pSampling w v E ≤ P₀)
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
    ∀ (W : ℝ) (hW : 0 ≤ W) (D : ℝ), D ≤ Real.exp Psp → W ≤ D * S.value →
    let H := trimmedSpatialRootScale ρ N stride
    let point := physicalCubeRowSample (O := rowTypes) U d (rows) p hmp
    let law := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let target := allocatedProductFullGridResidueProfile B U b hR hσ S refined x hb o bW d witnesses δideal
    let reference := allocatedSupportedWholeReference (dim := dim) B U b S refined
    ∀ (base : X → ℤ)
      (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
      (ξ : ℝ), 0 < ξ →
    let V₀ := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W ρ ξ N
    (0 < ∑' z, selectedResidueSmoothWeight stride cells V₀ z) →
    ∀ (M : ℕ) (hM : 0 < M), (M : ℝ) ≤ Real.exp Psp →
    ∀ (selection : Fin dim ↪ G) (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x),
    (allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W) →
    (integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage
        (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)) →
    ∀ (longReference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value)
        (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus stride)) →
      PrincipalAxisTuples (α := Fin dim) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
        (allocatedPrincipalSides B U b S)),
    (∀ u r, principalResidueLabel refined (longReference u r) = r) →
    ∀ (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ), (∀ v, ‖test v‖ ≤ 1) →
    ∀ (Z : ℝ), 0 < Z → Z⁻¹ ≤ 2 →
    let reconstruct := allocatedWholeResidueReconstruction B U b S X modulus stride reference x base
    let weight := allocatedRecenteredResidueWeight (τ := ρ) B U b S X modulus stride reference x hM selection hx
      N hW mesh base cells test
    ‖allocatedWholeIdealReference (τ := ρ) (ξ := ξ)
        B U b hR hσ S x
        (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) (j.val + 1) → Finset (Fin dim)))
        X hM selection hx modulus stride longReference hb o bW d
        N hW mesh base cells (physicalCubeEuclideanSample U d p hmp) test Z δideal -
      (law.fiberLaw (principalResidueLabel refined)).complexMean (fun r =>
        ∑ a : cells, (selectedResidueCellWeight stride cells V₀ a : ℂ) *
          ∑ v ∈ spatialWindow H 4, weight r a v * target r (point (reconstruct r a.val v))) / (Z : ℂ)‖ ≤
      Real.exp (-E) := by
  intro shiftSize mesh hmeshPos hmeshLe K hK hSampling δideal hδideal hδideal1 hδe hRi f
    x hb o Q _ bW d _ _ hσ1 Cinv hCinv hchartinv hsmall hperiod C V hC hV hCexp hVexp P₀ hP₀ hn hdim hbudget hgeometry
    _ _ _ μ _ _ ν _ _ p hp hmp R₁ S₀ ρ hS hSP hρ hρP hstride N hsize₁ hrank hR₁
    W hW D hD hWD H point law target reference base cells ξ hξ V₀ hZ₀ M hM hMP selection hx
    hroot hspatial longReference href test htest Z hZ hZi reconstruct weight
  let CM : ℝ≥0 := ⟨Real.exp (allocatedSiteKernelMaskLog m Psp), (Real.exp_pos _).le⟩
  let Cf : ℝ≥0 := ⟨Real.exp (allocatedIdealProfileLog m pAccuracy e), (Real.exp_pos _).le⟩
  have hCM : 1 ≤ (CM : ℝ) := Real.one_le_exp_iff.mpr (allocatedSiteKernelMaskLog_nonneg m hPsp)
  have hfb := allocatedPhysicalLongIdeal_primitive_bound B U b hR S rowSets hpAccuracy he
    (by simpa only [Fintype.card_fin] using hdimSmall) hvars hI hn₁ hRi δideal hδideal hδe
  have hrows (j : Fin m) (r : rowSets j) : r.val.card ≤ j.val + 1 :=
    (mem_boundedBooleanJetRows (j.val + 1) r.val).mp r.property
  have hqdim : Fintype.card (Fin dim) ≤ m + 1 := by simpa only [Fintype.card_fin] using hdimSmall
  have hprevious := allocated_product_original_separated_exponential_mesh B U b hR hσ S stride hs modulus δ
    witnesses hWitness hpAccuracy hAccuracySampling hw hv hE hPsp hdimSp hGsp hXsp hperiodSp hdimSmall
    hvars hI hn₁ hJ M₀ hqM hM₀ hS₁ hδ hEbudget mesh hmeshPos hmeshLe hK hSampling
  have hcomparison := @hprevious x hb o Q _ bW d _ _ δideal hδideal hδideal1 hσ1 Cinv hCinv hchartinv hsmall CM Cf hCM hfb
    (Real.exp_le_exp.mpr hmaskLog) (Real.exp_le_exp.mpr hidealLog)
    (fun y j z => ⟨(allocatedIntegerKernelMask_bound B U b S x rows hM selection hx hqdim
      (fun _ => Subtype.val_injective) hrows j _ _ z).1,
      allocatedIntegerKernelMask_le_exp B U b S x rows hM selection hx hqdim
        (fun _ => Subtype.val_injective) hrows hMP j _ _ z⟩)
    hperiod C V hC hV hCexp hVexp P₀ hP₀ hn hdim hbudget hgeometry _ _ _ μ _ _ ν _ _
    p hp hmp R₁ S₀ ρ hS hSP hρ hρP hstride N hsize₁ hrank hR₁ W hW D hD hWD
    base cells ξ hξ hZ₀ M hM hMP selection hx hroot hspatial longReference href test htest Z hZ hZi
  rw [allocatedWholeIdealReference_full_rows B U b hR hσ S x X hM selection hx modulus stride
    longReference hb o bW d N hW mesh base cells test Z p hmp δideal]
  simpa only [allocatedWholeIdealReference, sub_div, f, allocatedPhysicalLongIdeal,
    law, V₀, H, weight, target, point, reconstruct, reference] using hcomparison

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
theorem allocated_product_source_separated_exponential_comparison
    {pAccuracy pSampling w v e E Psp : ℝ} (hpAccuracy : 0 ≤ pAccuracy)
    (hAccuracySampling : pAccuracy ≤ pSampling) (hw : 0 ≤ w) (hv : 0 ≤ v) (he : 0 ≤ e) (hE : 0 ≤ E)
    (hPsp : 0 ≤ Psp) (hdimSp : ((dim + 1 : ℕ) : ℝ) ≤ Psp)
    (hGsp : (Fintype.card G : ℝ) ≤ Psp) (hXsp : (Fintype.card X : ℝ) ≤ Psp)
    (hperiodSp : (modulus : ℝ) ≤ Real.exp (Psp ^ 2))
    (hdimSmall : dim ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pAccuracy)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ pAccuracy) (hn₁ : ∀ j, (n j : ℝ) ≤ pAccuracy)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ pAccuracy)
    (M₀ : ℕ) (hqM : refined ≤ M₀ ^ (m + 1)) (hM₀ : (M₀ : ℝ) ≤ Real.exp pAccuracy)
    (hS₁ : (S.value : ℝ) ≤ Real.exp pSampling)
    (hδ : δ ≤ allocatedSitePrimitiveTolerance m pAccuracy w v (allocatedOriginalCoverAccuracy Psp (E + 1)))
    (hEbudget : allocatedOriginalCoverAccuracy Psp (E + 1) + 4 ≤ pAccuracy)
    (hmaskLog : allocatedSiteKernelMaskLog m Psp ≤ w)
    (hidealLog : allocatedIdealProfileLog m pAccuracy e ≤ v) :
  let shiftSize := allocatedOriginalCoverMesh m Psp pAccuracy w v (E + 1)
  ∀ (sourceMesh : ℝ), 0 < sourceMesh →
  let mesh := min sourceMesh shiftSize
  ∀ {K : ℕ}, 2 ≤ K → AllocatedBooleanRowsSampling.{uX,uJ,uG,uI,uB,uQ} m dim K (rowTypes) (rows) →
    ∀ (δideal : ℝ≥0), 0 < δideal → δideal ≤ 1 → (δideal : ℝ)⁻¹ ≤ Real.exp e →
    (∀ j, (R j)⁻¹ ≤ Real.exp pAccuracy) →
    let _f := allocatedPhysicalLongIdeal B U b hR S rowSets δideal
    ∀ (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Q : Fin m → Type uQ} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d]
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

    (_hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchartinv : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (_hsmall : ∀ j, R j ≤ allocatedProductGridRadius (G := G) B
      (fun k : Fin m => boundedBooleanJetRows (Fin dim) (k.val + 1)) Cinv j)
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
    (_hgeometry : allocatedSeparatedGeometryLog m Psp pAccuracy pSampling w v (E + 1) ≤ P₀)
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hmp : ∀ j e, coefficients (p j) e ∈ U j)
    {R₁ S₀ ρ : ℝ} (_hS : 0 ≤ S₀) (_hSP : S₀ ≤ Real.exp P₀) (hρ : 0 < ρ)
    (_hρP : 1 / ρ ≤ Real.exp P₀)
    (_hstride : ∀ x, (stride x : ℝ) ≤ S₀)
    (N : X → ℕ) (hsize : ∀ x, Real.exp ((P₀ + K) ^ K) ≤ (N x : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) R₁ (U j) (p j))
    (_hR : Real.exp ((P₀ + K) ^ K) ≤ R₁),
    ∀ (W : ℝ) (hW : 0 ≤ W) (D : ℝ), D ≤ Real.exp Psp → W ≤ D * S.value →
    let H := trimmedSpatialRootScale ρ N stride
    let point := physicalCubeRowSample (O := rowTypes) U d (rows) p hmp
    let law := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let target := allocatedProductFullGridResidueProfile B U b hR hσ S refined x hb o bW d witnesses δideal
    let reference := allocatedSupportedWholeReference (dim := dim) B U b S refined
    ∀ (base : X → ℤ)
      (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
      (ξ : ℝ) (hξ : 0 < ξ),
    let V₀ := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W ρ ξ N
    ∀ (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells V₀ z),
    ∀ (M : ℕ) (hM : 0 < M), (M : ℝ) ≤ Real.exp Psp →
    ∀ (selection : Fin dim ↪ G) (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x),
    (allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W) →
    (integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage
        (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)) →
    ∀ (longReference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value)
        (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus stride)) →
      PrincipalAxisTuples (α := Fin dim) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
        (allocatedPrincipalSides B U b S)),
    (∀ u r, principalResidueLabel refined (longReference u r) = r) →
    ∀ (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ), (∀ v, ‖test v‖ ≤ 1) →
    ∀ (Z : ℝ), 0 < Z → Z⁻¹ ≤ 2 →
    let reconstruct := allocatedWholeResidueReconstruction B U b S X modulus stride reference x base
    let weight := allocatedRecenteredResidueWeight (τ := ρ) B U b S X modulus stride reference x hM selection hx
      N hW mesh base cells test
    let hN : ∀ t, 0 < N t := fun t => Nat.cast_pos.mp ((Real.exp_pos _).trans_le (hsize t))
    ‖allocatedOriginalTupleSource B U b hR hσ S x X stride hb o N hN hW hρ hξ
        base cells hmass test Z p hmp -
      allocatedWholeIdealReference (τ := ρ) (ξ := ξ)
        B U b hR hσ S x
        (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) (j.val + 1) → Finset (Fin dim)))
        X hM selection hx modulus stride longReference hb o bW d
        N hW mesh base cells (physicalCubeEuclideanSample U d p hmp) test Z δideal‖ ≤ Real.exp (-(E + 1)) →
    ‖allocatedOriginalTupleSource B U b hR hσ S x X stride hb o N hN hW hρ hξ
        base cells hmass test Z p hmp -
      (law.fiberLaw (principalResidueLabel refined)).complexMean (fun r =>
        ∑ a : cells, (selectedResidueCellWeight stride cells V₀ a : ℂ) *
          ∑ v ∈ spatialWindow H 4, weight r a v * target r (point (reconstruct r a.val v))) / (Z : ℂ)‖ ≤
      Real.exp (-E) := by
  intro shiftSize sourceMesh hsourceMesh mesh K hK hSampling δideal hδideal hδideal1 hδe hRi f
    x hb o Q _ bW d _ _ hσ1 Cinv hCinv hchartinv hsmall hperiod C V hC hV hCexp hVexp P₀ hP₀ hn hdim hbudget hgeometry
    _ _ _ μ _ _ ν _ _ p hp hmp R₁ S₀ ρ hS hSP hρ hρP hstride N hsize hrank hR₁
    W hW D hD hWD H point law target reference base cells ξ hξ V₀ hmass M hM hMP selection hx
    hroot hspatial longReference href test htest Z hZ hZi reconstruct weight hN hsource
  have hshift := (allocatedOriginalCoverMesh_spec m hPsp hpAccuracy hw hv (by linarith : 0 ≤ E + 1)).1
  have hmesh : 0 < mesh := lt_min hsourceMesh hshift
  have hmeshLe : mesh ≤ shiftSize := min_le_right _ _
  have hprevious := allocated_product_ideal_separated_exponential_comparison B U b hR hσ S stride hs modulus δ
    witnesses hWitness hpAccuracy hAccuracySampling hw hv he (by linarith : 0 ≤ E + 1) hPsp hdimSp hGsp hXsp hperiodSp hdimSmall
    hvars hI hn₁ hJ M₀ hqM hM₀ hS₁ hδ hEbudget hmaskLog hidealLog
    mesh hmesh hmeshLe hK hSampling δideal hδideal hδideal1 hδe hRi
  have hcomparison := @hprevious x hb o Q _ bW d _ _ hσ1 Cinv hCinv hchartinv hsmall hperiod C V hC hV hCexp hVexp
    P₀ hP₀ hn hdim hbudget hgeometry _ _ _ μ _ _ ν _ _ p hp hmp R₁ S₀ ρ
    hS hSP hρ hρP hstride N hsize hrank hR₁ W hW D hD hWD
    base cells ξ hξ hmass M hM hMP selection hx hroot hspatial longReference href test htest Z hZ hZi
  have hsum : Real.exp (-(E + 1)) + Real.exp (-(E + 1)) ≤ Real.exp (-E) := by
    calc
      _ = 2 * Real.exp (-(E + 1)) := by ring
      _ ≤ Real.exp 1 * Real.exp (-(E + 1)) := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  exact ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hsource hcomparison)).trans hsum

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)]
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
theorem allocated_product_primitive_coarse_comparison
    {pAccuracy pSampling w v e E Psp : ℝ} (hpAccuracy : 0 ≤ pAccuracy)
    (hAccuracySampling : pAccuracy ≤ pSampling) (hw : 0 ≤ w) (hv : 0 ≤ v) (he : 0 ≤ e) (hE : 0 ≤ E)
    (hPsp : 0 ≤ Psp) (hdimSp : ((dim + 1 : ℕ) : ℝ) ≤ Psp)
    (hGsp : (Fintype.card G : ℝ) ≤ Psp) (hXsp : (Fintype.card X : ℝ) ≤ Psp)
    (hperiodSp : (modulus : ℝ) ≤ Real.exp (Psp ^ 2))
    (hdimSmall : dim ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pAccuracy)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ pAccuracy) (hn₁ : ∀ j, (n j : ℝ) ≤ pAccuracy)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ pAccuracy)
    (M₀ : ℕ) (hqM : refined ≤ M₀ ^ (m + 1)) (hM₀ : (M₀ : ℝ) ≤ Real.exp pAccuracy)
    (hS₁ : (S.value : ℝ) ≤ Real.exp pSampling)
    (hδ : δ ≤ allocatedSitePrimitiveTolerance m pAccuracy w v (allocatedOriginalCoverAccuracy Psp (E + 1)))
    (hEbudget : allocatedOriginalCoverAccuracy Psp (E + 1) + 4 ≤ pAccuracy)
    (hmaskLog : allocatedSiteKernelMaskLog m Psp ≤ w)
    (hidealLog : allocatedIdealProfileLog m pAccuracy e ≤ v) :
  ∀ {K : ℕ}, 2 ≤ K → AllocatedBooleanRowsSampling.{uX,uJ,uG,uI,uB,uQ} m dim K (rowTypes) (rows) → ∀
    (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Q : Fin m → Type uQ} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d]
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

    (δideal : ℝ≥0) (_hδideal : 0 < δideal) (_hδideal1 : δideal ≤ 1)
    (_hδe : (δideal : ℝ)⁻¹ ≤ Real.exp e) (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp pAccuracy)
    (_hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchartinv : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (_hsmall : ∀ j, R j ≤ allocatedProductGridRadius (G := G) B
      (fun k : Fin m => boundedBooleanJetRows (Fin dim) (k.val + 1)) Cinv j)
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
    (_hgeometry : allocatedSeparatedGeometryLog m Psp pAccuracy pSampling w v (E + 1) ≤ P₀)
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
    ∀ (W : ℝ) (hW : 0 ≤ W) (D : ℝ), D ≤ Real.exp Psp → W ≤ D * S.value →
    let H := trimmedSpatialRootScale ρ N stride
    let point := physicalCubeRowSample (O := rowTypes) U d (rows) p hmp
    let law := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let target := allocatedProductFullGridResidueProfile B U b hR hσ S refined x hb o bW d witnesses δideal
    let reference := allocatedSupportedWholeReference (dim := dim) B U b S refined
    ∀ (base : X → ℤ)
      (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
      (ξ : ℝ), 0 < ξ →
    let V₀ := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W ρ ξ N
    (0 < ∑' z, selectedResidueSmoothWeight stride cells V₀ z) →
    ∀ (M : ℕ) (hM : 0 < M), (M : ℝ) ≤ Real.exp Psp →
    ∀ (selection : Fin dim ↪ G)
      (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x),
    (allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W) →
    (integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage
        (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)) →
    ∀ (Z : ℝ), 0 < Z → Z⁻¹ ≤ 2 →
    let reconstruct := allocatedWholeResidueReconstruction B U b S X modulus stride reference x base
    let coarse := allocatedProductCoarseMesh m X selection M modulus Psp pAccuracy w v (E + 1)
    0 < coarse ∧ coarse ≤ 1 / 4 ∧
      ∀ (fine : ℝ), 0 < fine → fine ≤ coarse →
      ∀ (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ), (∀ v, ‖test v‖ ≤ 1) →
      let weight := fun mesh => allocatedRecenteredResidueWeight (τ := ρ)
        B U b S X modulus stride reference x hM selection hx N hW mesh base cells test
      let value := fun mesh =>
        (law.fiberLaw (principalResidueLabel refined)).complexMean (fun r =>
          ∑ a : cells, (selectedResidueCellWeight stride cells V₀ a : ℂ) *
            ∑ v ∈ spatialWindow H 4, weight mesh r a v * target r (point (reconstruct r a.val v))) / (Z : ℂ)
      ‖value fine - value coarse‖ ≤ Real.exp (-E) := by
  intro K hK hSampling x hb o Q _ bW d _ _ δideal hδideal hδideal1 hδe hRi
    hσ1 Cinv hCinv hchartinv hsmall hperiod C V hC hV hCexp hVexp
    P₀ hP₀ hn hdim hbudget hgeometry _ _ _ μ _ _ ν _ _ p hp hmp R₁ S₀ ρ
    hS hSP hρ hρP hstride N hsize₁ hrank hR₁ W hW D hD hWD H point law target reference
    base cells ξ hξ V₀ hZ₀ M hM hMP selection hx hroot hspatial Z hZ hZi reconstruct coarse
  have hE1 : 0 ≤ E + 1 := by linarith only [hE]
  have hcover := allocatedOriginalCoverMesh_spec m hPsp hpAccuracy hw hv hE1
  have hN (t : X) : 0 < N t := Nat.cast_pos.mp ((Real.exp_pos _).trans_le (hsize₁ t))
  have hH (t : X) : 0 < H t :=
    (trimmedSpatial_scales_pos hW hρ N stride t (hN t) (hs t)).1
  have hgeom := allocatedOriginalCover_separated_geometry m (Fintype.card (LayerSamplerVariables G I n B))
    N stride hPsp hpAccuracy hAccuracySampling hw hv hE1 hgeometry hK hvars (Nat.cast_nonneg S.value) hS₁
    hρ hρP hs (fun t => (hstride t).trans hSP) hsize₁
  have hentry : allocatedPhysicalEntryBudget B U b S (fun _ => 0) =
      1 + ((Fintype.card (LayerSamplerVariables G I n B) : ℝ) + 1) * S.value := by
    simp only [allocatedPhysicalEntryBudget, allocatedPhysicalRootBudget, Int.cast_zero,
      abs_zero, Finset.sum_const_zero, zero_add]
    ring
  have hshift (t : X) : Fintype.card (Option (LayerSamplerVariables G I n B)) *
      (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0)) ≤
        allocatedOriginalCoverMesh m Psp pAccuracy w v (E + 1) * H t := by
    simpa only [hentry, Fintype.card_option, Nat.cast_add, Nat.cast_one] using (hgeom t).1
  have hscale (t : X) : 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H t := (hgeom t).2
  have hmesh1 : allocatedOriginalCoverMesh m Psp pAccuracy w v (E + 1) ≤ 1 := by
    linarith [hcover.2.1]
  have hrows (t : X) : Fintype.card (Option (LayerSamplerVariables G I n B)) *
      allocatedPhysicalEntryBudget B U b S (fun _ => 0) ≤ H t := by
    have hsmall := mul_le_mul_of_nonneg_right hmesh1 (hH t).le
    nlinarith [hshift t, hH t]
  let CM : ℝ≥0 := ⟨Real.exp (allocatedSiteKernelMaskLog m Psp), (Real.exp_pos _).le⟩
  let Cf : ℝ≥0 := ⟨Real.exp (allocatedIdealProfileLog m pAccuracy e), (Real.exp_pos _).le⟩
  have hCM : 1 ≤ (CM : ℝ) := Real.one_le_exp_iff.mpr (allocatedSiteKernelMaskLog_nonneg m hPsp)
  have hfb := allocatedPhysicalLongIdeal_primitive_bound B U b hR S rowSets hpAccuracy he
    (by simpa only [Fintype.card_fin] using hdimSmall) hvars hI hn₁ hRi δideal hδideal hδe
  have hrowdegree (j : Fin m) (r : rowSets j) : r.val.card ≤ j.val + 1 :=
    (mem_boundedBooleanJetRows (j.val + 1) r.val).mp r.property
  have hqdim : Fintype.card (Fin dim) ≤ m + 1 := by simpa only [Fintype.card_fin] using hdimSmall
  have hEcover : 0 ≤ allocatedOriginalCoverAccuracy Psp (E + 1) := by
    have hlog := coefficientErrorSpatialLog_nonneg hPsp
    unfold allocatedOriginalCoverAccuracy
    positivity
  have hprevious := allocated_product_early_coarse_comparison B U b hR hσ S stride hs modulus δ
    witnesses hWitness hpAccuracy hAccuracySampling hw hv hEcover hdimSmall
    hvars hI hn₁ hJ M₀ hqM hM₀ hS₁ hδ hEbudget (K := K) hSampling
  have hbound := @hprevious x hb o Q _ bW d _ _ δideal hδideal hδideal1 hσ1 Cinv hCinv hchartinv hsmall
    CM Cf hCM hfb (Real.exp_le_exp.mpr hmaskLog) (Real.exp_le_exp.mpr hidealLog)
    (fun y j z => ⟨(allocatedIntegerKernelMask_bound B U b S x rows hM selection hx hqdim
      (fun _ => Subtype.val_injective) hrowdegree j _ _ z).1,
      allocatedIntegerKernelMask_le_exp B U b S x rows hM selection hx hqdim
        (fun _ => Subtype.val_injective) hrowdegree hMP j _ _ z⟩)
    hperiod C V hC hV hCexp hVexp P₀ hP₀ hn hdim hbudget _ _ _ μ _ _ ν _ _
    p hp hmp R₁ S₀ ρ hS hSP hρ hρP hstride N hsize₁ hrank hR₁ W hW
    base cells ξ hξ hZ₀ hrows hscale M hM selection hx hroot hspatial
    Psp D (E + 1) hPsp hdimSp hXsp hD hWD Z hZ hZi
  refine ⟨hbound.1, hbound.2.1, ?_⟩
  intro fine hfine hle test htest weight value
  have hcomparison := hbound.2.2 fine hfine hle test htest
  have hnum := allocatedProductCoarse_error_bound (X := X) (E := E) dim selection
    hPsp hM hMP hperiodSp hdimSp hGsp hXsp (by exact_mod_cast S.positive) hW hD hWD hZ hZi
  exact hcomparison.trans hnum

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

def AllocatedProductSeparatedContract
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (pAccuracy pSampling w v e E Psp : ℝ) : Prop :=
  let shiftSize := allocatedOriginalCoverMesh m Psp pAccuracy w v (E + 1)
  ∀ (sourceMesh : ℝ), 0 < sourceMesh →
  let mesh := min sourceMesh shiftSize
  ∀ {K : ℕ}, 2 ≤ K → AllocatedBooleanRowsSampling.{uX,uJ,uG,uI,uB,uQ} m dim K (rowTypes) (rows) →
    ∀ (δideal : ℝ≥0), 0 < δideal → δideal ≤ 1 → (δideal : ℝ)⁻¹ ≤ Real.exp e →
    (∀ j, (R j)⁻¹ ≤ Real.exp pAccuracy) →
    let _f := allocatedPhysicalLongIdeal B U b hR S rowSets δideal
    ∀ (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    {Q : Fin m → Type uQ} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d]
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

    (_hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchartinv : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (_hproductSmall : ∀ j, R j ≤ allocatedProductGridRadius (G := G) B
      (fun k : Fin m => boundedBooleanJetRows (Fin dim) (k.val + 1)) Cinv j)
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
    (_hgeometry : allocatedSeparatedGeometryLog m Psp pAccuracy pSampling w v (E + 1) ≤ P₀)
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hmp : ∀ j e, coefficients (p j) e ∈ U j)
    {R₁ S₀ ρ : ℝ} (_hS : 0 ≤ S₀) (_hSP : S₀ ≤ Real.exp P₀) (hρ : 0 < ρ)
    (_hρP : 1 / ρ ≤ Real.exp P₀)
    (_hstride : ∀ x, (stride x : ℝ) ≤ S₀)
    (N : X → ℕ) (hsize : ∀ x, Real.exp ((P₀ + K) ^ K) ≤ (N x : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) R₁ (U j) (p j))
    (_hR : Real.exp ((P₀ + K) ^ K) ≤ R₁),
    ∀ (W : ℝ) (hW : 0 ≤ W) (D : ℝ), D ≤ Real.exp Psp → W ≤ D * S.value →
    let H := trimmedSpatialRootScale ρ N stride
    let point := physicalCubeRowSample (O := rowTypes) U d (rows) p hmp
    let law := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let target := allocatedProductFullGridResidueProfile B U b hR hσ S refined x hb o bW d witnesses δideal
    let reference := allocatedSupportedWholeReference (dim := dim) B U b S refined
    ∀ (base : X → ℤ)
      (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
      (ξ : ℝ) (hξ : 0 < ξ),
    let V₀ := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W ρ ξ N
    ∀ (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells V₀ z),
    ∀ (M : ℕ) (hM : 0 < M), (M : ℝ) ≤ Real.exp Psp →
    ∀ (selection : Fin dim ↪ G) (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x),
    (allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W) →
    (integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage
        (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)) →
    ∀ (longReference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value)
        (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus stride)) →
      PrincipalAxisTuples (α := Fin dim) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
        (allocatedPrincipalSides B U b S)),
    (∀ u r, principalResidueLabel refined (longReference u r) = r) →
    ∀ (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ), (∀ v, ‖test v‖ ≤ 1) →
    ∀ (Z : ℝ), 0 < Z → Z⁻¹ ≤ 2 →
    let reconstruct := allocatedWholeResidueReconstruction B U b S X modulus stride reference x base
    let weight := allocatedRecenteredResidueWeight (τ := ρ) B U b S X modulus stride reference x hM selection hx
      N hW mesh base cells test
    let hN : ∀ t, 0 < N t := fun t => Nat.cast_pos.mp ((Real.exp_pos _).trans_le (hsize t))
    ‖allocatedOriginalTupleSource B U b hR hσ S x X stride hb o N hN hW hρ hξ
        base cells hmass test Z p hmp -
      allocatedWholeIdealReference (τ := ρ) (ξ := ξ)
        B U b hR hσ S x
        (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) (j.val + 1) → Finset (Fin dim)))
        X hM selection hx modulus stride longReference hb o bW d
        N hW mesh base cells (physicalCubeEuclideanSample U d p hmp) test Z δideal‖ ≤ Real.exp (-(E + 1)) →
    ‖allocatedOriginalTupleSource B U b hR hσ S x X stride hb o N hN hW hρ hξ
        base cells hmass test Z p hmp -
      (law.fiberLaw (principalResidueLabel refined)).complexMean (fun r =>
        ∑ a : cells, (selectedResidueCellWeight stride cells V₀ a : ℂ) *
          ∑ v ∈ spatialWindow H 4, weight r a v * target r (point (reconstruct r a.val v))) / (Z : ℂ)‖ ≤
      Real.exp (-E)

include hWitness hs in
theorem allocatedProductSeparatedContract_of_sampling
    {pAccuracy pSampling w v e E Psp : ℝ} (hpAccuracy : 0 ≤ pAccuracy)
    (hAccuracySampling : pAccuracy ≤ pSampling) (hw : 0 ≤ w) (hv : 0 ≤ v) (he : 0 ≤ e) (hE : 0 ≤ E)
    (hPsp : 0 ≤ Psp) (hdimSp : ((dim + 1 : ℕ) : ℝ) ≤ Psp)
    (hGsp : (Fintype.card G : ℝ) ≤ Psp) (hXsp : (Fintype.card X : ℝ) ≤ Psp)
    (hperiodSp : (modulus : ℝ) ≤ Real.exp (Psp ^ 2))
    (hdimSmall : dim ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pAccuracy)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ pAccuracy) (hn₁ : ∀ j, (n j : ℝ) ≤ pAccuracy)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ pAccuracy)
    (M₀ : ℕ) (hqM : refined ≤ M₀ ^ (m + 1)) (hM₀ : (M₀ : ℝ) ≤ Real.exp pAccuracy)
    (hS₁ : (S.value : ℝ) ≤ Real.exp pSampling)
    (hδ : δ ≤ allocatedSitePrimitiveTolerance m pAccuracy w v (allocatedOriginalCoverAccuracy Psp (E + 1)))
    (hEbudget : allocatedOriginalCoverAccuracy Psp (E + 1) + 4 ≤ pAccuracy)
    (hmaskLog : allocatedSiteKernelMaskLog m Psp ≤ w)
    (hidealLog : allocatedIdealProfileLog m pAccuracy e ≤ v)
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))) :
    AllocatedProductSeparatedContract.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ S stride modulus witnesses o pAccuracy pSampling w v e E Psp := by
  have hprevious := allocated_product_source_separated_exponential_comparison B U b hR hσ S stride hs modulus δ
    witnesses hWitness hpAccuracy hAccuracySampling hw hv he hE hPsp hdimSp hGsp hXsp hperiodSp hdimSmall
    hvars hI hn₁ hJ M₀ hqM hM₀ hS₁ hδ hEbudget hmaskLog hidealLog
  unfold AllocatedProductSeparatedContract
  intro shiftSize sourceMesh hsourceMesh mesh K hK hSampling δideal hδideal hδideal1 hδe hRi f x hb Q instQ
  exact @hprevious sourceMesh hsourceMesh K hK (@hSampling) δideal hδideal hδideal1 hδe hRi x hb o Q instQ

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq

variable {m dim : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) (Fin.val j + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : jets j → Finset (Fin dim)))
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "fullRows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

def AllocatedProductSeparatedRawData (Psp E e pNum Pbase Qraw pAccuracy pSampling : ℝ) (hP : 0 ≤ Psp)
    (δ : ℝ≥0) (A Kraw Ksite : ℕ)
    (witnesses : (q : AllocatedRefinedPeriodIndex m Psp) →
      (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
      AllocatedFullGridResidueWitness (dim := dim) B U b S (q.val : ℕ) r.val) : Prop :=
  let w := allocatedSiteKernelMaskLog m Psp
  let v := allocatedIdealProfileLog m pAccuracy e
  let Pfinal := sourceCoverParameter dim Kraw Psp pNum Qraw
    (allocatedSiteErrorFourierOutput m pSampling w v)
    (allocatedSeparatedGeometryLog m Psp pAccuracy pSampling w v (E + 1))
  ∀ (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    {Mk : ℕ} (hMk : 0 < Mk) (selection : Fin dim ↪ G)
    (hx : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
    (_hqDim : dim ≤ m + 1) (hMkPsp : (Mk : ℝ) ≤ Real.exp Psp),
  ∃ (d : ℕ) (hd : 0 < d),
    let : NeZero d := ⟨hd.ne'⟩
    (d : ℝ) ≤ Real.exp ((Pbase + A) ^ A) ∧
  ∀ (modulus : ℕ) (hmodulus : 0 < modulus),
    let : NeZero modulus := ⟨hmodulus.ne'⟩
    ∀ (hmodulusSize : modulus ≤ Mk ^ (m + 1))
      (_hspatialPeriod : ∀ root : G → ℤ, integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
        pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
          (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection))
      (_hcoefficientPeriod : ∀ j, integerScalarLattice (jets j) (modulus : ℤ) ≤
        (scalarKernelIntegerJet x (j.val + 1) (jetRows j)).mulVecLin.range),
    ∃ (s : ∀ j, jets j ↪ BoundedIntegerExponent G (j.val + 1))
      (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (jetRows j)).submatrix id (s j)).det ≠ 0),
    (∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val + 1) (jetRows j) (s j) (hA j) (1 / (Mk : ℝ))) ∧
    ∀ (_block : ∀ a : {a // ¬allocatedGridAxis (I := I) U b S.value a}, jets a.val.1 ↪ B a.val)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (SiteTorus (Finset (Fin dim)) U)] [BorelSpace (SiteTorus (Finset (Fin dim)) U)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Kcov : Fin m → Type uQ} [∀ j, Fintype (Kcov j)]
    (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hCp : ∀ j, (C j : ℝ) ≤ Real.exp pNum) (_hVp : ∀ j, (V j : ℝ) ≤ Real.exp pNum)
    (_hCpAccuracy : ∀ j, (C j : ℝ) ≤ Real.exp pAccuracy)
    (_hVpAccuracy : ∀ j, (V j : ℝ) ≤ Real.exp pAccuracy)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B (Fin dim) Cinv 1 j)
    (_hσ1 : ∀ j, σ j ≤ 1)
    (_hproductSmall : ∀ j, R j ≤ allocatedProductGridRadius (G := G) B rowSets Cinv j)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μsmall : Measure (CoefficientTorus (K := Fin dim) U)) [μsmall.IsAddLeftInvariant] [IsProbabilityMeasure μsmall]
    {X : Type uX} [Fintype X] [DecidableEq X]
    (hXPsp : (Fintype.card X : ℝ) ≤ Psp)
    (q : X → ℕ) (hq : ∀ t, 0 < q t) (hqPsp : ∀ t, (q t : ℝ) ≤ Real.exp Psp),
    let refined := residueRefinedPeriod modulus q
    let index := allocatedRefinedPeriodIndex m hP hMkPsp hmodulusSize hXPsp hmodulus q hq hqPsp
    ∃ hRefined : 0 < refined,
    let : NeZero refined := ⟨hRefined.ne'⟩
    (∀ t, q t * modulus ∣ refined) ∧
    (refined : ℝ) ≤ Real.exp ((m + 1 : ℕ) * Psp + Fintype.card X * Psp) ∧
    ∃ hsize : ∀ a, (Fintype.card (Fin dim) + 1) * refined ≤
      principalAxisLength (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
        (allocatedPrincipalSides B U b S) a,
    ∃ (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      PrincipalAxisTuples (α := Fin dim) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
    (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      ∀ j, Matrix (jets j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus)),
    (∀ u r, principalResidueLabel refined (reference u r) = r) ∧
    (∀ u r v, (allocatedLongResidueWeights B U b S refined hRefined r hsize).weight v ≠ 0 →
      ∀ j, integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u jetRows j v) modulus = residue u r j) ∧
    let W := allocatedPhysicalRootBudget B U b S (fun _ => 0)
    let hW := allocatedPhysicalRootBudget_nonneg B U b S (fun _ => 0)
    let indices := PrincipalTupleIndex B (layerSamplerDegree I n)
    let ξ := normalizedTupleNarrowWidth X indices selection Mk Psp ((E + 1) + 2)
    let hξ := normalizedTupleNarrowWidth_pos X indices selection Mk Psp ((E + 1) + 2)
    let sourceMesh := normalizedTupleRadius X selection Mk Psp ((E + 1) + 2) W / 4
    let mesh := min sourceMesh (allocatedOriginalCoverMesh m Psp pAccuracy w v (E + 1))
    ∀ {τ : ℝ} (hτ : 0 < τ) (_hτP : 1 / τ ≤ Real.exp pNum)
    (N : X → ℕ) (hN : ∀ t, 0 < N t)
    (_hsize : ∀ t, Real.exp ((Pfinal + Ksite) ^ Ksite) ≤ (N t : ℝ))
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
    {rank : ℝ}
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) rank (U j) (poly j))
    (_hRank : Real.exp ((Pfinal + Ksite) ^ Ksite) ≤ rank)
    (base : X → ℤ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
    (_hcells : cells.Nonempty)
    (test : Finset (Fin dim) → (X → ℝ) → ℂ) (_htest : ∀ site v, ‖test site v‖ ≤ 1)
    (Z : ℝ) (_hZ : 1 / 2 ≤ Z),
    let V₀ := narrowTrimmedSpatialWidths (G := G) (J := indices) W τ ξ N
    let H := trimmedSpatialRootScale τ N q
    let point := physicalCubeRowSample U d fullRows poly hmem
    let law := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let target := allocatedProductFullGridResidueProfile B U b hR hσ S refined x hb o bW d
      (witnesses index) δ
    let wholeReference := allocatedSupportedWholeReference (dim := dim) B U b S refined
    let reconstruct := allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base
    let weight := allocatedRecenteredResidueWeight (τ := τ) B U b S X modulus q wholeReference x hMk selection hx
      N hW mesh base cells (physicalCubeSiteTest test)
    ∃ hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells V₀ z,
    ‖allocatedOriginalTupleSource B U b hR hσ S x X q hb o N hN hW hτ hξ base cells hmass
        (physicalCubeSiteTest test) Z poly hmem -
      (law.fiberLaw (principalResidueLabel refined)).complexMean (fun r =>
        ∑ a : cells, (selectedResidueCellWeight q cells V₀ a : ℂ) *
          ∑ z ∈ spatialWindow H 4, weight r a z * target r (point (reconstruct r a.val z))) / (Z : ℂ)‖ ≤
      Real.exp (-E)

end Erdos3.VectorPolynomial

end

end OAI
