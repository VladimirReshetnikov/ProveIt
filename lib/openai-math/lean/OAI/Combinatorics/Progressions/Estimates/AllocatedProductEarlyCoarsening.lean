import OAI.Combinatorics.Progressions.Estimates.AllocatedProductSourceCover

namespace OAI

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
theorem allocated_product_coarse_comparison
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
      (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x),
    (allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W) →
    (integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage
        (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)) →
    ∀ (Qratio : ℝ≥0), 1 ≤ Qratio → (1 + W) / (S.value : ℝ) ≤ Qratio →
    ∀ (Z Vmass ε : ℝ), 0 < Z → 0 < ε →
    let profile := fun y z => (allocatedWholeMaskedCoveredProfile (O := rowTypes)
      B U b hR hσ S x (rows) hb o bW d y modulus (allocatedPhysicalLongIdeal B U b hR S rowSets δideal) z : ℂ)
    let reconstruct := allocatedWholeResidueReconstruction B U b S X modulus stride reference x base
    let cap := ((modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
      anisotropicSpatialDensityCap selection (1 / (M : ℝ))) ^ Fintype.card X
    let factor := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + W) / (S.value : ℝ)) ^ dim) ^ Fintype.card X
    law.mean (allocatedRecenteredProfileMass (W := W) (τ := ρ) (ξ := ξ)
      B U b S X modulus stride reference x N base cells point profile) / Z ≤ Vmass →
    let coarse := allocatedRecenteredCoarseMesh (M := M) X modulus selection Qratio Vmass ε
    0 < coarse ∧ coarse ≤ 1 / 4 ∧
      ∀ (fine : ℝ), 0 < fine → fine ≤ coarse →
      ∀ (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ), (∀ v, ‖test v‖ ≤ 1) →
      let weight := fun mesh => allocatedRecenteredResidueWeight (τ := ρ)
        B U b S X modulus stride reference x hM selection hx N hW mesh base cells test
      let value := fun mesh =>
        (law.fiberLaw (principalResidueLabel refined)).complexMean (fun r =>
          ∑ a : cells, (selectedResidueCellWeight stride cells V₀ a : ℂ) *
            ∑ v ∈ spatialWindow H 4, weight mesh r a v * target r (point (reconstruct r a.val v))) / (Z : ℂ)
      ‖value fine - value coarse‖ ≤ 2 * ((cap * factor * Real.exp (-E)) / Z) + ε := by
  intro K hSampling x hb o Q _ bW d _ _ δideal hδideal hδideal1 hσ1 Cinv hCinv hchartinv hsmall
    CM Cf hCM hfb hCMexp hCfexp hmask hperiod C V hC hV
    hCexp hVexp P₀ hP₀ hn hdim hbudget _ _ _ μ _ _ ν _ _ p hp hmp R₁ S₀ ρ
    hS hSP hρ hρP hstride N hsize₁ hrank hR₁ W hW H point law target reference
    base cells ξ hξ V₀ hZ₀ hrows hscale M hM selection hx hrootBudget hspatial
    Qratio hQratio hratio Z Vmass ε hZ hε profile reconstruct cap factor hMass coarse
  have hN (t : X) : 0 < N t := by
    exact Nat.cast_pos.mp ((Real.exp_pos _).trans_le (hsize₁ t))
  obtain ⟨y, _hy⟩ := law.exists_weight_pos
  have hroot (g : G) : |((x g none : ℤ) : ℝ)| ≤ 1 + W := by
    have h := (allocatedPhysicalCube_root_budget B U b S (fun _ => 0) x y (.inl g)).trans hrootBudget
    have h' : |((x g none : ℤ) : ℝ)| ≤ W := by
      simpa only [allocatedPhysicalCubeRoot, Sum.elim_inl, zero_add] using h
    linarith only [h']
  have hstage := allocatedRecenteredReference_coarse_comparison (O := rowTypes) (ξ := ξ) (τ := ρ)
    B U b S X modulus stride reference x hM selection hx N hW base cells point
  have hstage2 := hstage hs hN hρ profile Qratio hQratio hratio hroot hspatial Z Vmass ε hZ hε
  dsimp only [law] at hMass
  have hcoarse := hstage2 hMass
  refine ⟨hcoarse.1, hcoarse.2.1, ?_⟩
  intro fine hfine hle test htest weight value
  let source := fun mesh => law.complexMean (allocatedRecenteredProfileTerm (τ := ρ) (ξ := ξ)
    B U b S X modulus stride reference x hM selection hx N hW mesh base cells point test profile) / (Z : ℂ)
  have hprevious := allocated_product_recentered_separated_comparison
    B U b hR hσ S stride hs modulus δ witnesses hWitness
    hpAccuracy hAccuracySampling hw hv hE hdimSmall hvars hI hn₁ hJ M₀ hqM hM₀ hS₁ hδ hEbudget (K := K) hSampling
  have hcompare (mesh : ℝ) (hmesh : 0 < mesh) :
      ‖source mesh - value mesh‖ ≤ (cap * factor * Real.exp (-E)) / Z := by
    have hbound := @hprevious x hb o Q _ bW d _ _ δideal hδideal hδideal1 hσ1 Cinv hCinv hchartinv hsmall
      CM Cf hCM hfb hCMexp hCfexp hmask hperiod C V hC hV hCexp hVexp
      P₀ hP₀ hn hdim hbudget _ _ _ μ _ _ ν _ _ p hp hmp R₁ S₀ ρ
      hS hSP hρ hρP hstride N hsize₁ hrank hR₁ W hW
      base cells ξ hξ hZ₀ hrows hscale M hM selection hx mesh hmesh hrootBudget hspatial test htest Z hZ
    dsimp only at hbound
    change ‖(law.complexMean (allocatedRecenteredProfileTerm (τ := ρ) (ξ := ξ)
      B U b S X modulus stride reference x hM selection hx N hW mesh base cells point test profile) -
      (law.fiberLaw (principalResidueLabel refined)).complexMean (fun r =>
        ∑ a : cells, (selectedResidueCellWeight stride cells V₀ a : ℂ) *
          ∑ v ∈ spatialWindow H 4, weight mesh r a v * target r (point (reconstruct r a.val v)))) / (Z : ℂ)‖ ≤
      (cap * factor * Real.exp (-E)) / Z at hbound
    simpa only [source, value, sub_div] using hbound
  have hmid : ‖source fine - source coarse‖ ≤ ε := by
    dsimp only [source, law, coarse]
    exact hcoarse.2.2 fine hfine hle test htest
  have hleft : ‖value fine - source fine‖ ≤ (cap * factor * Real.exp (-E)) / Z := by
    rw [norm_sub_rev]
    exact hcompare fine hfine
  calc
    ‖value fine - value coarse‖ ≤ ‖value fine - source fine‖ + ‖source fine - value coarse‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (cap * factor * Real.exp (-E)) / Z +
        (‖source fine - source coarse‖ + ‖source coarse - value coarse‖) :=
      add_le_add hleft (norm_sub_le_norm_sub_add_norm_sub _ _ _)
    _ ≤ (cap * factor * Real.exp (-E)) / Z +
        (ε + (cap * factor * Real.exp (-E)) / Z) :=
      add_le_add le_rfl (add_le_add hmid (hcompare coarse hcoarse.1))
    _ = 2 * ((cap * factor * Real.exp (-E)) / Z) + ε := by ring

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
theorem allocated_product_early_coarse_comparison
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
      (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x),
    (allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W) →
    (integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage
        (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)) →
    ∀ {P D Ecoarse : ℝ}, 0 ≤ P → ((dim + 1 : ℕ) : ℝ) ≤ P →
    (Fintype.card X : ℝ) ≤ P → D ≤ Real.exp P → W ≤ D * S.value →
    ∀ (Z : ℝ), 0 < Z → Z⁻¹ ≤ 2 →
    let reconstruct := allocatedWholeResidueReconstruction B U b S X modulus stride reference x base
    let cap := ((modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
      anisotropicSpatialDensityCap selection (1 / (M : ℝ))) ^ Fintype.card X
    let factor := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + W) / (S.value : ℝ)) ^ dim) ^ Fintype.card X
    let coarse := allocatedProductCoarseMesh m X selection M modulus P pAccuracy w v Ecoarse
    0 < coarse ∧ coarse ≤ 1 / 4 ∧
      ∀ (fine : ℝ), 0 < fine → fine ≤ coarse →
      ∀ (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ), (∀ v, ‖test v‖ ≤ 1) →
      let weight := fun mesh => allocatedRecenteredResidueWeight (τ := ρ)
        B U b S X modulus stride reference x hM selection hx N hW mesh base cells test
      let value := fun mesh =>
        (law.fiberLaw (principalResidueLabel refined)).complexMean (fun r =>
          ∑ a : cells, (selectedResidueCellWeight stride cells V₀ a : ℂ) *
            ∑ v ∈ spatialWindow H 4, weight mesh r a v * target r (point (reconstruct r a.val v))) / (Z : ℂ)
      ‖value fine - value coarse‖ ≤ 2 * ((cap * factor * Real.exp (-E)) / Z) + Real.exp (-Ecoarse) := by
  intro K hSampling x hb o Q _ bW d _ _ δideal hδideal hδideal1 hσ1 Cinv hCinv hchartinv hsmall
    CM Cf hCM hfb hCMexp hCfexp hmask hperiod C V hC hV
    hCexp hVexp P₀ hP₀ hn hdim hbudget _ _ _ μ _ _ ν _ _ p hp hmp R₁ S₀ ρ
    hS hSP hρ hρP hstride N hsize₁ hrank hR₁ W hW H point law target reference
    base cells ξ hξ V₀ hZ₀ hrows hscale M hM selection hx hrootBudget hspatial
    P D Ecoarse hP hdimP hXP hD hWD Z hZ hZi reconstruct cap factor coarse
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
  have hSpos : (0 : ℝ) < S.value := Nat.cast_pos.mpr S.positive
  have hSone : (1 : ℝ) ≤ S.value := by exact_mod_cast S.positive
  have hMass := allocatedOriginalProfile_normalized_mass_bound m dim X hP hdimP hXP
    hSone hW hD hWD hZ hZi hmass
  have hratio : (1 + W) / (S.value : ℝ) ≤ allocatedPrimitiveRootRatio (Real.exp P) := by
    rw [(allocatedPrimitiveRootRatio_bounds (Real.exp_pos P).le).1]
    apply (div_le_iff₀ hSpos).mpr
    have hWExp := hWD.trans (mul_le_mul_of_nonneg_right hD hSpos.le)
    nlinarith only [hWExp, hSone]
  have hprevious := allocated_product_coarse_comparison
    B U b hR hσ S stride hs modulus δ witnesses hWitness
    hpAccuracy hAccuracySampling hw hv hE hdimSmall hvars hI hn₁ hJ M₀ hqM hM₀ hS₁ hδ hEbudget (K := K) hSampling
  have hbound := @hprevious x hb o Q _ bW d _ _ δideal hδideal hδideal1 hσ1 Cinv hCinv hchartinv hsmall
    CM Cf hCM hfb hCMexp hCfexp hmask hperiod C V hC hV hCexp hVexp
    P₀ hP₀ hn hdim hbudget _ _ _ μ _ _ ν _ _ p hp hmp R₁ S₀ ρ
    hS hSP hρ hρP hstride N hsize₁ hrank hR₁ W hW
    base cells ξ hξ hZ₀ hrows hscale M hM selection hx hrootBudget hspatial
    (allocatedPrimitiveRootRatio (Real.exp P)) (allocatedPrimitiveRootRatio_bounds (Real.exp_pos P).le).2.1
    hratio Z (Real.exp (allocatedOriginalMassLog m P pAccuracy w v + 1)) (Real.exp (-Ecoarse))
    hZ (Real.exp_pos _) hMass
  simpa only [coarse, allocatedProductCoarseMesh, target, reconstruct, reference, cap, factor,
    law, V₀, H, point] using hbound

end Erdos3.VectorPolynomial

end

end OAI
