import OAI.Combinatorics.Progressions.Estimates.AllocatedCommonCover
import OAI.Combinatorics.Progressions.Lattices.AllocatedNormalizedProductResidueCover

namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def allocatedFullGridPrimitiveResourceLog {A : Type*} [Semiring A]
    (m : ℕ) (p w v E : A) : A :=
  let D := allocatedComparisonDimension m p
  allocatedMixedJointSiteLog m D p ((m + 1 : ℕ) * p)
    (E + allocatedSiteSpatialMassLog D w v + 3 + allocatedFullGridWindowLog D)

theorem allocatedFullGridPrimitiveResourceLog_nonneg (m : ℕ) {p w v E : ℝ}
    (hp : 0 ≤ p) (hw : 0 ≤ w) (hv : 0 ≤ v) (hE : 0 ≤ E) :
    0 ≤ allocatedFullGridPrimitiveResourceLog m p w v E := by
  have hD := (allocatedComparisonDimension_bounds m hp).1
  have hmass := allocatedSiteSpatialMassLog_nonneg hD hw hv
  have hwindow := allocatedFullGridWindowLog_nonneg hD
  exact (allocatedMixedJointLogs_nonneg m hD hp (by positivity)
    (by positivity : 0 ≤ E + allocatedSiteSpatialMassLog (allocatedComparisonDimension m p) w v + 3 +
      allocatedFullGridWindowLog (allocatedComparisonDimension m p))).2

theorem exists_allocatedFullGridPrimitiveResourceLog_bound (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ p : ℝ, 0 ≤ p →
      allocatedFullGridPrimitiveResourceLog m p p p p ≤ (p + a) ^ a := by
  let poly : Polynomial ℕ := allocatedFullGridPrimitiveResourceLog m
    Polynomial.X Polynomial.X Polynomial.X Polynomial.X
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro p hp
  simpa [poly, allocatedFullGridPrimitiveResourceLog, allocatedMixedJointSiteLog,
    allocatedMixedSiteOutputLog, allocatedMixedAccuracyLog, uniformProductAccuracyLog,
    allocatedActiveSiteOutputLog_eval, allocatedInactiveSiteOutputLog_eval,
    allocatedMixedPointCapLog_eval, allocatedComparisonDimension, allocatedSiteSpatialMassLog,
    coefficientMajorantMassLog, allocatedFullGridWindowLog, allocatedFullGridCoefficientLog,
    Polynomial.eval₂_pow] using hbound p hp

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
theorem allocated_full_grid_primitive_error
    {p₁ w v E : ℝ} (hp₁ : 0 ≤ p₁) (hw : 0 ≤ w) (hv : 0 ≤ v) (hE : 0 ≤ E)
    (hdimSmall : dim ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p₁)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p₁) (hn₁ : ∀ j, (n j : ℝ) ≤ p₁)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p₁)
    (M₀ : ℕ) (hqM : q ≤ M₀ ^ (m + 1)) (hM₀ : (M₀ : ℝ) ≤ Real.exp p₁)
    (hS₁ : (S.value : ℝ) ≤ Real.exp p₁)
    (hδ : δ ≤ allocatedSitePrimitiveTolerance m p₁ w v E) (hEbudget : E + 4 ≤ p₁) :
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
    (_hperiod : ∀ j, integerScalarLattice (rowTypes j) (q : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hCexp : ∀ j, (C j : ℝ) ≤ Real.exp p₁) (_hVexp : ∀ j, (V j : ℝ) ≤ Real.exp p₁)
    {X : Type uX} [Fintype X] [DecidableEq X]
    {P₀ : ℝ} (_hP : 0 ≤ P₀) (_hn : (Fintype.card X : ℝ) ≤ P₀)
    (_hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P₀)
    (_hbudget : allocatedSiteErrorFourierOutput m p₁ w v ≤ P₀)
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
    (H : X → ℝ) (_hsize : ∀ x, Real.exp ((P₀ + K) ^ K) ≤ H x)
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H R₁ (U j) (p j))
    (_hR : Real.exp ((P₀ + K) ^ K) ≤ R₁)
    (cells : Finset (ColumnResiduePattern (Option (Fin dim)) X stride)) (_hcells : cells.Nonempty)
    (W : Option (Fin dim) × X → ℝ) (hW : ∀ z, 0 < W z) (_hwidth : ∀ z, ρ * H z.2 ≤ W z),
    let law := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let target := allocatedSupportedFullGridResidueProfile B U b hR hσ S q x hb o bW d f witnesses
    let error := fun y : EuclideanJetLayers U (rowTypes) =>
      law.complexMean (fun y₀ =>
        (allocatedWholeMaskedCoveredProfile (O := rowTypes) B U b hR hσ S x (rows) hb o bW d y₀ q f y : ℂ)) -
      (law.fiberLaw (principalResidueLabel q)).complexMean (fun r => target r y)
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells W z,
      selectedResidueDensityMass stride cells W
        (fun z => ‖error (physicalCubeRowSample (O := rowTypes) U d (rows) p hmp (standardPhysicalCubeOutput z))‖)
        ≤ Real.exp (-E) ∧
      ∀ φ : (Option (Fin dim) × X → ℤ) → ℂ, (∀ z, ‖φ z‖ ≤ 1) →
        ‖∑' z, ((selectedResidueSmoothPMF stride cells W hW hZ z).toReal : ℂ) *
          (error (physicalCubeRowSample (O := rowTypes) U d (rows) p hmp (standardPhysicalCubeOutput z)) * φ z)‖
          ≤ Real.exp (-E) := by
  intro K hSampling x hb o Q _ bW d _ _ f CM Cf hCM hfb hCMexp hCfexp hmask hperiod C V hC hV
    hCexp hVexp X _ _ P₀ hP₀ hn hdim hbudget _ _ _ μ _ _ ν _ _ p hp hmp stride hs R₁ S₀ ρ
    hS hSP hρ hρP hstride H hsize₁ hrank hR₁ cells hcells W hW hwidth law target error
  have hδnn : Real.toNNReal δ ≤ 1 := Real.toNNReal_le_one.mpr
    (hδ.trans (allocatedSitePrimitiveTolerance_le_one m hp₁ hw hv hE))
  have hrowdim : Fintype.card (Fin dim) ≤ m + 1 := by
    simpa only [Fintype.card_fin] using hdimSmall
  have hshare : (physicalIdealErrorShare E 1)⁻¹ ≤ Real.exp p₁ := by
    rw [physicalIdealErrorShare_inv]
    exact Real.exp_le_exp.mpr (by linarith)
  obtain ⟨hLF, hpP, hamb, hδL, hLip, hfreq, hcoeff⟩ :=
    allocatedSiteErrorPrimitive_fourier_budget B U b S (rows) hrowdim
      (fun _ => Subtype.val_injective) hb bW M₀ q hqM (Real.toNNReal δ) CM Cf C V
      hp₁ hw hv hvars hI hn₁ hJ hδnn hM₀ hS₁ hCexp hVexp hCMexp hCfexp hshare
  have heP := Real.exp_le_exp.mpr hbudget
  have hεP : 1 / physicalIdealErrorShare E 1 ≤ Real.exp P₀ := by
    simpa only [one_div] using hshare.trans (Real.exp_le_exp.mpr (hpP.trans hbudget))
  have hprevious := allocated_full_grid_sampled_error B U b hR hσ S q δ witnesses hWitness
    (K := K) hSampling
  obtain ⟨hZ, hmean, htest⟩ := @hprevious x hb o Q _ bW d _ _ f CM Cf hCM hfb hmask hperiod C V hC hV
    X _ _ P₀ hP₀ hn hdim _ _ _ μ _ _ ν _ _ p hp hmp stride hs R₁ S₀ ρ (physicalIdealErrorShare E 1)
    hS hSP hρ (physicalIdealErrorShare_pos E 1) hρP hεP hstride H hsize₁ hrank hR₁ cells hcells W hW hwidth
    (physicalIdealErrorShare E 1) (allocatedSiteErrorFourierInput m p₁ w v)
    (physicalIdealErrorShare_pos E 1) hLF hamb hδL hLip (hfreq.trans heP) (hcoeff.trans heP)
  have hmass := allocatedSiteSpatial_primitive_error_budget B U b (rows) hrowdim
    (fun _ => Subtype.val_injective) hb bW M₀ q hqM CM Cf C hp₁ hw hvars hI hn₁ hJ
    hM₀ hCexp hCMexp hCfexp hδ (le_refl (physicalIdealErrorShare E 1))
    (le_refl (physicalIdealErrorShare E 1))
  exact ⟨hZ, hmean.trans hmass, fun φ hφ => (htest φ hφ).trans hmass⟩

theorem exists_allocated_full_grid_primitive_error
    {D P pSite vSite δ ESite : ℝ}
    (hD : AllocatedComparisonDimensions (G := G) B (Fin dim) (fun j : Fin m => (rowSets j : Type)) D)
    (hα : Fintype.card (Fin dim) ≤ m + 1) (hP : 1 ≤ P) (hpSite : 0 ≤ pSite) (hvSite : 0 ≤ vSite)
    (hPpSite : P ≤ Real.exp pSite) (hq : 0 < q) (hqvSite : (q : ℝ) ≤ Real.exp vSite)
    (hδ : 0 < δ) (hESite : 0 ≤ ESite) (hδESite : δ⁻¹ ≤ Real.exp ESite)
    (hsize : (Fintype.card (Fin dim) + 1) * q ≤ S.value)
    (hgamma : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a}, principalProfileSize (R (allocatedGridIntegerAxis B U b S a).1)
      (Finset.card (layerIntegerPrincipalSlots (G := G) B (allocatedGridIntegerAxis B U b S a).1 (allocatedGridIntegerAxis B U b S a).2)) ≤ 1)
    (hσ1 : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a}, σ (allocatedGridIntegerAxis B U b S a).1 ≤ 1)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hcP : scalarCubePrimitiveEnvelope Empty L 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope (Fin dim) L 1 0 q ≤ P)
    (hrows : ∀ j t, t ∈ rowSets j → t.card ≤ j.val + 1)
    (hB : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a}, max
      (positiveModerateSpectrumBlockCount (allocatedGridIntegerAxis B U b S a).1.val (rowSets (allocatedGridIntegerAxis B U b S a).1).card
        ((layerTailDegree m + 2) * (rowSets (allocatedGridIntegerAxis B U b S a).1).card))
      (uniformSpectrumBlockCount (allocatedGridIntegerAxis B U b S a).1.val (rowSets (allocatedGridIntegerAxis B U b S a).1).card
        (((allocatedGridIntegerAxis B U b S a).1.val + 1) * (rowSets (allocatedGridIntegerAxis B U b S a).1).card)) ≤
      Fintype.card (B ⟨(allocatedGridIntegerAxis B U b S a).1, Sum.inr (allocatedGridIntegerAxis B U b S a).2⟩))
    {p₁ w v E : ℝ} (hp₁ : 0 ≤ p₁) (hw : 0 ≤ w) (hv : 0 ≤ v) (hE : 0 ≤ E)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p₁)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p₁) (hn₁ : ∀ j, (n j : ℝ) ≤ p₁)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p₁)
    (M₀ : ℕ) (hqM : q ≤ M₀ ^ (m + 1)) (hM₀ : (M₀ : ℝ) ≤ Real.exp p₁)
    (hS₁ : (S.value : ℝ) ≤ Real.exp p₁)
    (hδbudget : δ ≤ allocatedSitePrimitiveTolerance m p₁ w v E) (hEbudget : E + 4 ≤ p₁) :
    let O := allocatedMixedJointSiteLog m D pSite vSite (ESite + allocatedFullGridWindowLog D)
    ∃ K : ℕ, 2 ≤ K ∧
      ∃ witnesses : (r : AllocatedPositiveResidue (dim := dim) B U b S q) →
        AllocatedFullGridResidueWitness (dim := dim) B U b S q r.val,
      (∀ r a, ((witnesses r).expansion a).Bounds (Real.exp O) (Real.exp O) (Real.exp O)
        ⟨Real.exp O, Real.exp_nonneg _⟩ (Real.exp (allocatedInactiveSupportLog D))) ∧
      ∀
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
    (_hperiod : ∀ j, integerScalarLattice (rowTypes j) (q : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hCexp : ∀ j, (C j : ℝ) ≤ Real.exp p₁) (_hVexp : ∀ j, (V j : ℝ) ≤ Real.exp p₁)
    {X : Type uX} [Fintype X] [DecidableEq X]
    {P₀ : ℝ} (_hP : 0 ≤ P₀) (_hn : (Fintype.card X : ℝ) ≤ P₀)
    (_hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P₀)
    (_hbudget : allocatedSiteErrorFourierOutput m p₁ w v ≤ P₀)
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
    (H : X → ℝ) (_hsize : ∀ x, Real.exp ((P₀ + K) ^ K) ≤ H x)
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H R₁ (U j) (p j))
    (_hR : Real.exp ((P₀ + K) ^ K) ≤ R₁)
    (cells : Finset (ColumnResiduePattern (Option (Fin dim)) X stride)) (_hcells : cells.Nonempty)
    (W : Option (Fin dim) × X → ℝ) (hW : ∀ z, 0 < W z) (_hwidth : ∀ z, ρ * H z.2 ≤ W z),
    let law := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let target := allocatedSupportedFullGridResidueProfile B U b hR hσ S q x hb o bW d f witnesses
    let error := fun y : EuclideanJetLayers U (rowTypes) =>
      law.complexMean (fun y₀ =>
        (allocatedWholeMaskedCoveredProfile (O := rowTypes) B U b hR hσ S x (rows) hb o bW d y₀ q f y : ℂ)) -
      (law.fiberLaw (principalResidueLabel q)).complexMean (fun r => target r y)
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells W z,
      selectedResidueDensityMass stride cells W
        (fun z => ‖error (physicalCubeRowSample (O := rowTypes) U d (rows) p hmp (standardPhysicalCubeOutput z))‖)
        ≤ Real.exp (-E) ∧
      ∀ φ : (Option (Fin dim) × X → ℤ) → ℂ, (∀ z, ‖φ z‖ ≤ 1) →
        ‖∑' z, ((selectedResidueSmoothPMF stride cells W hW hZ z).toReal : ℂ) *
          (error (physicalCubeRowSample (O := rowTypes) U d (rows) p hmp (standardPhysicalCubeOutput z)) * φ z)‖
          ≤ Real.exp (-E) := by
  obtain ⟨K, hK, hSampling⟩ :=
    exists_allocated_boolean_rows_sampling.{uX,uJ,uG,uI,uB,uQ} m dim
  obtain ⟨witnesses, hBounds, hWitnesses⟩ := exists_allocated_full_grid_residue_sampling
    B U b hR hσ S q hD hα hP hpSite hvSite hPpSite hq hqvSite hδ hESite hδESite
    hsize hgamma hσ1 L hL hcP hsP hrows hB
  have hdimSmall : dim ≤ m + 1 := by simpa only [Fintype.card_fin] using hα
  refine ⟨K, hK, witnesses, hBounds, ?_⟩
  exact allocated_full_grid_primitive_error B U b hR hσ S q δ witnesses hWitnesses
    hp₁ hw hv hE hdimSmall hvars hI hn₁ hJ M₀ hqM hM₀ hS₁ hδbudget hEbudget
    (K := K) (@hSampling (fun j => Finset.Subtype.fintype (rowSets j)))

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

theorem exists_allocated_full_grid_primitive_sampling
    {p w v E : ℝ} (hp : 0 ≤ p) (hw : 0 ≤ w) (hv : 0 ≤ v) (hE : 0 ≤ E)
    (hα : Fintype.card (Fin dim) ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (M₀ : ℕ) (hqM : q ≤ M₀ ^ (m + 1)) (hM₀ : (M₀ : ℝ) ≤ Real.exp p)
    (hsize : (Fintype.card (Fin dim) + 1) * q ≤ S.value)
    (hgamma : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a},
      principalProfileSize (R (allocatedGridIntegerAxis B U b S a).1)
        (Finset.card (layerIntegerPrincipalSlots (G := G) B
          (allocatedGridIntegerAxis B U b S a).1 (allocatedGridIntegerAxis B U b S a).2)) ≤ 1)
    (hσ1 : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a},
      σ (allocatedGridIntegerAxis B U b S a).1 ≤ 1)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hcP : scalarCubePrimitiveEnvelope Empty L 16 (128 * probabilityProfileLipschitz) 1 ≤ Real.exp p)
    (hsP : scalarCubePrimitiveEnvelope (Fin dim) L 1 0 q ≤ Real.exp p)
    (hB : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a}, max
      (positiveModerateSpectrumBlockCount (allocatedGridIntegerAxis B U b S a).1.val
        (rowSets (allocatedGridIntegerAxis B U b S a).1).card
        ((layerTailDegree m + 2) * (rowSets (allocatedGridIntegerAxis B U b S a).1).card))
      (uniformSpectrumBlockCount (allocatedGridIntegerAxis B U b S a).1.val
        (rowSets (allocatedGridIntegerAxis B U b S a).1).card
        (((allocatedGridIntegerAxis B U b S a).1.val + 1) * (rowSets (allocatedGridIntegerAxis B U b S a).1).card)) ≤
      Fintype.card (B ⟨(allocatedGridIntegerAxis B U b S a).1, Sum.inr (allocatedGridIntegerAxis B U b S a).2⟩)) :
    let O := allocatedFullGridPrimitiveResourceLog m p w v E
    ∃ W : (r : AllocatedPositiveResidue (dim := dim) B U b S q) →
        AllocatedFullGridResidueWitness (dim := dim) B U b S q r.val,
      (∀ r a, ((W r).expansion a).Bounds (Real.exp O) (Real.exp O) (Real.exp O)
        ⟨Real.exp O, Real.exp_nonneg _⟩
        (Real.exp (allocatedInactiveSupportLog (allocatedComparisonDimension m p)))) ∧
      ∀ r, AllocatedFullGridResidueSampling.{uG,uI,uB,uJ,uQ,uX} B U b hR hσ S q (W r)
        (allocatedSitePrimitiveTolerance m p w v E) := by
  let D : ℝ := allocatedComparisonDimension m p
  have hD := allocatedComparisonDimensions_of_primitive B
    (O := fun j => (rowSets j : Type)) (rows) hα (fun _ => Subtype.val_injective) hp hvars hI hn
  have hmass := allocatedSiteSpatialMassLog_nonneg hD.nonneg hw hv
  have hP : 1 ≤ Real.exp p := by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hp
  have hqv : (q : ℝ) ≤ Real.exp ((m + 1 : ℕ) * p) := by
    calc
      _ ≤ (M₀ : ℝ) ^ (m + 1) := by exact_mod_cast hqM
      _ ≤ Real.exp p ^ (m + 1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hM₀ _
      _ = _ := (Real.exp_nat_mul p (m + 1)).symm
  have hrows (j : Fin m) (t : Finset (Fin dim)) (ht : t ∈ rowSets j) : t.card ≤ j.val + 1 :=
    (mem_boundedBooleanJetRows (j.val + 1) t).mp ht
  exact exists_allocated_full_grid_residue_sampling B U b hR hσ S q hD hα hP hp (by positivity)
    (le_refl (Real.exp p)) (NeZero.pos q) hqv (allocatedSitePrimitiveTolerance_pos m p w v E)
    (by positivity : 0 ≤ E + allocatedSiteSpatialMassLog D w v + 3)
    (allocatedSitePrimitiveTolerance_inv m p w v E).le hsize hgamma hσ1 L hL hcP hsP hrows hB

theorem exists_allocated_full_grid_primitive_comparison
    {p w v E : ℝ} (hp : 0 ≤ p) (hw : 0 ≤ w) (hv : 0 ≤ v) (hE : 0 ≤ E)
    (hα : Fintype.card (Fin dim) ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (M₀ : ℕ) (hqM : q ≤ M₀ ^ (m + 1)) (hM₀ : (M₀ : ℝ) ≤ Real.exp p)
    (hsize : (Fintype.card (Fin dim) + 1) * q ≤ S.value)
    (hgamma : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a},
      principalProfileSize (R (allocatedGridIntegerAxis B U b S a).1)
        (Finset.card (layerIntegerPrincipalSlots (G := G) B
          (allocatedGridIntegerAxis B U b S a).1 (allocatedGridIntegerAxis B U b S a).2)) ≤ 1)
    (hσ1 : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a},
      σ (allocatedGridIntegerAxis B U b S a).1 ≤ 1)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hcP : scalarCubePrimitiveEnvelope Empty L 16 (128 * probabilityProfileLipschitz) 1 ≤ Real.exp p)
    (hsP : scalarCubePrimitiveEnvelope (Fin dim) L 1 0 q ≤ Real.exp p)
    (hB : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a}, max
      (positiveModerateSpectrumBlockCount (allocatedGridIntegerAxis B U b S a).1.val
        (rowSets (allocatedGridIntegerAxis B U b S a).1).card
        ((layerTailDegree m + 2) * (rowSets (allocatedGridIntegerAxis B U b S a).1).card))
      (uniformSpectrumBlockCount (allocatedGridIntegerAxis B U b S a).1.val
        (rowSets (allocatedGridIntegerAxis B U b S a).1).card
        (((allocatedGridIntegerAxis B U b S a).1.val + 1) * (rowSets (allocatedGridIntegerAxis B U b S a).1).card)) ≤
      Fintype.card (B ⟨(allocatedGridIntegerAxis B U b S a).1, Sum.inr (allocatedGridIntegerAxis B U b S a).2⟩))
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (hS : (S.value : ℝ) ≤ Real.exp p) (hEbudget : E + 4 ≤ p) :
    let O := allocatedFullGridPrimitiveResourceLog m p w v E
    ∃ K : ℕ, 2 ≤ K ∧
      ∃ witnesses : (r : AllocatedPositiveResidue (dim := dim) B U b S q) →
        AllocatedFullGridResidueWitness (dim := dim) B U b S q r.val,
      (∀ r a, ((witnesses r).expansion a).Bounds (Real.exp O) (Real.exp O) (Real.exp O)
        ⟨Real.exp O, Real.exp_nonneg _⟩
        (Real.exp (allocatedInactiveSupportLog (allocatedComparisonDimension m p)))) ∧
      ∀
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
    (_hperiod : ∀ j, integerScalarLattice (rowTypes j) (q : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hCexp : ∀ j, (C j : ℝ) ≤ Real.exp p) (_hVexp : ∀ j, (V j : ℝ) ≤ Real.exp p)
    {X : Type uX} [Fintype X] [DecidableEq X]
    {P₀ : ℝ} (_hP : 0 ≤ P₀) (_hn : (Fintype.card X : ℝ) ≤ P₀)
    (_hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P₀)
    (_hbudget : allocatedSiteErrorFourierOutput m p w v ≤ P₀)
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (polys : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (polys j))
    (hmp : ∀ j e, coefficients (polys j) e ∈ U j)
    (stride : X → ℕ) (_hs : ∀ x, 0 < stride x)
    {R₁ S₀ ρ : ℝ} (_hS : 0 ≤ S₀) (_hSP : S₀ ≤ Real.exp P₀) (_hρ : 0 < ρ)
    (_hρP : 1 / ρ ≤ Real.exp P₀)
    (_hstride : ∀ x, (stride x : ℝ) ≤ S₀)
    (H : X → ℝ) (_hsize : ∀ x, Real.exp ((P₀ + K) ^ K) ≤ H x)
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H R₁ (U j) (polys j))
    (_hR : Real.exp ((P₀ + K) ^ K) ≤ R₁)
    (cells : Finset (ColumnResiduePattern (Option (Fin dim)) X stride)) (_hcells : cells.Nonempty)
    (W : Option (Fin dim) × X → ℝ) (hW : ∀ z, 0 < W z) (_hwidth : ∀ z, ρ * H z.2 ≤ W z),
    let law := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let target := allocatedSupportedFullGridResidueProfile B U b hR hσ S q x hb o bW d f witnesses
    let error := fun y : EuclideanJetLayers U (rowTypes) =>
      law.complexMean (fun y₀ =>
        (allocatedWholeMaskedCoveredProfile (O := rowTypes) B U b hR hσ S x (rows) hb o bW d y₀ q f y : ℂ)) -
      (law.fiberLaw (principalResidueLabel q)).complexMean (fun r => target r y)
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells W z,
      selectedResidueDensityMass stride cells W
        (fun z => ‖error (physicalCubeRowSample (O := rowTypes) U d (rows) polys hmp (standardPhysicalCubeOutput z))‖)
        ≤ Real.exp (-E) ∧
      ∀ φ : (Option (Fin dim) × X → ℤ) → ℂ, (∀ z, ‖φ z‖ ≤ 1) →
        ‖∑' z, ((selectedResidueSmoothPMF stride cells W hW hZ z).toReal : ℂ) *
          (error (physicalCubeRowSample (O := rowTypes) U d (rows) polys hmp (standardPhysicalCubeOutput z)) * φ z)‖
          ≤ Real.exp (-E) := by
  obtain ⟨K, hK, hSampling⟩ :=
    exists_allocated_boolean_rows_sampling.{uX,uJ,uG,uI,uB,uQ} m dim
  obtain ⟨witnesses, hBounds, hWitnesses⟩ := exists_allocated_full_grid_primitive_sampling
    B U b hR hσ S q hp hw hv hE hα hvars hI hn M₀ hqM hM₀ hsize hgamma hσ1 L hL hcP hsP hB
  have hdim : dim ≤ m + 1 := by simpa only [Fintype.card_fin] using hα
  refine ⟨K, hK, witnesses, hBounds, ?_⟩
  exact allocated_full_grid_primitive_error B U b hR hσ S q
    (allocatedSitePrimitiveTolerance m p w v E) witnesses hWitnesses
    hp hw hv hE hdim hvars hI hn hJ M₀ hqM hM₀ hS (le_refl _) hEbudget
    (K := K) (@hSampling (fun j => Finset.Subtype.fintype (rowSets j)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type uG} [Fintype G]
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

theorem exists_allocated_early_full_grid_family
    {Psp p w v E : ℝ} (hPsp : 0 ≤ Psp) (hp : 0 ≤ p) (hw : 0 ≤ w) (hv : 0 ≤ v) (hE : 0 ≤ E)
    (hα : Fintype.card (Fin dim) ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (hcutoff : (allocatedRefinedPeriodCutoff m Psp : ℝ) ≤ Real.exp p)
    (hsize : (Fintype.card (Fin dim) + 1) * allocatedRefinedPeriodCutoff m Psp ≤ S.value)
    (hgamma : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a},
      principalProfileSize (R (allocatedGridIntegerAxis B U b S a).1)
        (Finset.card (layerIntegerPrincipalSlots (G := G) B
          (allocatedGridIntegerAxis B U b S a).1 (allocatedGridIntegerAxis B U b S a).2)) ≤ 1)
    (hσ1 : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a},
      σ (allocatedGridIntegerAxis B U b S a).1 ≤ 1)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hcP : scalarCubePrimitiveEnvelope Empty L 16 (128 * probabilityProfileLipschitz) 1 ≤ Real.exp p)
    (hsP : scalarCubePrimitiveEnvelope (Fin dim) L 1 0 (allocatedRefinedPeriodCutoff m Psp) ≤ Real.exp p)
    (hB : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a}, max
      (positiveModerateSpectrumBlockCount (allocatedGridIntegerAxis B U b S a).1.val
        (rowSets (allocatedGridIntegerAxis B U b S a).1).card
        ((layerTailDegree m + 2) * (rowSets (allocatedGridIntegerAxis B U b S a).1).card))
      (uniformSpectrumBlockCount (allocatedGridIntegerAxis B U b S a).1.val
        (rowSets (allocatedGridIntegerAxis B U b S a).1).card
        (((allocatedGridIntegerAxis B U b S a).1.val + 1) * (rowSets (allocatedGridIntegerAxis B U b S a).1).card)) ≤
      Fintype.card (B ⟨(allocatedGridIntegerAxis B U b S a).1, Sum.inr (allocatedGridIntegerAxis B U b S a).2⟩)) :
    let O := allocatedFullGridPrimitiveResourceLog m p w v E
    ∃ witnesses : (q : AllocatedRefinedPeriodIndex m Psp) →
        (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
        AllocatedFullGridResidueWitness (dim := dim) B U b S (q.val : ℕ) r.val,
      (∀ q r a, ((witnesses q r).expansion a).Bounds (Real.exp O) (Real.exp O) (Real.exp O)
        ⟨Real.exp O, Real.exp_nonneg _⟩
        (Real.exp (allocatedInactiveSupportLog (allocatedComparisonDimension m p)))) ∧
      ∀ q r, AllocatedFullGridResidueSampling.{uG,uI,uB,uJ,uQ,uX}
        B U b hR hσ S (q.val : ℕ) (witnesses q r) (allocatedSitePrimitiveTolerance m p w v E) := by
  have hEach (q : AllocatedRefinedPeriodIndex m Psp) :
      ∃ W : (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
          AllocatedFullGridResidueWitness (dim := dim) B U b S (q.val : ℕ) r.val,
        (∀ r a, ((W r).expansion a).Bounds
          (Real.exp (allocatedFullGridPrimitiveResourceLog m p w v E))
          (Real.exp (allocatedFullGridPrimitiveResourceLog m p w v E))
          (Real.exp (allocatedFullGridPrimitiveResourceLog m p w v E))
          ⟨Real.exp (allocatedFullGridPrimitiveResourceLog m p w v E), Real.exp_nonneg _⟩
          (Real.exp (allocatedInactiveSupportLog (allocatedComparisonDimension m p)))) ∧
        ∀ r, AllocatedFullGridResidueSampling.{uG,uI,uB,uJ,uQ,uX}
          B U b hR hσ S (q.val : ℕ) (W r) (allocatedSitePrimitiveTolerance m p w v E) := by
    let _ : NeZero (q.val : ℕ) := ⟨q.val.property.ne'⟩
    have hsizeq : (Fintype.card (Fin dim) + 1) * (q.val : ℕ) ≤ S.value :=
      (Nat.mul_le_mul_left _ q.property).trans hsize
    have hsPq : scalarCubePrimitiveEnvelope (Fin dim) L 1 0 (q.val : ℕ) ≤ Real.exp p :=
      (scalarCubePrimitiveEnvelope_mono (Fin dim) L le_rfl le_rfl q.property).trans hsP
    exact exists_allocated_full_grid_primitive_sampling B U b hR hσ S (q.val : ℕ)
      hp hw hv hE hα hvars hI hn (allocatedRefinedPeriodCutoff m Psp)
      (allocatedRefinedPeriodIndex_power m hPsp q) hcutoff hsizeq hgamma hσ1 L hL hcP hsPq hB
  choose witnesses hBounds hSampling using hEach
  exact ⟨witnesses, hBounds, hSampling⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq fullBooleanRowSetFintype

def allocatedFullGridCoefficientPreLog {A : Type*} [Semiring A]
    (m : ℕ) (D O : A) : A := (2 ^ (m + 1) : ℕ) + D * O

theorem coverSiteCoefficient_uniform_exp_bound {A V : Type*} [Fintype A] [Fintype V]
    (e : A → ScalarSiteExpansion V) {T C H : A → ℝ} {L : ℝ≥0} {O : ℝ}
    (he : ∀ a, (e a).Bounds (T a) (C a) (Real.exp O) L (H a)) :
    (∑ k, ‖coverSiteCoefficient e k‖) ≤
      Real.exp ((Fintype.card V : ℝ) + Fintype.card A * O) := by
  apply (coverSiteCoefficient_bound e he).trans
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpow : (2 : ℝ) ^ Fintype.card V ≤ Real.exp (Fintype.card V : ℝ) := by
    simpa only [← Real.exp_nat_mul, mul_one] using
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo (Fintype.card V)
  simp only [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]
  exact (mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (q : ℕ) [NeZero q]
variable (W : (r : AllocatedPositiveResidue (dim := dim) B U b S q) →
  AllocatedFullGridResidueWitness (dim := dim) B U b S q r.val)

local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}

theorem allocatedFullGrid_coefficient_pre_bound
    {T C H : gridAxes → ℝ} {L : ℝ≥0} {O D : ℝ}
    (he : ∀ r a, ((W r).expansion a).Bounds (T a) (C a) (Real.exp O) L (H a))
    (hO : 0 ≤ O) (hdim : dim ≤ m + 1)
    (haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ D) :
    (∀ r, (∑ k, ‖coverSiteCoefficient (W r).expansion k‖) ≤
      Real.exp (allocatedFullGridCoefficientPreLog m D O)) ∧
    allocatedClippedFullGridCoverCoefficientMass B U b S q W ≤
      Real.exp (allocatedFullGridCoefficientPreLog m D O) := by
  have hgrid : (Fintype.card gridAxes : ℝ) ≤ D :=
    (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans haxes
  have hsites : (Fintype.card (Finset (Fin dim)) : ℝ) ≤ (2 ^ (m + 1) : ℕ) := by
    simp only [Fintype.card_finset, Fintype.card_fin]
    exact_mod_cast Nat.pow_le_pow_right (by omega : 1 ≤ 2) hdim
  have hlocal (r : AllocatedPositiveResidue (dim := dim) B U b S q) :
      (∑ k, ‖coverSiteCoefficient (W r).expansion k‖) ≤
        Real.exp (allocatedFullGridCoefficientPreLog m D O) := by
    apply (coverSiteCoefficient_uniform_exp_bound (W r).expansion (he r)).trans
    apply Real.exp_le_exp.mpr
    exact add_le_add hsites (mul_le_mul_of_nonneg_right hgrid hO)
  exact ⟨hlocal, allocatedClippedFullGridCoverCoefficientMass_le B U b S q W _ hlocal⟩

end Erdos3.VectorPolynomial

end

end OAI
