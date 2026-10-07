import OAI.Combinatorics.Progressions.Estimates.CanonicalSiteBlocks
import OAI.Combinatorics.Progressions.Lattices.AllocatedPointwiseResidueCover

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq
attribute [local instance] ScalarSiteExpansion.termFinite

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
  AllocatedResidueSiteWitness (dim := dim) B U b S q r.val)
variable (hWitness : ∀ r, AllocatedResidueSiteSampling.{uG,uI,uB,uJ,uQ,uX}
  B U b hR hσ S q (witnesses r) δ)

local notation "activeAxes" => {a : {a // allocatedGridAxis (I := I) U b S.value a} // allocatedActiveGrid B U b S a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "siteH" => (fun a : activeAxes => allocatedNaturalSiteRadius (G := G) B
  (Sigma.fst (ig (Subtype.val a))) (Sigma.snd (ig (Subtype.val a)))
  (rowSets (Sigma.fst (ig (Subtype.val a)))) + 1 / 4)

include hWitness in
theorem exists_allocated_ideal_cover_error
    {p₁ w e E : ℝ} (hp₁ : 0 ≤ p₁) (hw : 0 ≤ w) (he : 0 ≤ e) (hE : 0 ≤ E)
    (hdimSmall : dim ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p₁)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p₁) (hn₁ : ∀ j, (n j : ℝ) ≤ p₁)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p₁)
    (M₀ : ℕ) (hqM : q ≤ M₀ ^ (m + 1)) (hM₀ : (M₀ : ℝ) ≤ Real.exp p₁)
    (hS₁ : (S.value : ℝ) ≤ Real.exp p₁)
    (hδ : δ ≤ allocatedSitePrimitiveTolerance m p₁ w (allocatedIdealProfileLog m p₁ e) E)
    (hEbudget : E + 4 ≤ p₁)
    {Nt Den Cc : activeAxes → ℝ} {L : ℝ≥0}
    (hBounds : ∀ r a, ((witnesses r).expansion a).Bounds (Nt a) (Den a) (Cc a) L ((siteH) a))
    {K : ℕ} (hSampling : AllocatedBooleanRowsSampling.{uX,uJ,uG,uI,uB,uQ} m dim K (rowTypes) (rows))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Q : Fin m → Type uQ} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d]
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (C V : Fin m → ℝ≥0)
    (hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (hCexp : ∀ j, (C j : ℝ) ≤ Real.exp p₁) (hVexp : ∀ j, (V j : ℝ) ≤ Real.exp p₁)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp p₁) (hσ1 : ∀ j, σ j ≤ 1)
    (Qsite : ℝ≥0) (hQsite : ∀ a : activeAxes, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (ig a.val).1 (ig a.val).2) : ℝ) + 1) ≤ Qsite)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
    (hsmall : ∀ j, R j ≤ allocatedIdealCoverRadius (G := G) B rowSets Cinv j) :
    ∃ g : (r : AllocatedPositiveResidue (dim := dim) B U b S q) →
        (∀ a, ((witnesses r).expansion a).Term) → Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ),
      (∀ r k s, LipschitzWith (max (((Fintype.card activeAxes * L) * Qsite) *
        (Real.toNNReal (Real.exp p₁) * ∑ j, C j * Fintype.card (J j)) * commonSitePeriod (witnesses r).expansion k)
          (4 * commonSitePeriod (witnesses r).expansion k)) (g r k s) ∧ ∀ z, ‖g r k s z‖ ≤ 1) ∧
      (∀ r, (∑ k, ‖coverSiteCoefficient (witnesses r).expansion k‖) ≤
        (2 : ℝ) ^ Fintype.card (Finset (Fin dim)) * ∏ a, Cc a) ∧
      allocatedResidueCoverCoefficientMass B U b S q witnesses ≤
        (2 : ℝ) ^ Fintype.card (Finset (Fin dim)) * ∏ a, Cc a ∧
      ∀ (τ : ℝ≥0), 0 < τ → τ ≤ 1 → (τ : ℝ)⁻¹ ≤ Real.exp e → ∀
        (x : G → IntegerScalarCubeBox (Fin dim) S.value)
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
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ Real.exp w)
    (_hperiod : ∀ j, integerScalarLattice (rowTypes j) (q : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    {X : Type uX} [Fintype X] [DecidableEq X]
    {P₀ : ℝ} (_hP : 0 ≤ P₀) (_hn : (Fintype.card X : ℝ) ≤ P₀)
    (_hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P₀)
    (_hbudget : allocatedSiteErrorFourierOutput m p₁ w (allocatedIdealProfileLog m p₁ e) ≤ P₀)
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
    let f := allocatedPhysicalLongIdeal B U b hR S rowSets τ
    let law := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let error := fun z : Option (Fin dim) × X → ℤ =>
      law.complexMean (fun y₀ =>
        (allocatedWholeMaskedCoveredProfile (O := rowTypes) B U b hR hσ S x (rows) hb o bW d y₀ q f
          (physicalCubeRowSample U d (rows) p hmp (standardPhysicalCubeOutput z)) : ℂ)) -
      (law.fiberLaw (principalResidueLabel q)).complexMean
        (allocatedSupportedIdealCoverValue B U b hR hσ S q witnesses hb o bW d g τ x p hmp
          (standardPhysicalCubeOutput z))
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells W z,
      selectedResidueDensityMass stride cells W (fun z => ‖error z‖) ≤ Real.exp (-E) ∧
      ∀ φ : (Option (Fin dim) × X → ℤ) → ℂ, (∀ z, ‖φ z‖ ≤ 1) →
        ‖∑' z, ((selectedResidueSmoothPMF stride cells W hW hZ z).toReal : ℂ) *
          (error z * φ z)‖ ≤ Real.exp (-E) := by
  obtain ⟨g, hg, hc, hmass, hcover⟩ := exists_allocated_ideal_residue_cover B U b hR hσ S q
    witnesses hb o bW d hBounds Qsite hQsite C hC (Real.toNNReal (Real.exp p₁))
    (fun j => (hRi j).trans (Real.le_coe_toNNReal _)) hσ1 Cinv hCinv hchart hsmall
  refine ⟨g, hg, hc, hmass, ?_⟩
  intro τ hτ hτ1 hτe x hmask hperiod X _ _ P₀ hP₀ hn hdim hbudget _ _ _ μ _ _ ν _ _
    p hp hmp stride hs R₁ S₀ ρ hS hSP hρ hρP hstride H hsize hrank hR₁ cells hcells W hW hwidth f law error
  let CM : ℝ≥0 := ⟨Real.exp w, (Real.exp_pos _).le⟩
  let Cf : ℝ≥0 := ⟨Real.exp (allocatedIdealProfileLog m p₁ e), (Real.exp_pos _).le⟩
  have hfb := allocatedPhysicalLongIdeal_primitive_bound B U b hR S rowSets hp₁ he
    (by simpa only [Fintype.card_fin] using hdimSmall) hvars hI hn₁ hRi τ hτ hτe
  have hprevious := allocated_residue_site_primitive_error B U b hR hσ S q δ witnesses hWitness
    hp₁ hw (allocatedIdealProfileLog_nonneg m hp₁ he) hE hdimSmall hvars hI hn₁ hJ
    M₀ hqM hM₀ hS₁ hδ hEbudget (K := K) hSampling
  obtain ⟨hZ, hmean, htest⟩ := @hprevious x hb o Q _ bW d _ _ f CM Cf
    (Real.one_le_exp_iff.mpr hw) hfb (le_refl _) (le_refl _) hmask hperiod C V hC hV hCexp hVexp
    X _ _ P₀ hP₀ hn hdim hbudget _ _ _ μ _ _ ν _ _ p hp hmp stride hs R₁ S₀ ρ
    hS hSP hρ hρP hstride H hsize hrank hR₁ cells hcells W hW hwidth
  let oldError := fun z : Option (Fin dim) × X → ℤ =>
    law.complexMean (fun y₀ =>
      (allocatedWholeMaskedCoveredProfile (O := rowTypes) B U b hR hσ S x (rows) hb o bW d y₀ q f
        (physicalCubeRowSample U d (rows) p hmp (standardPhysicalCubeOutput z)) : ℂ)) -
    (law.fiberLaw (principalResidueLabel q)).complexMean (fun r =>
      allocatedSupportedResidueSiteProfile B U b hR hσ S q x hb o bW d f witnesses r
        (physicalCubeRowSample U d (rows) p hmp (standardPhysicalCubeOutput z)))
  have hid : oldError = error := by
    funext z
    exact congrArg (fun t : ℂ => law.complexMean (fun y₀ =>
      (allocatedWholeMaskedCoveredProfile (O := rowTypes) B U b hR hσ S x (rows) hb o bW d y₀ q f
        (physicalCubeRowSample U d (rows) p hmp (standardPhysicalCubeOutput z)) : ℂ)) - t)
      (hcover τ hτ hτ1 x p hp hmp (standardPhysicalCubeOutput z))
  change selectedResidueDensityMass stride cells W (fun z => ‖oldError z‖) ≤ Real.exp (-E) at hmean
  refine ⟨hZ, by simpa only [hid] using hmean, ?_⟩
  intro φ hφ
  have ht := htest φ hφ
  change ‖∑' z, ((selectedResidueSmoothPMF stride cells W hW hZ z).toReal : ℂ) *
    (oldError z * φ z)‖ ≤ Real.exp (-E) at ht
  simpa only [hid] using ht

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq
attribute [local instance] ScalarSiteExpansion.termFinite

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

variable {p₁ w e E : ℝ}
local notation "δ" => allocatedSitePrimitiveTolerance m p₁ w (allocatedIdealProfileLog m p₁ e) E
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "active" => allocatedActiveGrid B U b S
local notation "activeAxes" => {a : {a // grid a} // active a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "axisN" => allocatedGridNaturalScale B U b S
local notation "volumeN" => allocatedActiveNaturalVolume B U b S rowSets
local notation "rowFamily" => (fun a : (Σ j : Fin m, Fin (n j)) => rowSets (Sigma.fst a))

variable (hq : 0 < q) (hsize : (Fintype.card (Fin dim) + 1) * q ≤ S.value)
variable (P Λ : ℝ)
variable (M : {a : {a // allocatedGridAxis (I := I) U b S.value a} // allocatedActiveGrid B U b S a} → ℕ)
variable [∀ a, NeZero (M a)]

local notation "pointTolerance" => allocatedSitePointTolerance (G := G) B rowSets δ
local notation "trueCap" => allocatedGridFamilyCap B (rowFamily) P + 1
local notation "halfAccuracy" => uniformProductAccuracy (Fintype.card (Σ j : Fin m, Fin (n j))) trueCap pointTolerance / 2
local notation "torus" => (fun a : activeAxes => allocatedGridTorusFactor B (Fin dim) (ig (Subtype.val a)))
local notation "cap" => (fun a : activeAxes => allocatedGridPointCap B P (ig (Subtype.val a)) (rowSets (Sigma.fst (ig (Subtype.val a)))))
local notation "siteH" => (fun a : activeAxes =>
  allocatedNaturalSiteRadius (G := G) B (Sigma.fst (ig (Subtype.val a))) (Sigma.snd (ig (Subtype.val a))) (rowSets (Sigma.fst (ig (Subtype.val a)))) + 1 / 4)
local notation "bias" => (fun a : activeAxes => positiveModerateRetainedBias (Fin.val (Sigma.fst (ig (Subtype.val a))))
  (Finset.card (rowSets (Sigma.fst (ig (Subtype.val a))))) ((layerTailDegree m + 2) * Finset.card (rowSets (Sigma.fst (ig (Subtype.val a)))))
  P ((torus) a : ℝ) ((2 * ((torus) a : ℝ)) ^ Finset.card (rowSets (Sigma.fst (ig (Subtype.val a))))) halfAccuracy)
local notation "freq" => (fun a : activeAxes => Real.toNNReal (positiveRetainedFrequencyBound
  (Fin.val (Sigma.fst (ig (Subtype.val a)))) (Finset.card (rowSets (Sigma.fst (ig (Subtype.val a))))) P ((torus) a : ℝ) ((bias) a)))
local notation "siteLip" => (NNReal.mk (Real.exp (1 + 6 * Λ + 12)) (Real.exp_nonneg _) + 4 : ℝ≥0)
local notation "coefficientCap" => (fun a : activeAxes =>
  allocatedGridPointCap B P (ig (Subtype.val a)) (rowSets (Sigma.fst (ig (Subtype.val a)))) *
    Real.exp (Fintype.card (Finset (Fin dim)) * (4 * Λ + 8) + Λ))

include hq hsize in
theorem exists_constructed_allocated_ideal_cover_error
    (hp₁ : 0 ≤ p₁) (hw : 0 ≤ w) (he : 0 ≤ e) (hE : 0 ≤ E)
    (hdimSmall : dim ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p₁)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p₁) (hn₁ : ∀ j, (n j : ℝ) ≤ p₁)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p₁)
    (M₀ : ℕ) (hqM : q ≤ M₀ ^ (m + 1)) (hM₀ : (M₀ : ℝ) ≤ Real.exp p₁)
    (hS₁ : (S.value : ℝ) ≤ Real.exp p₁)
    (hEbudget : E + 4 ≤ p₁) (hP : 1 ≤ P)
    (hgamma : ∀ a : activeAxes, principalProfileSize (R (ig a.val).1)
      (Finset.card (layerIntegerPrincipalSlots (G := G) B (ig a.val).1 (ig a.val).2)) ≤ S.value)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hcP : scalarCubePrimitiveEnvelope Empty L 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope (Fin dim) L 1 0 q ≤ P)
    (hM : ∀ a, M a = (torus) a * axisN a.val)
    (hB : ∀ a : activeAxes, positiveModerateSpectrumBlockCount (ig a.val).1.val
      (rowSets (ig a.val).1).card ((layerTailDegree m + 2) * (rowSets (ig a.val).1).card) ≤
        Fintype.card (B ⟨(ig a.val).1, Sum.inr (ig a.val).2⟩))
    (T : ℝ) (hT : 0 ≤ T)
    (hcap : allocatedGridFamilyCap B (rowFamily) P + 1 ≤ Real.exp T)
    (hΛbudget : allocatedSiteConstructionLog m p₁ w (allocatedIdealProfileLog m p₁ e) E T ≤ Λ)
    (hLΛ : ∀ a, ((CircleFourier.characterLipConstant * ((rowSets (ig a.val).1).card * (freq) a) + 4) *
      (2 : ℝ≥0) ^ Fintype.card (Fin dim) : ℝ≥0) ≤ Real.exp Λ) :
    ∃ K : ℕ, 2 ≤ K ∧
      ∃ witnesses : (r : AllocatedPositiveResidue (dim := dim) B U b S q) →
        AllocatedResidueSiteWitness (dim := dim) B U b S q r.val,
      (∀ r, allocatedActiveSiteBounds B U b S rowSets P pointTolerance Λ M (witnesses r).expansion) ∧ ∀
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Q : Fin m → Type uQ} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d]
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hCexp : ∀ j, (C j : ℝ) ≤ Real.exp p₁) (_hVexp : ∀ j, (V j : ℝ) ≤ Real.exp p₁)
    (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp p₁) (_hσ1 : ∀ j, σ j ≤ 1)
    (Qsite : ℝ≥0) (_hQsite : ∀ a : activeAxes, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (ig a.val).1 (ig a.val).2) : ℝ) + 1) ≤ Qsite)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, R j ≤ allocatedIdealCoverRadius (G := G) B rowSets Cinv j),
    ∃ g : (r : AllocatedPositiveResidue (dim := dim) B U b S q) →
        (∀ a, ((witnesses r).expansion a).Term) → Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ),
      (∀ r k s, LipschitzWith (max (((Fintype.card activeAxes * siteLip) * Qsite) *
        (Real.toNNReal (Real.exp p₁) * ∑ j, C j * Fintype.card (J j)) * commonSitePeriod (witnesses r).expansion k)
          (4 * commonSitePeriod (witnesses r).expansion k)) (g r k s) ∧ ∀ z, ‖g r k s z‖ ≤ 1) ∧
      (∀ r, (∑ k, ‖coverSiteCoefficient (witnesses r).expansion k‖) ≤
        (2 : ℝ) ^ Fintype.card (Finset (Fin dim)) * ∏ a, (coefficientCap) a) ∧
      allocatedResidueCoverCoefficientMass B U b S q witnesses ≤
        (2 : ℝ) ^ Fintype.card (Finset (Fin dim)) * ∏ a, (coefficientCap) a ∧
      ∀ (τ : ℝ≥0), 0 < τ → τ ≤ 1 → (τ : ℝ)⁻¹ ≤ Real.exp e → ∀
        (x : G → IntegerScalarCubeBox (Fin dim) S.value)
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
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ Real.exp w)
    (_hperiod : ∀ j, integerScalarLattice (rowTypes j) (q : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    {X : Type uX} [Fintype X] [DecidableEq X]
    {P₀ : ℝ} (_hP : 0 ≤ P₀) (_hn : (Fintype.card X : ℝ) ≤ P₀)
    (_hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P₀)
    (_hbudget : allocatedSiteErrorFourierOutput m p₁ w (allocatedIdealProfileLog m p₁ e) ≤ P₀)
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
    let f := allocatedPhysicalLongIdeal B U b hR S rowSets τ
    let law := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let error := fun z : Option (Fin dim) × X → ℤ =>
      law.complexMean (fun y₀ =>
        (allocatedWholeMaskedCoveredProfile (O := rowTypes) B U b hR hσ S x (rows) hb o bW d y₀ q f
          (physicalCubeRowSample U d (rows) p hmp (standardPhysicalCubeOutput z)) : ℂ)) -
      (law.fiberLaw (principalResidueLabel q)).complexMean
        (allocatedSupportedIdealCoverValue B U b hR hσ S q witnesses hb o bW d g τ x p hmp
          (standardPhysicalCubeOutput z))
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells W z,
      selectedResidueDensityMass stride cells W (fun z => ‖error z‖) ≤ Real.exp (-E) ∧
      ∀ φ : (Option (Fin dim) × X → ℤ) → ℂ, (∀ z, ‖φ z‖ ≤ 1) →
        ‖∑' z, ((selectedResidueSmoothPMF stride cells W hW hZ z).toReal : ℂ) *
          (error z * φ z)‖ ≤ Real.exp (-E) := by
  have hv := allocatedIdealProfileLog_nonneg m hp₁ he
  have hδ := allocatedSitePrimitiveTolerance_pos m p₁ w (allocatedIdealProfileLog m p₁ e) E
  have hΛ := (allocatedSiteConstructionLog_bounds m hp₁ hw hv hE hT).1.trans hΛbudget
  have hwindow := allocatedSiteConstruction_primitive_budget B rowSets
    (by simpa only [Fintype.card_fin] using hdimSmall) hp₁ hw hv hE hT hP hvars hI hn₁ hcap
  have hHΛ : ∀ a : activeAxes, (siteH) a ≤ Real.exp Λ :=
    fun a => ((hwindow (ig a.val)).1).trans (Real.exp_le_exp.mpr hΛbudget)
  have hδΛ : ∀ a : activeAxes, (halfAccuracy / ((cap) a + 1))⁻¹ ≤ Real.exp Λ :=
    fun a => ((hwindow (ig a.val)).2).trans (Real.exp_le_exp.mpr hΛbudget)
  obtain ⟨K, hK, hSampling⟩ :=
    exists_allocated_boolean_rows_sampling.{uX,uJ,uG,uI,uB,uQ} m dim
  obtain ⟨witnesses, hBounds, hWitnesses⟩ := exists_allocated_residue_site_sampling
    B U b hR hσ S q hq hsize P δ Λ M hP hδ hΛ hgamma L hL hcP hsP hM hB hHΛ hδΛ hLΛ
  refine ⟨K, hK, witnesses, hBounds, ?_⟩
  intro hb o Q _ bW d _ _ C V hC hV hCexp hVexp hRi hσ1 Qsite hQsite Cinv hCinv hchart hsmall
  have hBounds' := hBounds
  dsimp only [allocatedActiveSiteBounds] at hBounds'
  exact exists_allocated_ideal_cover_error B U b hR hσ S q δ witnesses hWitnesses
    hp₁ hw he hE hdimSmall hvars hI hn₁ hJ M₀ hqM hM₀ hS₁ (le_refl _) hEbudget hBounds'
    (K := K) (@hSampling (fun j => Finset.Subtype.fintype (rowSets j)))
    hb o bW d C V hC hV hCexp hVexp hRi hσ1 Qsite hQsite Cinv hCinv hchart hsmall

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq
attribute [local instance] ScalarSiteExpansion.termFinite

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

variable (M₀ : ℕ)
local notation "period" => kernelPeriodCandidate (m + 1)
local notation "P" => canonicalScalarSourceEnvelope m M₀
local notation "L" => scalarSourceTransitionBound

variable {p₀ p₁ w e E : ℝ}
local notation "δ" => allocatedSitePrimitiveTolerance m p₁ w (allocatedIdealProfileLog m p₁ e) E
local notation "Λ" => allocatedSiteSpectrumLog m p₁ w (allocatedIdealProfileLog m p₁ e) E
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "active" => allocatedActiveGrid B U b S
local notation "activeAxes" => {a : {a // grid a} // active a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "axisN" => allocatedGridNaturalScale B U b S

variable (hsize : (Fintype.card (Fin dim) + 1) * M₀ ^ (m + 1) ≤ S.value)
variable (M : {a : {a // allocatedGridAxis (I := I) U b S.value a} // allocatedActiveGrid B U b S a} → ℕ)
variable [∀ a, NeZero (M a)]

local notation "pointTolerance" => allocatedSitePointTolerance (G := G) B rowSets δ
local notation "torus" => (fun a : activeAxes => allocatedGridTorusFactor B (Fin dim) (ig (Subtype.val a)))
local notation "siteLip" => (NNReal.mk (Real.exp (1 + 6 * Λ + 12)) (Real.exp_nonneg _) + 4 : ℝ≥0)
local notation "coefficientCap" => (fun a : activeAxes =>
  allocatedGridPointCap B P (ig (Subtype.val a)) (rowSets (Sigma.fst (ig (Subtype.val a)))) *
    Real.exp (Fintype.card (Finset (Fin dim)) * (4 * Λ + 8) + Λ))

include hsize in
theorem exists_cutoff_mask_good_kernel_ideal_cover_family
    (hw : 0 ≤ w) (he : 0 ≤ e) (hE : 0 ≤ E)
    (hdimSmall : dim ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p₁)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p₁) (hn₁ : ∀ j, (n j : ℝ) ≤ p₁)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p₁)
    (hp₀ : 0 ≤ p₀) (hcutoff : (M₀ : ℝ) ≤ Real.exp p₀)
    (hSourceLog : canonicalScalarSourceLog m p₀ ≤ p₁)
    (hmaskBudget : (m * 2 ^ (m + 1) : ℕ) * p₀ ≤ w)
    (hS₁ : (S.value : ℝ) ≤ Real.exp p₁)
    (hEbudget : E + 4 ≤ p₁)
    (hgamma : ∀ a : activeAxes, principalProfileSize (R (ig a.val).1)
      (Finset.card (layerIntegerPrincipalSlots (G := G) B (ig a.val).1 (ig a.val).2)) ≤ S.value)
    (hM : ∀ a, M a = (torus) a * axisN a.val)
    (hB : ∀ a : activeAxes, positiveModerateSpectrumBlockCount (ig a.val).1.val
      (rowSets (ig a.val).1).card ((layerTailDegree m + 2) * (rowSets (ig a.val).1).card) ≤
        Fintype.card (B ⟨(ig a.val).1, Sum.inr (ig a.val).2⟩)) :
    ∃ K : ℕ, 2 ≤ K ∧
      ∃ witnesses : (t : Fin M₀) → (r : AllocatedPositiveResidue (dim := dim) B U b S (period t)) →
        AllocatedResidueSiteWitness (dim := dim) B U b S (period t) r.val,
      (∀ t r, allocatedActiveSiteBounds B U b S rowSets P pointTolerance Λ M (witnesses t r).expansion) ∧ ∀
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Q : Fin m → Type uQ} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d]
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hCexp : ∀ j, (C j : ℝ) ≤ Real.exp p₁) (_hVexp : ∀ j, (V j : ℝ) ≤ Real.exp p₁)
    (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp p₁) (_hσ1 : ∀ j, σ j ≤ 1)
    (Qsite : ℝ≥0) (_hQsite : ∀ a : activeAxes, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (ig a.val).1 (ig a.val).2) : ℝ) + 1) ≤ Qsite)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, R j ≤ allocatedIdealCoverRadius (G := G) B rowSets Cinv j),
    ∃ g : (t : Fin M₀) → (r : AllocatedPositiveResidue (dim := dim) B U b S (period t)) →
        (∀ a, ((witnesses t r).expansion a).Term) → Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ),
      (∀ t r k s, LipschitzWith (max (((Fintype.card activeAxes * siteLip) * Qsite) *
        (Real.toNNReal (Real.exp p₁) * ∑ j, C j * Fintype.card (J j)) * commonSitePeriod (witnesses t r).expansion k)
          (4 * commonSitePeriod (witnesses t r).expansion k)) (g t r k s) ∧ ∀ z, ‖g t r k s z‖ ≤ 1) ∧
      (∀ t r, (∑ k, ‖coverSiteCoefficient (witnesses t r).expansion k‖) ≤
        (2 : ℝ) ^ Fintype.card (Finset (Fin dim)) * ∏ a, (coefficientCap) a) ∧
      (∀ t, allocatedResidueCoverCoefficientMass B U b S (period t) (witnesses t) ≤
        (2 : ℝ) ^ Fintype.card (Finset (Fin dim)) * ∏ a, (coefficientCap) a) ∧
      ∀ (x : G → IntegerScalarCubeBox (Fin dim) S.value)
        (selection : Fin dim ↪ G) {κ : ℝ}
        (_hx : GoodScalarKernelTuple selection κ M₀ x),
      ∃ t : Fin M₀,
        (∀ root : G → ℤ, integerScalarLattice (Unit ⊕ Fin dim) (period t : ℤ) ≤
          pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
            (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection)) ∧
        (∀ j, integerScalarLattice (rowTypes j) (period t : ℤ) ≤
          (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range) ∧
      ∀ (τ : ℝ≥0), 0 < τ → τ ≤ 1 → (τ : ℝ)⁻¹ ≤ Real.exp e → ∀
    {X : Type uX} [Fintype X] [DecidableEq X]
    {P₀ : ℝ} (_hP : 0 ≤ P₀) (_hn : (Fintype.card X : ℝ) ≤ P₀)
    (_hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P₀)
    (_hbudget : allocatedSiteErrorFourierOutput m p₁ w (allocatedIdealProfileLog m p₁ e) ≤ P₀)
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
    let f := allocatedPhysicalLongIdeal B U b hR S rowSets τ
    let law := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let error := fun z : Option (Fin dim) × X → ℤ =>
      law.complexMean (fun y₀ =>
        (allocatedWholeMaskedCoveredProfile (O := rowTypes) B U b hR hσ S x (rows) hb o bW d y₀ (period t) f
          (physicalCubeRowSample U d (rows) p hmp (standardPhysicalCubeOutput z)) : ℂ)) -
      (law.fiberLaw (principalResidueLabel (period t))).complexMean
        (allocatedSupportedIdealCoverValue B U b hR hσ S (period t) (witnesses t) hb o bW d (g t) τ x p hmp
          (standardPhysicalCubeOutput z))
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells W z,
      selectedResidueDensityMass stride cells W (fun z => ‖error z‖) ≤ Real.exp (-E) ∧
      ∀ φ : (Option (Fin dim) × X → ℤ) → ℂ, (∀ z, ‖φ z‖ ≤ 1) →
        ‖∑' z, ((selectedResidueSmoothPMF stride cells W hW hZ z).toReal : ℂ) *
          (error z * φ z)‖ ≤ Real.exp (-E) := by
  have hp₁ := (canonicalScalarSourceLog_bounds m hp₀).1.trans hSourceLog
  have hM₀ := hcutoff.trans (Real.exp_le_exp.mpr
    ((canonicalScalarSourceLog_bounds m hp₀).2.trans hSourceLog))
  have hPp := (canonicalScalarSourceEnvelope_le_exp m hp₀ hcutoff).trans
    (Real.exp_le_exp.mpr hSourceLog)
  obtain ⟨hP, hcP, hsources⟩ := canonicalScalarSourceEnvelope_bounds m M₀
  have hsP := hsources dim hdimSmall
  have hL := scalarSourceTransitionBound_spec.2
  have hv := allocatedIdealProfileLog_nonneg m hp₁ he
  have hδ := allocatedSitePrimitiveTolerance_pos m p₁ w (allocatedIdealProfileLog m p₁ e) E
  have hΛ := (allocatedSiteSpectrumLog_bounds m hp₁ hw hv hE).2.2.2.1
  have hspec := allocatedSiteSpectrum_primitive_budget B rowSets
    (by simpa only [Fintype.card_fin] using hdimSmall) hp₁ hw hv hE hP hPp hvars hI hn₁
  obtain ⟨K, hK, hSampling⟩ :=
    exists_allocated_boolean_rows_sampling.{uX,uJ,uG,uI,uB,uQ} m dim
  have hsizeFamily (t : Fin M₀) : (Fintype.card (Fin dim) + 1) * period t ≤ S.value :=
    (Nat.mul_le_mul_left _ (kernelPeriodCandidate_le (m + 1) t)).trans hsize
  have hsourceFamily (t : Fin M₀) :
      scalarCubePrimitiveEnvelope (Fin dim) L 1 0 (period t) ≤ P := by
    have hperiodSize : (period t : ℝ) ≤ (M₀ ^ (m + 1) : ℕ) := by
      exact_mod_cast kernelPeriodCandidate_le (m + 1) t
    have hcap := paddedResidueDensityCap_mono (Fin dim) (kernelPeriodCandidate_le (m + 1) t)
    dsimp only [scalarCubePrimitiveEnvelope] at hsP ⊢
    linarith only [hsP, hperiodSize, hcap]
  have hex (t : Fin M₀) := exists_allocated_residue_site_sampling.{uG,uI,uB,uJ,uQ,uX}
    B U b hR hσ S (period t) (kernelPeriodCandidate_pos (m + 1) t) (hsizeFamily t)
    P δ Λ M hP hδ hΛ hgamma L hL hcP (hsourceFamily t) hM hB
    (fun a => (hspec (ig a.val)).1)
    (fun a => (hspec (ig a.val)).2.1)
    (fun a => (hspec (ig a.val)).2.2)
  choose witnesses hBounds hWitnesses using hex
  refine ⟨K, hK, witnesses, hBounds, ?_⟩
  intro hb o Q _ bW d _ _ C V hC hV hCexp hVexp hRi hσ1 Qsite hQsite Cinv hCinv hchart hsmall
  have hBounds' := hBounds
  dsimp only [allocatedActiveSiteBounds] at hBounds'
  have hcover (t : Fin M₀) := exists_allocated_ideal_cover_error B U b hR hσ S (period t)
    δ (witnesses t) (hWitnesses t) hp₁ hw he hE hdimSmall hvars hI hn₁ hJ
    M₀ (kernelPeriodCandidate_le (m + 1) t) hM₀ hS₁ (le_refl _) hEbudget (hBounds' t)
    (K := K) (@hSampling (fun j => Finset.Subtype.fintype (rowSets j)))
    hb o bW d C V hC hV hCexp hVexp hRi hσ1 Qsite hQsite Cinv hCinv hchart hsmall
  choose g hg hc hmass hcomparison using hcover
  refine ⟨g, hg, hc, hmass, ?_⟩
  intro x selection κ hx
  have hrows : ∀ j (z : rowTypes j), z.val.card ≤ j.val + 1 :=
    fun j z => (mem_boundedBooleanJetRows (j.val + 1) z.val).mp z.property
  obtain ⟨t, hspatial, hperiod⟩ := goodKernel_periodFamily selection x hx (m + 1) (by omega)
    (fun j : Fin m => j.val + 1) (fun j => by omega) rows
    (fun _ => Subtype.val_injective) hrows
  refine ⟨t, hspatial, hperiod, ?_⟩
  have hMpos : 0 < M₀ := by
    obtain ⟨a, ha, haM, _⟩ := hx.2
    exact ha.trans_le haM
  intro τ hτ hτ1 hτe
  refine @hcomparison t τ hτ hτ1 hτe x ?_ hperiod
  intro y₀ j z
  have hbound := allocatedIntegerKernelMask_bound B U b S x rows hMpos selection hx
    (by simpa only [Fintype.card_fin] using hdimSmall)
    (fun _ => Subtype.val_injective) hrows j (period t)
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict grid y₀) rows j
      (principalAxisRestrict (fun a => ¬grid a) y₀)) (period t)) z
  exact ⟨hbound.1, hbound.2.trans
    ((layerKernelIndexBound_le_exp m hcutoff).trans (Real.exp_le_exp.mpr hmaskBudget))⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq
attribute [local instance] ScalarSiteExpansion.termFinite

variable {m dim : ℕ} {G : Type uG} [Fintype G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {p e E : ℝ}
local notation "S" => allocatedSiteScale (G := G) B U b hR hσ p e E
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

variable (M₀ : ℕ)
local notation "period" => kernelPeriodCandidate (m + 1)
local notation "P" => canonicalScalarSourceEnvelope m M₀
local notation "L" => scalarSourceTransitionBound

local notation "sourceParameter" => allocatedSiteSourceLog m p e E
local notation "maskLog" => allocatedSiteKernelMaskLog m p
local notation "δ" => allocatedSitePrimitiveTolerance m sourceParameter maskLog (allocatedIdealProfileLog m sourceParameter e) E
local notation "Λ" => allocatedSiteSpectrumLog m sourceParameter maskLog (allocatedIdealProfileLog m sourceParameter e) E
local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "active" => allocatedActiveGrid B U b S
local notation "activeAxes" => {a : {a // grid a} // active a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "axisN" => allocatedGridNaturalScale B U b S

local notation "sitePeriods" => (fun a : activeAxes =>
  (allocatedPositiveSitePeriod B (Fin dim) U b hR S (Subtype.val a) : ℕ))

local notation "pointTolerance" => allocatedSitePointTolerance (G := G) B rowSets δ
local notation "torus" => (fun a : activeAxes => allocatedGridTorusFactor B (Fin dim) (ig (Subtype.val a)))
local notation "siteLip" => (NNReal.mk (Real.exp (1 + 6 * Λ + 12)) (Real.exp_nonneg _) + 4 : ℝ≥0)
local notation "coefficientCap" => (fun a : activeAxes =>
  allocatedGridPointCap B P (ig (Subtype.val a)) (rowSets (Sigma.fst (ig (Subtype.val a)))) *
    Real.exp (Fintype.card (Finset (Fin dim)) * (4 * Λ + 8) + Λ))

theorem exists_scaled_good_kernel_ideal_cover_family
    (hp : 0 ≤ p) (he : 0 ≤ e) (hE : 0 ≤ E)
    (hdimSmall : dim ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn₁ : ∀ j, (n j : ℝ) ≤ p)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (hcutoff : (M₀ : ℝ) ≤ Real.exp p)
    (hRi₀ : ∀ j, (R j)⁻¹ ≤ Real.exp p)
    (hσi₀ : ∀ j, (σ j)⁻¹ ≤ Real.exp p)
    (hR1 : ∀ j, R j ≤ 1)
    (hBlocks : ∀ j i, siteSpectrumBlockCount m ≤ Fintype.card (B ⟨j, Sum.inr i⟩)) :
    ∃ K : ℕ, 2 ≤ K ∧
      ∃ witnesses : (t : Fin M₀) → (r : AllocatedPositiveResidue (dim := dim) B U b S (period t)) →
        AllocatedResidueSiteWitness (dim := dim) B U b S (period t) r.val,
      (∀ t r, allocatedActiveSiteBounds B U b S rowSets P pointTolerance Λ sitePeriods (witnesses t r).expansion) ∧ ∀
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Q : Fin m → Type uQ} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d]
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hCexp : ∀ j, (C j : ℝ) ≤ Real.exp sourceParameter) (_hVexp : ∀ j, (V j : ℝ) ≤ Real.exp sourceParameter)
    (_hσ1 : ∀ j, σ j ≤ 1)
    (Qsite : ℝ≥0) (_hQsite : ∀ a : activeAxes, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (ig a.val).1 (ig a.val).2) : ℝ) + 1) ≤ Qsite)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, R j ≤ allocatedIdealCoverRadius (G := G) B rowSets Cinv j),
    ∃ g : (t : Fin M₀) → (r : AllocatedPositiveResidue (dim := dim) B U b S (period t)) →
        (∀ a, ((witnesses t r).expansion a).Term) → Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ),
      (∀ t r k s, LipschitzWith (max (((Fintype.card activeAxes * siteLip) * Qsite) *
        (Real.toNNReal (Real.exp sourceParameter) * ∑ j, C j * Fintype.card (J j)) * commonSitePeriod (witnesses t r).expansion k)
          (4 * commonSitePeriod (witnesses t r).expansion k)) (g t r k s) ∧ ∀ z, ‖g t r k s z‖ ≤ 1) ∧
      (∀ t r, (∑ k, ‖coverSiteCoefficient (witnesses t r).expansion k‖) ≤
        (2 : ℝ) ^ Fintype.card (Finset (Fin dim)) * ∏ a, (coefficientCap) a) ∧
      (∀ t, allocatedResidueCoverCoefficientMass B U b S (period t) (witnesses t) ≤
        (2 : ℝ) ^ Fintype.card (Finset (Fin dim)) * ∏ a, (coefficientCap) a) ∧
      ∀ (x : G → IntegerScalarCubeBox (Fin dim) (LayerSamplerScale.value S))
        (selection : Fin dim ↪ G) {κ : ℝ}
        (_hx : GoodScalarKernelTuple selection κ M₀ x),
      ∃ t : Fin M₀,
        (∀ root : G → ℤ, integerScalarLattice (Unit ⊕ Fin dim) (period t : ℤ) ≤
          pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
            (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection)) ∧
        (∀ j, integerScalarLattice (rowTypes j) (period t : ℤ) ≤
          (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range) ∧
      ∀ (τ : ℝ≥0), 0 < τ → τ ≤ 1 → (τ : ℝ)⁻¹ ≤ Real.exp e → ∀
    {X : Type uX} [Fintype X] [DecidableEq X]
    {P₀ : ℝ} (_hP : 0 ≤ P₀) (_hn : (Fintype.card X : ℝ) ≤ P₀)
    (_hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P₀)
    (_hbudget : allocatedSiteErrorFourierOutput m sourceParameter maskLog (allocatedIdealProfileLog m sourceParameter e) ≤ P₀)
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
    let f := allocatedPhysicalLongIdeal B U b hR S rowSets τ
    let law := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let error := fun z : Option (Fin dim) × X → ℤ =>
      law.complexMean (fun y₀ =>
        (allocatedWholeMaskedCoveredProfile (O := rowTypes) B U b hR hσ S x (rows) hb o bW d y₀ (period t) f
          (physicalCubeRowSample U d (rows) p hmp (standardPhysicalCubeOutput z)) : ℂ)) -
      (law.fiberLaw (principalResidueLabel (period t))).complexMean
        (allocatedSupportedIdealCoverValue B U b hR hσ S (period t) (witnesses t) hb o bW d (g t) τ x p hmp
          (standardPhysicalCubeOutput z))
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells W z,
      selectedResidueDensityMass stride cells W (fun z => ‖error z‖) ≤ Real.exp (-E) ∧
      ∀ φ : (Option (Fin dim) × X → ℤ) → ℂ, (∀ z, ‖φ z‖ ≤ 1) →
        ‖∑' z, ((selectedResidueSmoothPMF stride cells W hW hZ z).toReal : ℂ) *
          (error z * φ z)‖ ≤ Real.exp (-E) := by
  obtain ⟨_, _, hpSource, hEbudget, hCSource, hScaleSource⟩ :=
    allocatedSiteSourceLog_bounds m hp he hE
  have hw := allocatedSiteKernelMaskLog_nonneg m hp
  have hrowdim : Fintype.card (Fin dim) ≤ m + 1 := by
    simpa only [Fintype.card_fin] using hdimSmall
  have hscale := allocatedSiteScale_upper (G := G) B U b hR hσ rows hrowdim
    (fun _ => Subtype.val_injective) hp he hE hvars hI hn₁ hRi₀ hσi₀
  have hsize := allocatedSiteScale_period_window (G := G) B U b hR hσ hdimSmall hp he hE hcutoff
  have hblocks := allocatedUniformBlocks_spectrum_bound B rowSets hrowdim hBlocks
  have hgamma (a : activeAxes) : principalProfileSize (R (ig a.val).1)
      (Finset.card (layerIntegerPrincipalSlots (G := G) B (ig a.val).1 (ig a.val).2)) ≤ (LayerSamplerScale.value S) :=
    principalProfileSize_le_natScale (hR _).le (hR1 _) _ (LayerSamplerScale.value S) (LayerSamplerScale.positive S)
  obtain ⟨K, hK, witnesses, hBounds, hgeometry⟩ := exists_cutoff_mask_good_kernel_ideal_cover_family
    (B := B) (U := U) (b := b) (hR := hR) (hσ := hσ) («S» := S) (M₀ := M₀)
    (hsize := hsize) (M := sitePeriods) (p₀ := p) (p₁ := sourceParameter) (w := maskLog)
    hw he hE hdimSmall (hvars.trans hpSource) (fun j => (hI j).trans hpSource)
    (fun j => (hn₁ j).trans hpSource) (fun j => (hJ j).trans hpSource)
    hp hcutoff hCSource le_rfl (hscale.trans (Real.exp_le_exp.mpr hScaleSource))
    hEbudget hgamma (fun _ => rfl) (fun a => hblocks (ig a.val))
  refine ⟨K, hK, witnesses, hBounds, ?_⟩
  intro hb o Q _ bW d _ _ C V hC hV hCexp hVexp hσ1 Qsite hQsite Cinv hCinv hchart hsmall
  exact hgeometry hb o bW d C V hC hV hCexp hVexp
    (fun j => (hRi₀ j).trans (Real.exp_le_exp.mpr hpSource))
    hσ1 Qsite hQsite Cinv hCinv hchart hsmall

end Erdos3.VectorPolynomial

end

end OAI
