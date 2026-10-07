import OAI.Combinatorics.Progressions.Estimates.AllocatedFixedCommonCover

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq
attribute [local instance] ScalarSiteExpansion.termFinite

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

local notation "activeAxes" => {a : {a // allocatedGridAxis (I := I) U b S.value a} //
  allocatedActiveGrid B U b S a}
local notation "ig" => allocatedGridIntegerAxis B U b S

def AllocatedGenuineKernelData (Psp E e pNum Pbase Qraw p₁ : ℝ) (hP : 0 ≤ Psp)
    (δ : ℝ≥0) (A Kraw Ksite : ℕ)
    (witnesses : (q : AllocatedRefinedPeriodIndex m Psp) →
      (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
      AllocatedResidueSiteWitness (dim := dim) B U b S (q.val : ℕ) r.val)
    (L : ℝ≥0) (Cc : activeAxes → ℝ) : Prop :=
  let w := allocatedSiteKernelMaskLog m Psp
  let v := allocatedIdealProfileLog m p₁ e
  let Pfinal := sourceCoverParameter dim Kraw Psp pNum Qraw
    (allocatedSiteErrorFourierOutput m p₁ w v)
    (allocatedOriginalGeometryLog m Psp p₁ w v (E + 1))
  ∀ {Mk : ℕ} (hMk : 0 < Mk) (selection : Fin dim ↪ G)
    (_hqDim : dim ≤ m + 1) (hMkPsp : (Mk : ℝ) ≤ Real.exp Psp),
  let Kernel := G → IntegerScalarCubeBox (Fin dim) S.value
  let Good := GoodScalarKernelTuple (L := S.value) selection (1 / (Mk : ℝ)) Mk
  let GoodKernel := {x : Kernel // Good x}
  ∃ (d : GoodKernel → ℕ) (hd : ∀ x, 0 < d x),
    let : ∀ x, NeZero (d x) := fun x => ⟨(hd x).ne'⟩
    (∀ x, (d x : ℝ) ≤ Real.exp ((Pbase + A) ^ A)) ∧
  ∃ (modulus : GoodKernel → ℕ) (hmodulus : ∀ x, 0 < modulus x),
    let : ∀ x, NeZero (modulus x) := fun x => ⟨(hmodulus x).ne'⟩
    ∃ hmodulusSize : ∀ x, modulus x ≤ Mk ^ (m + 1),
    (∀ (x : GoodKernel) (root : G → ℤ), integerScalarLattice (Unit ⊕ Fin dim) (modulus x : ℤ) ≤
      pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x.val) selection)
        (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x.val) selection)) ∧
    (∀ (x : GoodKernel) j, integerScalarLattice (jets j) (modulus x : ℤ) ≤
      (scalarKernelIntegerJet x.val (j.val + 1) (jetRows j)).mulVecLin.range) ∧
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
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B (Fin dim) Cinv 1 j)
    (Qsite : ℝ≥0)
    (_hQsite : ∀ a : activeAxes, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (ig a.val).1 (ig a.val).2) : ℝ) + 1) ≤ Qsite)
    (Kcap : ℝ≥0) (_hKcap : ∀ j, (R j)⁻¹ ≤ Kcap) (_hσ1 : ∀ j, σ j ≤ 1)
    (_hcoverSmall : ∀ j, R j ≤ allocatedIdealCoverRadius (G := G) B rowSets Cinv j),
    ∃ g : (x : GoodKernel) → (q : AllocatedRefinedPeriodIndex m Psp) →
        (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
        (∀ a, ((witnesses q r).expansion a).Term) →
        Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ),
      (∀ x q r k s, LipschitzWith (max (((Fintype.card activeAxes * L) * Qsite) *
        (Kcap * ∑ j, C j * Fintype.card (J j)) * commonSitePeriod (witnesses q r).expansion k)
          (4 * commonSitePeriod (witnesses q r).expansion k)) (g x q r k s) ∧
        ∀ z, ‖g x q r k s z‖ ≤ 1) ∧
      (∀ (_x : GoodKernel) q r, (∑ k, ‖coverSiteCoefficient (witnesses q r).expansion k‖) ≤
        (2 : ℝ) ^ Fintype.card (Finset (Fin dim)) * ∏ a, Cc a) ∧
      (∀ (_x : GoodKernel) q, allocatedResidueCoverCoefficientMass B U b S (q.val : ℕ) (witnesses q) ≤
        (2 : ℝ) ^ Fintype.card (Finset (Fin dim)) * ∏ a, Cc a) ∧
    ∀
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
    let refined := fun x => residueRefinedPeriod (modulus x) q
    let index := fun x => allocatedRefinedPeriodIndex m hP hMkPsp
      (hmodulusSize x)
      hXPsp (hmodulus x) q hq hqPsp
    let : ∀ x, NeZero (refined x) := fun x => ⟨(residueRefinedPeriod_pos (hmodulus x) q hq).ne'⟩
    let W := allocatedPhysicalRootBudget B U b S (fun _ => 0)
    let hW := allocatedPhysicalRootBudget_nonneg B U b S (fun _ => 0)
    let indices := PrincipalTupleIndex B (layerSamplerDegree I n)
    let ξ := normalizedTupleNarrowWidth X indices selection Mk Psp ((E + 1) + 2)
    let hξ := normalizedTupleNarrowWidth_pos X indices selection Mk Psp ((E + 1) + 2)
    let sourceMesh := normalizedTupleRadius X selection Mk Psp ((E + 1) + 2) W / 4
    let mesh := min sourceMesh (allocatedOriginalCoverMesh m Psp p₁ w v (E + 1))
    ∀ {τ : ℝ} (hτ : 0 < τ) (_hτP : 1 / τ ≤ Real.exp pNum)
    (N : X → ℕ) (hN : ∀ t, 0 < N t)
    (_hsize : ∀ t, Real.exp ((Pfinal + Ksite) ^ Ksite) ≤ (N t : ℝ))
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
    {rank : ℝ}
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) rank (U j) (poly j))
    (_hRank : Real.exp ((Pfinal + Ksite) ^ Ksite) ≤ rank)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
    (_hcells : cells.Nonempty)
    (test : Finset (Fin dim) → (X → ℝ) → ℂ) (_htest : ∀ site v, ‖test site v‖ ≤ 1)
    (bases : Finset (X → ℤ)) (_hbases : bases.Nonempty),
    let V₀ := narrowTrimmedSpatialWidths (G := G) (J := indices) W τ ξ N
    let Z := selectedJointDensityMass bases q cells V₀
      (allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem)
    ∀ (_hZ : 1 / 2 ≤ Z),
    let H := trimmedSpatialRootScale τ N q
    let law := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let coverValue := fun (x : GoodKernel) input r =>
      allocatedSupportedIdealCoverValue B U b hR hσ S (refined x) (witnesses (index x))
        hb o bW (d x) (g x (index x)) δ x.val poly hmem input r
    let wholeReference := fun x => allocatedSupportedWholeReference (dim := dim) B U b S (refined x)
    let reconstruct := fun (x : GoodKernel) base =>
      allocatedWholeResidueReconstruction B U b S X (modulus x) q (wholeReference x) x.val base
    let weight := fun (x : GoodKernel) base =>
      allocatedRecenteredResidueWeight (τ := τ) B U b S X (modulus x) q (wholeReference x) x.val hMk selection x.property
        N hW mesh base cells (physicalCubeSiteTest test)
    let cover := fun (x : GoodKernel) base =>
      (law.fiberLaw (principalResidueLabel (refined x))).complexMean (fun r =>
        ∑ a : cells, (selectedResidueCellWeight q cells V₀ a : ℂ) *
          ∑ z ∈ spatialWindow H 4, weight x base r a z * coverValue x (reconstruct x base r a.val z) r) / (Z : ℂ)
    ∃ hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells V₀ z,
    ∀ (kernelLaw : FiniteProbabilityWeights Kernel) {η : ℝ},
    kernelLaw.eventProbability (fun x => ¬Good x) ≤ η →
    ‖kernelLaw.complexMean (fun x => 𝔼 base ∈ bases,
        allocatedOriginalTupleSource B U b hR hσ S x X q hb o N hN hW hτ hξ base cells hmass
          (physicalCubeSiteTest test) Z poly hmem) -
      kernelLaw.goodPartBaseMean bases Good (fun x hx base => cover ⟨x, hx⟩ base)‖ ≤ Real.exp (-E) + η

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq
attribute [local instance] ScalarSiteExpansion.termFinite

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

local notation "activeAxes" => {a : {a // allocatedGridAxis (I := I) U b S.value a} //
  allocatedActiveGrid B U b S a}
local notation "ig" => allocatedGridIntegerAxis B U b S

theorem allocatedGenuineKernelData_of_cover
    {Psp E e pNum Pbase Qraw p₁ : ℝ} (hP : 0 ≤ Psp)
    {δ : ℝ≥0} {A Kraw Ksite : ℕ}
    (witnesses : (q : AllocatedRefinedPeriodIndex m Psp) →
      (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
      AllocatedResidueSiteWitness (dim := dim) B U b S (q.val : ℕ) r.val)
    {L : ℝ≥0} {Cc : activeAxes → ℝ}
    (hcover : AllocatedGenuineCoverData.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ S Psp E e pNum Pbase Qraw p₁ hP δ A Kraw Ksite witnesses L Cc) :
    AllocatedGenuineKernelData.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ S Psp E e pNum Pbase Qraw p₁ hP δ A Kraw Ksite witnesses L Cc := by
  unfold AllocatedGenuineKernelData
  intro w v Pfinal Mk hMk selection hqDim hMkPsp Kernel Good GoodKernel
  have hstart (x : GoodKernel) := hcover x.val hMk selection x.property hqDim hMkPsp
  choose d hd hdb hstep using hstart
  let : ∀ x, NeZero (d x) := fun x => ⟨(hd x).ne'⟩
  have hperiod (x : GoodKernel) := goodKernel_common_period selection x.val x.property
    (m + 1) (by omega) (fun j : Fin m => j.val + 1) (fun j => by omega)
    jetRows (fun _ => Subtype.val_injective) (fun _ a => a.property)
  choose modulus hmodulus hmodulusSize hspatial hcoefficient using hperiod
  let : ∀ x, NeZero (modulus x) := fun x => ⟨(hmodulus x).ne'⟩
  refine ⟨d, hd, hdb, modulus, hmodulus, hmodulusSize, hspatial, hcoefficient, ?_⟩
  have hsteps (x : GoodKernel) := hstep x (modulus x) (hmodulus x)
    (hmodulusSize x) (hspatial x) (hcoefficient x)
  choose pivots hA hinverse hfamily using hsteps
  intro block _ _ _ _ _ _ hb o Kcov _ bW C V hC hV hCp hVp Cinv hCinv hchart hsmall
    Qsite hQsite Kcap hKcap hσ1 hcoverSmall
  have hgfam (x : GoodKernel) := hfamily x block hb o bW C V hC hV hCp hVp
    Cinv hCinv hchart hsmall Qsite hQsite Kcap hKcap hσ1 hcoverSmall
  choose g hg hcoeff hmassCover hcompare using hgfam
  refine ⟨g, hg, hcoeff, hmassCover, ?_⟩
  intro μ _ _ ν _ _ _ _ _ μsmall _ _ X _ _ hXPsp q hq hqPsp refined index _
    W hW indices ξ hξ sourceMesh mesh τ hτ hτP N hN hsizeN poly hpoly hmem
    rank hrank hRank cells hcells test htest bases hbases V₀ Z hZ H law
    coverValue wholeReference reconstruct weight cover
  have hZpos : 0 < Z := lt_of_lt_of_le (by norm_num) hZ
  have hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells V₀ z :=
    selectedJointDensityMass_smooth_mass_pos bases q cells V₀
      (allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem) hZpos
  refine ⟨hmass, ?_⟩
  intro kernelLaw η hbad
  have hpoint (x : GoodKernel) (base : X → ℤ) :
      ‖allocatedOriginalTupleSource B U b hR hσ S x.val X q hb o N hN hW hτ hξ base cells hmass
          (physicalCubeSiteTest test) Z poly hmem - cover x base‖ ≤ Real.exp (-E) := by
    obtain ⟨hRefined, hdiv, hRefinedBound, hsize, reference, residue, href, hresidue, hlocal⟩ :=
      hcompare x μ ν μsmall hXPsp q hq hqPsp
    obtain ⟨hmass', hestimate⟩ := hlocal hτ hτP N hN hsizeN poly hpoly hmem hrank hRank
      base cells hcells test htest Z hZ
    exact hestimate
  exact allocatedOriginal_kernel_average_of_bad_bound B U b hb o hR hσ S X poly hmem N hN
    hW hτ hξ q cells hmass bases hbases hZpos kernelLaw selection Mk
    (physicalCubeSiteTest test) (physicalCubeSiteTest_norm_le test htest)
    (fun x hx base => cover ⟨x, hx⟩ base) (Real.exp_pos _).le
    (fun x hx base _ => hpoint ⟨x, hx⟩ base) hbad

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

universe uG uI uB uJ uQ uX

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped ContDiff BigOperators Classical NNReal

attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq

variable {m dim : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) (Fin.val j + 1))
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

local notation "hLayer" => layerSamplerDegree I n

def AllocatedCommonGenuineKernelAt (p Psp E e t : ℝ) (hP : 0 ≤ Psp) (δ : ℝ≥0)
    (A T Kproj Kideal Ksite : ℕ) : Prop :=
  ∀ {c : ℝ}, 0 ≤ c →
    ∀ {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j),
    (∀ j, σ j ≤ t) → (∀ j, R j ≤ 1) →
    (∀ j, (R j)⁻¹ ≤ Real.exp c) → (∀ j, (σ j)⁻¹ ≤ Real.exp c) →
    let Eraw := E + 1 + 4
    let Esite := allocatedOriginalCoverAccuracy Psp (E + 1)
    let D := allocatedComparisonDimension m p
    let pNum := allocatedCommonScaleNumeric m p c Psp Eraw
    let S := allocatedCommonScale (G := G) B U b hR hσ p c Psp e Eraw
    let p₁ := allocatedCommonRefinedSourceLog m p c Psp e Eraw Esite
    let w := allocatedSiteKernelMaskLog m Psp
    let v := allocatedIdealProfileLog m p₁ e
    let error := allocatedReferenceIdealError m D Psp Eraw
    let lengthLog := allocatedIdealScaleLog m D pNum e w error
    let gainLog := allocatedProfileGainLog m D Psp w
    let Pbase := allocatedIdealSourceBudget m D pNum e w error
    let lateLog := allocatedSpatialLateLog (G := G) B Pbase Pbase
    let F := allocatedProfileFourierOutput (allocatedActualProfileInput m D pNum e gainLog lengthLog)
    let Λ := allocatedSiteSpectrumLog m p₁ w v Esite
    let L : ℝ≥0 := NNReal.mk (Real.exp (1 + 6 * Λ + 12)) (Real.exp_nonneg _) + 4
    let Cc := fun a : {a : {a // allocatedGridAxis (I := I) U b S.value a} //
        allocatedActiveGrid B U b S a} =>
      allocatedGridPointCap B (canonicalScalarSourceEnvelope m (allocatedRefinedPeriodCutoff m Psp))
        (allocatedGridIntegerAxis B U b S a.val)
        (rowSets (allocatedGridIntegerAxis B U b S a.val).1) *
          Real.exp (Fintype.card (Finset (Fin dim)) * (4 * Λ + 8) + Λ)
    ∃ witnesses : (q : AllocatedRefinedPeriodIndex m Psp) →
        (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
        AllocatedResidueSiteWitness (dim := dim) B U b S (q.val : ℕ) r.val,
      AllocatedPointwiseResidueCoverFamily.{uG,uI,uB,uJ,uQ,uX,0}
        B U b hR hσ S (fun q : AllocatedRefinedPeriodIndex m Psp => (q.val : ℕ)) witnesses L Cc ∧
      AllocatedGenuineKernelData.{uG,uI,uB,uJ,uQ,uX}
        B U b hR hσ S Psp E e pNum Pbase (allocatedSourceSamplingBudget m dim A Pbase (E + 1) lateLog F)
        p₁ hP δ A (max T (max Kproj Kideal)) Ksite witnesses L Cc

theorem allocatedCommonGenuineCoverAt_kernel
    {p P E e t : ℝ} (hP : 0 ≤ P) {δ : ℝ≥0} {A T Kproj Kideal Ksite : ℕ}
    (hcover : AllocatedCommonGenuineCoverAt.{uG,uI,uB,uJ,uQ,uX}
      (G := G) (dim := dim) B p P E e t hP δ A T Kproj Kideal Ksite) :
    AllocatedCommonGenuineKernelAt.{uG,uI,uB,uJ,uQ,uX}
      (G := G) (dim := dim) B p P E e t hP δ A T Kproj Kideal Ksite := by
  unfold AllocatedCommonGenuineKernelAt
  intro c hc J _ U b R σ hR hσ hσt hR1 hRi hσi
  obtain ⟨witnesses, hFamily, hData⟩ := hcover hc U b hR hσ hσt hR1 hRi hσi
  exact ⟨witnesses, hFamily, allocatedGenuineKernelData_of_cover B U b hR hσ _ hP witnesses hData⟩

def AllocatedRegularizedKernelMixture (p P E : ℝ) (hP : 0 ≤ P) (A T : ℝ≥0) (Ksite : ℕ) : Prop :=
  let D := allocatedComparisonDimension m p
  let target := profileReferenceErrorLog P (E + 1 + 4)
  let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * P
  let gainLog := allocatedProfileGainLog m D P w
  let ε := physicalIdealErrorShare target gainLog
  let e := physicalIdealSmoothingLog (B := B) (O := fun a : LayerSamplerAxis I n => jets a.1)
    (α := Fin dim) hLayer A T target gainLog
  let eTail := physicalIdealTailLog (B := B) (O := fun a : LayerSamplerAxis I n => jets a.1)
    (α := Fin dim) G (G × Option (Fin dim)) hLayer A T m target gainLog
  0 ≤ e ∧ 0 ≤ eTail ∧ ∃ Kideal : ℕ, 2 ≤ Kideal ∧
    ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧
      (δ : ℝ) = booleanRegularizationRadius (B := B)
        (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim) hLayer
        (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
        A T (ε / 2) ∧ (δ : ℝ)⁻¹ ≤ Real.exp e ∧
      let t := booleanMassPerturbationScale (B := B)
        (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim)
        ((G × Option (Fin dim)) ⊕ (Σ a, SamplerCoefficientSlot G B hLayer a)) hLayer
        (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
        A T m 1 (ε / 2)
      0 < t ∧ t ≤ 1 ∧ t⁻¹ ≤ Real.exp eTail ∧
        ∃ A₀ T₀ Kproj : ℕ, 2 ≤ A₀ ∧ 2 ≤ T₀ ∧ 2 ≤ Kproj ∧
          AllocatedCommonGenuineKernelAt.{uG,uI,uB,uJ,uQ,uX}
            (G := G) (dim := dim) B p P E e t hP δ A₀ T₀ Kproj Kideal Ksite

theorem allocatedRegularizedCommonCover_kernel
    {p P E : ℝ} (hP : 0 ≤ P) {A T : ℝ≥0} {Ksite : ℕ}
    (hcover : AllocatedRegularizedCommonCover.{uG,uI,uB,uJ,uQ,uX}
      (G := G) (dim := dim) B p P E hP A T Ksite) :
    AllocatedRegularizedKernelMixture.{uG,uI,uB,uJ,uQ,uX}
      (G := G) (dim := dim) B p P E hP A T Ksite := by
  unfold AllocatedRegularizedKernelMixture
  intro D target w gainLog ε e eTail
  obtain ⟨he, heTail, Kideal, hKideal, δ, hδ, hδ1, hδeq, hδe, ht, ht1, hti,
    A₀, T₀, Kproj, hA₀, hT₀, hKproj, hraw, hgenuine⟩ := hcover
  exact ⟨he, heTail, Kideal, hKideal, δ, hδ, hδ1, hδeq, hδe, ht, ht1, hti,
    A₀, T₀, Kproj, hA₀, hT₀, hKproj, allocatedCommonGenuineCoverAt_kernel B hP hgenuine⟩

theorem exists_fixed_regularized_kernel_mixture :
    ∃ A : ℝ≥0, 1 ≤ A ∧ ∀ m dim : ℕ, ∃ Ksite : ℕ, 2 ≤ Ksite ∧
      ∀ {G : Type uG} [Fintype G] [DecidableEq G]
        {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
        (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
        {p P E : ℝ}, 0 ≤ p → ∀ hP : 0 ≤ P, 0 ≤ E →
        dim ≤ m + 1 → ((m + 2 : ℕ) : ℝ) ≤ P → p ≤ P →
        (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p →
        (∀ j, (Fintype.card (I j) : ℝ) ≤ p) → (∀ j, (n j : ℝ) ≤ p) →
        (∀ j i, siteSpectrumBlockCount m ≤ Fintype.card (B ⟨j, Sum.inr i⟩)) →
        AllocatedRegularizedKernelMixture.{uG,uI,uB,uJ,uQ,uX}
          (G := G) (dim := dim) B p P E hP A scalarSourceTransitionBound Ksite := by
  obtain ⟨A, hA, hfixed⟩ := exists_fixed_regularized_common_cover.{uG,uI,uB,uJ,uQ,uX}
  refine ⟨A, hA, ?_⟩
  intro m dim
  obtain ⟨Ksite, hKsite, hfixed⟩ := hfixed m dim
  refine ⟨Ksite, hKsite, ?_⟩
  intro G _ _ I _ n B _ p P E hp hP hE hdim hmP hpP hvars hI hn hBlocks
  exact allocatedRegularizedCommonCover_kernel B hP (hfixed B hp hP hE hdim hmP hpP hvars hI hn hBlocks)

end Erdos3.VectorPolynomial

end

end OAI
