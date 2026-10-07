import OAI.Combinatorics.Progressions.Estimates.AllocatedProductSeparatedRawData

namespace OAI

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

def AllocatedProductKernelData (Psp E e pNum Pbase Qraw pAccuracy pSampling : ℝ) (hP : 0 ≤ Psp)
    (δ : ℝ≥0) (A Kraw Ksite : ℕ)
    (witnesses : (q : AllocatedRefinedPeriodIndex m Psp) →
      (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
      AllocatedFullGridResidueWitness (dim := dim) B U b S (q.val : ℕ) r.val) : Prop :=
  let w := allocatedSiteKernelMaskLog m Psp
  let v := allocatedIdealProfileLog m pAccuracy e
  let Pfinal := sourceCoverParameter dim Kraw Psp pNum Qraw
    (allocatedSiteErrorFourierOutput m pSampling w v)
    (allocatedSeparatedGeometryLog m Psp pAccuracy pSampling w v (E + 1))
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
      allocatedProductFullGridResidueProfile B U b hR hσ S (refined x) x.val hb o bW (d x)
        (witnesses (index x)) δ r (physicalCubeRowSample (O := fun j => (rowSets j : Type))
          U (d x) fullRows poly hmem input)
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

theorem allocatedProductKernelData_of_raw
    {Psp E e pNum Pbase Qraw pAccuracy pSampling : ℝ} (hP : 0 ≤ Psp)
    {δ : ℝ≥0} {A Kraw Ksite : ℕ}
    (witnesses : (q : AllocatedRefinedPeriodIndex m Psp) →
      (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
      AllocatedFullGridResidueWitness (dim := dim) B U b S (q.val : ℕ) r.val)
    (hcover : AllocatedProductSeparatedRawData.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ S Psp E e pNum Pbase Qraw pAccuracy pSampling hP δ A Kraw Ksite witnesses) :
    AllocatedProductKernelData.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ S Psp E e pNum Pbase Qraw pAccuracy pSampling hP δ A Kraw Ksite witnesses := by
  unfold AllocatedProductKernelData
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
  intro block _ _ _ _ _ _ hb o Kcov _ bW C V hC hV hCp hVp hCpAccuracy hVpAccuracy Cinv hCinv hchart hsmall
    hσ1 hproductSmall μ _ _ ν _ _ _ _ _ μsmall _ _ X _ _ hXPsp q hq hqPsp refined index _
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
      hfamily x block hb o bW C V hC hV hCp hVp hCpAccuracy hVpAccuracy
        Cinv hCinv hchart hsmall hσ1 hproductSmall μ ν μsmall hXPsp q hq hqPsp
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

def AllocatedProductNormalizedKernelData (Psp E e pNum Pbase Qraw pAccuracy pSampling : ℝ) (hP : 0 ≤ Psp)
    (δ : ℝ≥0) (A Kraw Ksite : ℕ)
    (witnesses : (q : AllocatedRefinedPeriodIndex m Psp) →
      (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
      AllocatedFullGridResidueWitness (dim := dim) B U b S (q.val : ℕ) r.val) : Prop :=
  let w := allocatedSiteKernelMaskLog m Psp
  let v := allocatedIdealProfileLog m pAccuracy e
  let Pfinal := sourceCoverParameter dim Kraw Psp pNum Qraw
    (allocatedSiteErrorFourierOutput m pSampling w v)
    (allocatedSeparatedGeometryLog m Psp pAccuracy pSampling w v (E + 1))
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
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
    (_hcells : cells.Nonempty)
    (test : Finset (Fin dim) → (X → ℝ) → ℂ) (_htest : ∀ site v, ‖test site v‖ ≤ 1)
    (bases : Finset (X → ℤ)) (_hbases : bases.Nonempty),
    let V₀ := narrowTrimmedSpatialWidths (G := G) (J := indices) W τ ξ N
    let Z := selectedJointDensityMass bases q cells V₀
      (allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem)
    let H := trimmedSpatialRootScale τ N q
    let law := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let coverValue := fun (x : GoodKernel) input r =>
      allocatedProductFullGridResidueProfile B U b hR hσ S (refined x) x.val hb o bW (d x)
        (witnesses (index x)) δ r (physicalCubeRowSample (O := fun j => (rowSets j : Type))
          U (d x) fullRows poly hmem input)
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
    (|Z - 1| ≤ Real.exp (-Qraw) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z ∧ Z⁻¹ ≤ 2) ∧
    ∀ (kernelLaw : FiniteProbabilityWeights Kernel) {η : ℝ},
    kernelLaw.eventProbability (fun x => ¬Good x) ≤ η →
    ‖kernelLaw.complexMean (fun x => 𝔼 base ∈ bases,
        allocatedOriginalTupleSource B U b hR hσ S x X q hb o N hN hW hτ hξ base cells hmass
          (physicalCubeSiteTest test) Z poly hmem) -
      kernelLaw.goodPartBaseMean bases Good (fun x hx base => cover ⟨x, hx⟩ base)‖ ≤ Real.exp (-E) + η

theorem allocatedProductKernelData_normalized
    {Psp E e pNum Pbase pAccuracy pSampling l F : ℝ} (hP : 0 ≤ Psp) (hE : 0 ≤ E)
    (hPbase : Psp ≤ Pbase) (hpNum : pNum ≤ Pbase)
    (hm : ((m + 1 : ℕ) : ℝ) ≤ Psp) (hdim : ((dim + 1 : ℕ) : ℝ) ≤ Psp)
    (hG : (Fintype.card G : ℝ) ≤ Psp) (hl : Pbase ≤ l) (hF : 0 ≤ F)
    (hnum : ∀ (_o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
      (C V : Fin m → ℝ≥0), (∀ j, (C j : ℝ) ≤ Real.exp pNum) →
      (∀ j, (V j : ℝ) ≤ Real.exp pNum) → AllocatedSourceNumerics B U b S C V Pbase)
    {δ : ℝ≥0} {A Kraw Ksite Knorm : ℕ}
    (hKraw : 1 ≤ Kraw) (hKsite : 1 ≤ Ksite) (hKnorm : 1 ≤ Knorm)
    (hnorm : AllocatedSourceNarrowNormalization.{uG,uI,uB,uJ,uX} m Knorm)
    (witnesses : (q : AllocatedRefinedPeriodIndex m Psp) →
      (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
      AllocatedFullGridResidueWitness (dim := dim) B U b S (q.val : ℕ) r.val) :
    let Qraw := allocatedSourceSamplingBudget m dim A Pbase (E + 1) l F
    AllocatedProductKernelData.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ S Psp E e pNum Pbase Qraw pAccuracy pSampling hP δ A Kraw Ksite witnesses →
    AllocatedProductNormalizedKernelData.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ S Psp E e pNum Pbase Qraw pAccuracy pSampling hP δ A Kraw (max Ksite Knorm) witnesses := by
  intro Qraw hKernel
  have hPbase0 : 0 ≤ Pbase := hP.trans hPbase
  have hEsource : 0 ≤ E + 1 := by linarith
  have hQraw1 : 1 ≤ Qraw :=
    (allocatedSourceSamplingBudget_bounds m dim A hPbase0 hEsource (hPbase0.trans hl) hF).1
  have hQraw0 : 0 ≤ Qraw := zero_le_one.trans hQraw1
  unfold AllocatedProductNormalizedKernelData
  intro w v Pfinal Mk hMk selection hqDim hMkPsp Kernel Good GoodKernel
  have hFinal := sourceCoverParameter_bounds dim Kraw (pNum := pNum) (Qraw := Qraw)
    (F := allocatedSiteErrorFourierOutput m pSampling w v)
    (G := allocatedSeparatedGeometryLog m Psp pAccuracy pSampling w v (E + 1)) hP
  have hFinal0 : 0 ≤ Pfinal := zero_le_one.trans hFinal.1
  have hRawPower : Qraw ≤ (Qraw + Kraw) ^ Kraw := by
    have h := shifted_power_self_mono hQraw0 (le_refl 1) hKraw
    simp only [Nat.cast_one, pow_one] at h
    linarith
  have hRawFinal : Qraw ≤ Pfinal := hRawPower.trans hFinal.2.2.2.2.1
  have hOldCut : Real.exp ((Pfinal + Ksite) ^ Ksite) ≤
      Real.exp ((Pfinal + (max Ksite Knorm : ℕ)) ^ max Ksite Knorm) :=
    Real.exp_le_exp.mpr (shifted_power_self_mono hFinal0 hKsite (le_max_left _ _))
  have hNormCut : Real.exp ((Qraw + Knorm) ^ Knorm) ≤
      Real.exp ((Pfinal + (max Ksite Knorm : ℕ)) ^ max Ksite Knorm) := by
    apply Real.exp_le_exp.mpr
    exact (pow_le_pow_left₀ (add_nonneg hQraw0 (Nat.cast_nonneg _))
      (add_le_add hRawFinal le_rfl) Knorm).trans
      (shifted_power_self_mono hFinal0 hKnorm (le_max_right _ _))
  obtain ⟨d, hd, hdb, modulus, hmodulus, hmodulusSize, hspatial, hcoefficient, hKernel⟩ :=
    hKernel hMk selection hqDim hMkPsp
  let _ : ∀ x, NeZero (d x) := fun x => ⟨(hd x).ne'⟩
  let _ : ∀ x, NeZero (modulus x) := fun x => ⟨(hmodulus x).ne'⟩
  refine ⟨d, hd, hdb, modulus, hmodulus, hmodulusSize, hspatial, hcoefficient, ?_⟩
  intro block _ _ _ _ _ _ hb o Kcov _ bW C V hC hV hCp hVp hCpAccuracy hVpAccuracy Cinv hCinv hchart hsmall
    hσ1 hproductSmall μ _ _ ν _ _ _ _ _ μsmall _ _ X _ _ hXPsp q hq hqPsp refined index _
    W hW indices ξ hξ sourceMesh mesh τ hτ hτP N hN hsizeN poly hpoly hmem
    rank hrank hRank cells hcells test htest bases hbases V₀ Z H law
    coverValue wholeReference reconstruct weight cover
  obtain ⟨_, hnormal⟩ := hnorm B U b S hb o μ ν hR hσ hσ1 C V hC hV Cinv hCinv hchart
    hsmall A (hnum o C V hCp hVp) hP hEsource hPbase hm hdim hG hl hF
    hXPsp selection hMk hMkPsp q hq hqPsp hτ (hτP.trans (Real.exp_le_exp.mpr hpNum))
    N (fun t => hNormCut.trans (hsizeN t)) poly hpoly hmem hrank (hNormCut.trans hRank) cells hcells
  have hZ := hnormal bases hbases
  obtain ⟨hmass, hcomparison⟩ := hKernel block hb o bW C V hC hV hCp hVp hCpAccuracy hVpAccuracy
    Cinv hCinv hchart hsmall hσ1 hproductSmall μ ν μsmall hXPsp q hq hqPsp hτ hτP N hN
    (fun t => hOldCut.trans (hsizeN t)) poly hpoly hmem hrank (hOldCut.trans hRank)
    cells hcells test htest bases hbases hZ.2.1.1
  exact ⟨hmass, hZ, hcomparison⟩

end Erdos3.VectorPolynomial

end

end OAI
