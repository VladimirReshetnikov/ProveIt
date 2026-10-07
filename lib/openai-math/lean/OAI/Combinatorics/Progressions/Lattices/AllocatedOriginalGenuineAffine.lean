import OAI.Combinatorics.Progressions.Lattices.AllocatedProductBoxAffine
import OAI.Combinatorics.Progressions.Linear.AllocatedProductCoarseNormalizedKernel

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

def AllocatedProductCoarseNormalizedAffineData (Psp E e pNum Pbase Qraw pAccuracy pSampling : ℝ) (hP : 0 ≤ Psp)
    (δ : ℝ≥0) (A Kraw Ksite : ℕ)
    (witnesses : (q : AllocatedRefinedPeriodIndex m Psp) →
      (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
      AllocatedFullGridResidueWitness (dim := dim) B U b S (q.val : ℕ) r.val)
    (M Dwin : ℕ) (hM : 0 < M) (hDwin : 0 < Dwin) (η : ℝ) (hη : 0 < η) : Prop :=
  let w := allocatedSiteKernelMaskLog m Psp
  let v := allocatedIdealProfileLog m pAccuracy e
  let Pfinal := sourceCoverParameter dim Kraw Psp pNum Qraw
    (allocatedSiteErrorFourierOutput m pSampling w v)
    (allocatedSeparatedGeometryLog m Psp pAccuracy pSampling w v (E + 2))
  let Mk := scalarKernelCutoff (Fin dim) G M Dwin η
  let hMk := (scalarKernelCutoff_bounds (Fin dim) G hM hDwin hη).1
  ∀ (selection : Fin dim ↪ G) (_hqDim : dim ≤ m + 1)
    (_hcard : dim * (dim + 2) ≤ Fintype.card G) [Nonempty (Fin dim)]
    (hMkPsp : (Mk : ℝ) ≤ Real.exp Psp) (hlarge : Mk ≤ S.value),
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
    let ξ := normalizedTupleNarrowWidth X indices selection Mk Psp ((E + 2) + 2)
    let hξ := normalizedTupleNarrowWidth_pos X indices selection Mk Psp ((E + 2) + 2)
    let mesh := fun x : GoodKernel =>
      allocatedProductCoarseMesh m X selection Mk (modulus x) Psp pAccuracy w v (E + 2)
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
        N hW (mesh x) base cells (physicalCubeSiteTest test)
    let cover := fun (x : GoodKernel) base =>
      (law.fiberLaw (principalResidueLabel (refined x))).complexMean (fun r =>
        ∑ a : cells, (selectedResidueCellWeight q cells V₀ a : ℂ) *
          ∑ z ∈ spatialWindow H 4, weight x base r a z * coverValue x (reconstruct x base r a.val z) r) / (Z : ℂ)
    ∃ hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells V₀ z,
    (|Z - 1| ≤ Real.exp (-Qraw) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z ∧ Z⁻¹ ≤ 2) ∧
    ∀ (window : G → ℕ) (hwindow : ∀ g, window g ≤ S.value)
      (hDwindow : ∀ g, S.value ≤ Dwin * window g)
      (shift : G → ℤ) (moduli : G → Option (Fin dim) → ℕ)
      (residues : ∀ g i, ZMod (moduli g i))
      (hmoduli : ∀ g i, 0 < moduli g i) (hmoduliM : ∀ g i, moduli g i ≤ M),
    let kernelLaw := FiniteProbabilityWeights.pi (fun g =>
      affineScalarCubeWindowWeights (Fin dim) S.value (window g) M Dwin (shift g) S.positive
        (hwindow g) (hDwindow g) (moduli g) (residues g) (hmoduli g) (hmoduliM g)
        (scalarKernelCutoff_window_size (Fin dim) G hM hDwin hη hlarge (hDwindow g)))
    ‖kernelLaw.complexMean (fun x => 𝔼 base ∈ bases,
        allocatedOriginalTupleSource B U b hR hσ S x X q hb o N hN hW hτ hξ base cells hmass
          (physicalCubeSiteTest test) Z poly hmem) -
      kernelLaw.goodPartBaseMean bases Good (fun x hx base => cover ⟨x, hx⟩ base)‖ ≤ Real.exp (-E) + η

theorem allocatedProductCoarseNormalizedAffineData_of_kernel
    {Psp E e pNum Pbase Qraw pAccuracy pSampling : ℝ} (hP : 0 ≤ Psp)
    {δ : ℝ≥0} {A Kraw Ksite : ℕ}
    (witnesses : (q : AllocatedRefinedPeriodIndex m Psp) →
      (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
      AllocatedFullGridResidueWitness (dim := dim) B U b S (q.val : ℕ) r.val)
    (hkernel : AllocatedProductCoarseNormalizedKernelData.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ S Psp E e pNum Pbase Qraw pAccuracy pSampling hP δ A Kraw Ksite witnesses)
    (M Dwin : ℕ) (hM : 0 < M) (hDwin : 0 < Dwin) (η : ℝ) (hη : 0 < η) :
    AllocatedProductCoarseNormalizedAffineData.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ S Psp E e pNum Pbase Qraw pAccuracy pSampling hP δ A Kraw Ksite witnesses
      M Dwin hM hDwin η hη := by
  unfold AllocatedProductCoarseNormalizedAffineData
  intro w v Pfinal Mk hMk selection hqDim hcard _ hMkPsp hlarge Kernel Good GoodKernel
  obtain ⟨d, hd, hdb, modulus, hmodulus, hmodulusSize, hspatial, hcoefficient, hkernel⟩ :=
    hkernel hMk selection hqDim hMkPsp
  let _ : ∀ x, NeZero (d x) := fun x => ⟨(hd x).ne'⟩
  let _ : ∀ x, NeZero (modulus x) := fun x => ⟨(hmodulus x).ne'⟩
  refine ⟨d, hd, hdb, modulus, hmodulus, hmodulusSize, hspatial, hcoefficient, ?_⟩
  intro block _ _ _ _ _ _ hb o Kcov _ bW C V hC hV hCp hVp hCpAccuracy hVpAccuracy Cinv hCinv hchart hsmall
    hσ1 hproductSmall μ _ _ ν _ _ _ _ _ μsmall _ _ X _ _ hXPsp q hq hqPsp refined index _
    W hW indices ξ hξ mesh τ hτ hτP N hN hsizeN poly hpoly hmem
    rank hrank hRank cells hcells test htest bases hbases V₀ Z H law
    coverValue wholeReference reconstruct weight cover
  obtain ⟨hmass, hZ, hcomparison⟩ := hkernel block hb o bW C V hC hV hCp hVp hCpAccuracy hVpAccuracy
    Cinv hCinv hchart hsmall hσ1 hproductSmall μ ν μsmall hXPsp q hq hqPsp hτ hτP N hN hsizeN
    poly hpoly hmem hrank hRank cells hcells test htest bases hbases
  refine ⟨hmass, hZ, ?_⟩
  intro window hwindow hDwindow shift moduli residues hmoduli hmoduliM kernelLaw
  have hbad := affineKernel_explicit_probability_le_of_card_le (Fin dim) G
    (by simpa only [Fintype.card_fin] using hcard) selection hM hDwin hη S.positive hlarge
    window hwindow hDwindow shift moduli residues hmoduli hmoduliM
  exact hcomparison kernelLaw hbad

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

def AllocatedProductCoarseBoxAffineData (Psp E e pNum Pbase Qraw pAccuracy pSampling : ℝ) (hP : 0 ≤ Psp)
    (δ : ℝ≥0) (A Kraw Ksite : ℕ)
    (witnesses : (q : AllocatedRefinedPeriodIndex m Psp) →
      (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
      AllocatedFullGridResidueWitness (dim := dim) B U b S (q.val : ℕ) r.val)
    (M Dwin : ℕ) (hM : 0 < M) (hDwin : 0 < Dwin) (η : ℝ) (hη : 0 < η) : Prop :=
  let w := allocatedSiteKernelMaskLog m Psp
  let v := allocatedIdealProfileLog m pAccuracy e
  let Pfinal := sourceCoverParameter dim Kraw Psp pNum Qraw
    (allocatedSiteErrorFourierOutput m pSampling w v)
    (allocatedSeparatedGeometryLog m Psp pAccuracy pSampling w v (E + 2))
  let Mk := scalarKernelCutoff (Fin dim) G M Dwin η
  let hMk := (scalarKernelCutoff_bounds (Fin dim) G hM hDwin hη).1
  ∀ (selection : Fin dim ↪ G) (_hqDim : dim ≤ m + 1)
    (_hcard : dim * (dim + 2) ≤ Fintype.card G) [Nonempty (Fin dim)]
    (hMkPsp : (Mk : ℝ) ≤ Real.exp Psp) (hlarge : Mk ≤ S.value),
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
    let ξ := normalizedTupleNarrowWidth X indices selection Mk Psp ((E + 2) + 2)
    let hξ := normalizedTupleNarrowWidth_pos X indices selection Mk Psp ((E + 2) + 2)
    let mesh := fun x : GoodKernel =>
      allocatedProductCoarseMesh m X selection Mk (modulus x) Psp pAccuracy w v (E + 2)
    ∀ {τ : ℝ} (hτ : 0 < τ) (_hτP : 1 / τ ≤ Real.exp pNum)
    (_hτ1 : τ ≤ 1 / 2)
    (N : X → ℕ) (hN : ∀ t, 0 < N t)
    (_hsize : ∀ t, Real.exp ((Pfinal + Ksite) ^ Ksite) ≤ (N t : ℝ))
    (_hsizeBox : ∀ t, 4 ≤ τ * (N t : ℝ))
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
    {rank : ℝ}
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) rank (U j) (poly j))
    (_hRank : Real.exp ((Pfinal + Ksite) ^ Ksite) ≤ rank)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
    (_hcells : cells.Nonempty)
    (test : Finset (Fin dim) → (X → ℝ) → ℂ) (_htest : ∀ site v, ‖test site v‖ ≤ 1)
    (bases : Finset (X → ℤ)) (_hbases : bases.Nonempty)
    (_hbaseBox : ∀ base ∈ bases, base ∈ trimmedIntegerBox N (spatialTrimMargin τ N)),
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
        N hW (mesh x) base cells (physicalCubeSiteTest (fun site => integerBoxTestExtension N (test site)))
    let cover := fun (x : GoodKernel) base =>
      (law.fiberLaw (principalResidueLabel (refined x))).complexMean (fun r =>
        ∑ a : cells, (selectedResidueCellWeight q cells V₀ a : ℂ) *
          ∑ z ∈ spatialWindow H 4, weight x base r a z * coverValue x (reconstruct x base r a.val z) r) / (Z : ℂ)
    ∃ hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells V₀ z,
    (|Z - 1| ≤ Real.exp (-Qraw) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z ∧ Z⁻¹ ≤ 2) ∧
    ∀ (window : G → ℕ) (hwindow : ∀ g, window g ≤ S.value)
      (hDwindow : ∀ g, S.value ≤ Dwin * window g)
      (shift : G → ℤ) (moduli : G → Option (Fin dim) → ℕ)
      (residues : ∀ g i, ZMod (moduli g i))
      (hmoduli : ∀ g i, 0 < moduli g i) (hmoduliM : ∀ g i, moduli g i ≤ M),
    let kernelLaw := FiniteProbabilityWeights.pi (fun g =>
      affineScalarCubeWindowWeights (Fin dim) S.value (window g) M Dwin (shift g) S.positive
        (hwindow g) (hDwindow g) (moduli g) (residues g) (hmoduli g) (hmoduliM g)
        (scalarKernelCutoff_window_size (Fin dim) G hM hDwin hη hlarge (hDwindow g)))
    ‖kernelLaw.complexMean (fun x => 𝔼 base ∈ bases,
        allocatedOriginalTupleSource B U b hR hσ S x X q hb o N hN hW hτ hξ base cells hmass
          (physicalCubeSiteTest test) Z poly hmem) -
      kernelLaw.goodPartBaseMean bases Good (fun x hx base => cover ⟨x, hx⟩ base)‖ ≤ Real.exp (-E) + η

theorem allocatedProductCoarseBoxAffineData_of_normalized
    {Psp E e pNum Pbase Qraw pAccuracy pSampling : ℝ} (hP : 0 ≤ Psp)
    {δ : ℝ≥0} {A Kraw Ksite : ℕ}
    (witnesses : (q : AllocatedRefinedPeriodIndex m Psp) →
      (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
      AllocatedFullGridResidueWitness (dim := dim) B U b S (q.val : ℕ) r.val)
    (M Dwin : ℕ) (hM : 0 < M) (hDwin : 0 < Dwin) (η : ℝ) (hη : 0 < η)
    (haffine : AllocatedProductCoarseNormalizedAffineData.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ S Psp E e pNum Pbase Qraw pAccuracy pSampling hP δ A Kraw Ksite witnesses
      M Dwin hM hDwin η hη) :
    AllocatedProductCoarseBoxAffineData.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ S Psp E e pNum Pbase Qraw pAccuracy pSampling hP δ A Kraw Ksite witnesses
      M Dwin hM hDwin η hη := by
  unfold AllocatedProductCoarseBoxAffineData
  intro w v Pfinal Mk hMk selection hqDim hcard _ hMkPsp hlarge Kernel Good GoodKernel
  obtain ⟨d, hd, hdb, modulus, hmodulus, hmodulusSize, hspatial, hcoefficient, haffine⟩ :=
    haffine selection hqDim hcard hMkPsp hlarge
  let _ : ∀ x, NeZero (d x) := fun x => ⟨(hd x).ne'⟩
  let _ : ∀ x, NeZero (modulus x) := fun x => ⟨(hmodulus x).ne'⟩
  refine ⟨d, hd, hdb, modulus, hmodulus, hmodulusSize, hspatial, hcoefficient, ?_⟩
  intro block _ _ _ _ _ _ hb o Kcov _ bW C V hC hV hCp hVp hCpAccuracy hVpAccuracy Cinv hCinv hchart hsmall
    hσ1 hproductSmall μ _ _ ν _ _ _ _ _ μsmall _ _ X _ _ hXPsp q hq hqPsp refined index _
    W hW indices ξ hξ mesh τ hτ hτP hτ1 N hN hsizeN hsizeBox poly hpoly hmem
    rank hrank hRank cells hcells test htest bases hbases hbaseBox V₀ Z H law
    coverValue wholeReference reconstruct weight cover
  have htestExt : ∀ site z, ‖integerBoxTestExtension N (test site) z‖ ≤ 1 :=
    fun site z => integerBoxTestExtension_norm_le_one N (test site) (htest site) z
  obtain ⟨hmass, hZ, hcomparison⟩ := haffine block hb o bW C V hC hV hCp hVp hCpAccuracy hVpAccuracy
    Cinv hCinv hchart hsmall hσ1 hproductSmall μ ν μsmall hXPsp q hq hqPsp hτ hτP N hN hsizeN
    poly hpoly hmem hrank hRank cells hcells (fun site => integerBoxTestExtension N (test site)) htestExt bases hbases
  refine ⟨hmass, hZ, ?_⟩
  intro window hwindow hDwindow shift moduli residues hmoduli hmoduliM kernelLaw
  have h := hcomparison window hwindow hDwindow shift moduli residues hmoduli hmoduliM
  have hξ1 : ξ ≤ 1 := by
    dsimp only [ξ, normalizedTupleNarrowWidth, twoTermErrorWidth]
    exact min_le_left _ _
  have hext := allocatedOriginalTupleSource_affine_box_extension B U b hR hσ S X q hb o
    N hN hW hτ hξ hξ1 hτ1 hsizeBox (le_refl W) cells hmass test Z poly hmem
    M Dwin window shift hwindow hDwindow moduli residues hmoduli hmoduliM
    (fun g => scalarKernelCutoff_window_size (Fin dim) G hM hDwin hη hlarge (hDwindow g)) bases hbaseBox
  change ‖kernelLaw.complexMean (fun x => 𝔼 base ∈ bases,
      allocatedOriginalTupleSource B U b hR hσ S x X q hb o N hN hW hτ hξ base cells hmass
        (physicalCubeSiteTest (fun site => integerBoxTestExtension N (test site))) Z poly hmem) -
    kernelLaw.goodPartBaseMean bases Good (fun x hx base => cover ⟨x, hx⟩ base)‖ ≤ Real.exp (-E) + η at h
  dsimp only at hext
  rw [hext] at h
  exact h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq fullGridCoverAxisDecidableEq

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

def AllocatedOriginalGenuineAffineData (Psp E e pNum Pbase Qraw pAccuracy pSampling Dgeom cgeom O : ℝ) (hP : 0 ≤ Psp)
    (δ : ℝ≥0) (A Kraw Ksite Kgen : ℕ)
    (witnesses : (q : AllocatedRefinedPeriodIndex m Psp) →
      (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
      AllocatedFullGridResidueWitness (dim := dim) B U b S (q.val : ℕ) r.val)
    (M Dwin : ℕ) (hM : 0 < M) (hDwin : 0 < Dwin) (η : ℝ) (hη : 0 < η) : Prop :=
  ∃ hgridPeriod : ∀ (q : AllocatedRefinedPeriodIndex m Psp)
      (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ))
      (a : {a // allocatedGridAxis (I := I) U b S.value a})
      (k : ((witnesses q r).expansion a).Term),
      0 < ((witnesses q r).expansion a).period k,
  let w := allocatedSiteKernelMaskLog m Psp
  let v := allocatedIdealProfileLog m pAccuracy e
  let Pfinal := sourceCoverParameter dim Kraw Psp pNum Qraw
    (allocatedSiteErrorFourierOutput m pSampling w v)
    (allocatedSeparatedGeometryLog m Psp pAccuracy pSampling w v (E + 2))
  let Mk := scalarKernelCutoff (Fin dim) G M Dwin η
  let hMk := (scalarKernelCutoff_bounds (Fin dim) G hM hDwin hη).1
  ∀ (selection : Fin dim ↪ G) (_hqDim : dim ≤ m + 1)
    (_hcard : dim * (dim + 2) ≤ Fintype.card G) [Nonempty (Fin dim)]
    (hMkPsp : (Mk : ℝ) ≤ Real.exp Psp) (hlarge : Mk ≤ S.value)
    (_hG : (Fintype.card G : ℝ) ≤ Psp) (_hdimP : ((dim + 1 : ℕ) : ℝ) ≤ Psp)
    (_hDexp : Dgeom ≤ Real.exp Psp) (_hpAccuracy : 0 ≤ pAccuracy) (_he : 0 ≤ e)
    (_hE : 0 ≤ E) (_hcgeom : 0 ≤ cgeom) (_hO : 0 ≤ O)
    (_hδ : 0 < δ) (_hδ1 : δ ≤ 1) (_hδe : (δ : ℝ)⁻¹ ≤ Real.exp e)
    (_hKgen : 2 ≤ Kgen)
    (_hSampling : PhysicalAmbientRowsKernelSampling.{uX,uJ,0} m dim Kgen
      (fun j => (rowSets j : Type)) fullRows),
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
    (_hgeom : AllocatedComparisonDimensions (G := G) B (Fin dim) (fun j => (rowSets j : Type)) Dgeom)
    (_hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Dgeom)
    (_hIgeom : ∀ j, (Fintype.card (I j) : ℝ) ≤ Dgeom)
    (_hngeom : ∀ j, (n j : ℝ) ≤ Dgeom)
    (_hKcov : ∀ j, (Fintype.card (Kcov j) : ℝ) ≤ Dgeom)
    (_hCgeom : ∀ j, Cinv j ≤ Real.exp cgeom)
    (_hsmall : ∀ j, R j ≤ allocatedProductChartRadius m Dgeom cgeom)
    (_hσ1 : ∀ j, σ j ≤ 1)
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
    let ξ := normalizedTupleNarrowWidth X indices selection Mk Psp ((E + 2) + 2)
    let hξ := normalizedTupleNarrowWidth_pos X indices selection Mk Psp ((E + 2) + 2)
    let mesh := fun x : GoodKernel =>
      allocatedProductCoarseMesh m X selection Mk (modulus x) Psp pAccuracy w v (E + 2)
    ∀ {τ : ℝ} (hτ : 0 < τ) (_hτP : 1 / τ ≤ Real.exp pNum)
    (_hτ1 : τ ≤ 1 / 2)
    {Psrc Psamp : ℝ} (_hnum : AllocatedSourceNumerics B U b S C V Psrc)
    (_hPsamp : Psp ≤ Psamp) (_hdimPsamp : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ Psamp)
    (_hτPsamp : 1 / τ ≤ Real.exp Psamp)
    (N : X → ℕ) (hN : ∀ t, 0 < N t)
    (_hsize : ∀ t, Real.exp ((Pfinal + Ksite) ^ Ksite) ≤ (N t : ℝ))
    (_hsizeBox : ∀ t, 4 ≤ τ * (N t : ℝ))
    (_hsizeG : ∀ t, Real.exp ((allocatedCutoffSamplingLog m dim Psrc
      (normalizedSiteCutoffBound : ℝ) 0 Psamp + Kgen) ^ Kgen) ≤ (N t : ℝ))
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
    {rank : ℝ}
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) rank (U j) (poly j))
    (_hRank : Real.exp ((Pfinal + Ksite) ^ Ksite) ≤ rank)
    (_hRankG : Real.exp ((allocatedCutoffSamplingLog m dim Psrc
      (normalizedSiteCutoffBound : ℝ) 0 Psamp + Kgen) ^ Kgen) ≤ rank)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
    (_hcells : cells.Nonempty)
    (bases : Finset (X → ℤ)) (_hbases : bases.Nonempty)
    (_hbaseBox : ∀ base ∈ bases, base ∈ trimmedIntegerBox N (spatialTrimMargin τ N)),
    let V₀ := narrowTrimmedSpatialWidths (G := G) (J := indices) W τ ξ N
    let Z := selectedJointDensityMass bases q cells V₀
      (allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem)
    let law := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let wholeReference := fun x => allocatedSupportedWholeReference (dim := dim) B U b S (refined x)
    let idealLog := allocatedGenuineComparisonErrorLog m Psp Dgeom cgeom
      (coarseSpatialPartitionLog (allocatedProductCoarseInput m dim Psp pAccuracy w v (E + 2))) O E
    ∃ hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells V₀ z,
    (|Z - 1| ≤ Real.exp (-Qraw) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z ∧ Z⁻¹ ≤ 2) ∧
    ∃ t : GoodKernel → (X → ℤ) → Fin Mk,
      (∀ x base, kernelPeriodCandidate (m + 1) (t x base) ≤ Mk ^ (m + 1)) ∧
    ∃ F : GoodKernel → (X → ℤ) →
        PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S) →
        AllocatedFiniteIdealData (Fin dim) I n,
      (∀ x base y₀, (F x base y₀).Bounds B U b S rowSets x.val y₀ (refined x) (d x)
        (kernelPeriodCandidate (m + 1) (t x base)) hb o bW hR δ (Real.exp (-idealLog))
        (allocatedFiniteIdealInputLog m Dgeom e idealLog) (layerKernelIndexBound m Mk)) ∧
    ∀ (test : Finset (Fin dim) → (X → ℝ) → ℂ), (∀ site z, ‖test site z‖ ≤ 1) →
    let genuine := fun (x : GoodKernel) base =>
      (law.fiberLaw (principalResidueLabel (refined x))).complexMean (fun r =>
        if hr : 0 < law.mass (Finset.univ.filter (fun y => principalResidueLabel (refined x) y = r)) then
          let rr : AllocatedPositiveResidue (dim := dim) B U b S (refined x) := ⟨r, hr⟩
          let _ : ∀ (a : {a // allocatedGridAxis (I := I) U b S.value a})
              (k : ((witnesses (index x) rr).expansion a).Term),
              NeZero (((witnesses (index x) rr).expansion a).period k) :=
            fun a k => ⟨(hgridPeriod (index x) rr a k).ne'⟩
          ∑ a : cells, (selectedResidueCellWeight q cells V₀ a : ℂ) *
            ((integerBoxCubeCount N dim : ℂ) *
              𝔼 cube : SupportedCube dim (integerBox N : Set (X → ℤ)),
                allocatedAmbientNormalizedSpatialApproximation (τ := τ) B U b S X (modulus x) q
                  (wholeReference x) (witnesses (index x)) hb o bW (d x) x.val hMk selection x.property N hW
                  ⟨mesh x, (allocatedProductCoarseMesh_pos m X selection Mk (modulus x)
                    Psp pAccuracy w v (E + 2)).le⟩ base cells poly hmem rr a
                  (kernelPeriodCandidate (m + 1) (t x base))
                  (F x base ((witnesses (index x) rr).representative)).coefficient
                  (F x base ((witnesses (index x) rr).representative)).factor test
                  ((physicalCubeParametersEquiv X dim).symm cube.val))
        else 0) / (Z : ℂ)
    ∀ (window : G → ℕ) (hwindow : ∀ g, window g ≤ S.value)
      (hDwindow : ∀ g, S.value ≤ Dwin * window g)
      (shift : G → ℤ) (moduli : G → Option (Fin dim) → ℕ)
      (residues : ∀ g i, ZMod (moduli g i))
      (hmoduli : ∀ g i, 0 < moduli g i) (hmoduliM : ∀ g i, moduli g i ≤ M),
    let kernelLaw := FiniteProbabilityWeights.pi (fun g =>
      affineScalarCubeWindowWeights (Fin dim) S.value (window g) M Dwin (shift g) S.positive
        (hwindow g) (hDwindow g) (moduli g) (residues g) (hmoduli g) (hmoduliM g)
        (scalarKernelCutoff_window_size (Fin dim) G hM hDwin hη hlarge (hDwindow g)))
    ‖kernelLaw.complexMean (fun x => 𝔼 base ∈ bases,
        allocatedOriginalTupleSource B U b hR hσ S x X q hb o N hN hW hτ hξ base cells hmass
          (physicalCubeSiteTest test) Z poly hmem) -
      kernelLaw.goodPartBaseMean bases Good (fun x hx base => genuine ⟨x, hx⟩ base)‖ ≤ 2 * Real.exp (-E) + η

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq fullGridCoverAxisDecidableEq

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

theorem allocatedOriginalGenuineAffineData_of_coarse
    {Psp E e pNum Pbase Qraw pAccuracy pSampling Dgeom cgeom O : ℝ} (hP : 0 ≤ Psp)
    {δ : ℝ≥0} {A Kraw Ksite Kgen : ℕ}
    (witnesses : (q : AllocatedRefinedPeriodIndex m Psp) →
      (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
      AllocatedFullGridResidueWitness (dim := dim) B U b S (q.val : ℕ) r.val)
    {Nt Vg Hs : (q : AllocatedRefinedPeriodIndex m Psp) →
      {a // allocatedGridAxis (I := I) U b S.value a} → ℝ} {L : ℝ≥0}
    (hgrid : ∀ q r a, ((witnesses q r).expansion a).Bounds
      (Nt q a) (Vg q a) (Real.exp O) L (Hs q a))
    (M Dwin : ℕ) (hM : 0 < M) (hDwin : 0 < Dwin) (η : ℝ) (hη : 0 < η)
    (hcoarse : AllocatedProductCoarseBoxAffineData.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ S Psp E e pNum Pbase Qraw pAccuracy pSampling hP δ A Kraw Ksite witnesses
      M Dwin hM hDwin η hη) :
    AllocatedOriginalGenuineAffineData.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ S Psp E e pNum Pbase Qraw pAccuracy pSampling Dgeom cgeom O hP δ
      A Kraw Ksite Kgen witnesses M Dwin hM hDwin η hη := by
  unfold AllocatedOriginalGenuineAffineData
  refine ⟨fun q r a k => (hgrid q r a).period_pos k, ?_⟩
  intro w v Pfinal Mk hMk selection hqDim hcard _ hMkPsp hlarge hG hdimP hDexp
    hpAccuracy he hE hcgeom hO hδ hδ1 hδe hKgen hSampling Kernel Good GoodKernel
  obtain ⟨d, hd, hdb, modulus, hmodulus, hmodulusSize, hspatial, hcoefficient, hcoarse⟩ :=
    hcoarse selection hqDim hcard hMkPsp hlarge
  let _ : ∀ x, NeZero (d x) := fun x => ⟨(hd x).ne'⟩
  let _ : ∀ x, NeZero (modulus x) := fun x => ⟨(hmodulus x).ne'⟩
  refine ⟨d, hd, hdb, modulus, hmodulus, hmodulusSize, hspatial, hcoefficient, ?_⟩
  intro block _ _ _ _ _ _ hb o Kcov _ bW C V hC hV hCp hVp hCpAccuracy hVpAccuracy
    Cinv hCinv hchart hgeom hvars hIgeom hngeom hKcov hCgeom hsmall hσ1
    μ _ _ ν _ _ _ _ _ μsmall _ _ X _ _ hXPsp q hq hqPsp refined index _
    W hW indices ξ hξ mesh τ hτ hτP hτ1 Psrc Psamp hnum hPsamp hdimPsamp hτPsamp
    N hN hsizeN hsizeBox hsizeG poly hpoly hmem rank hrank hRank hRankG cells hcells
    bases hbases hbaseBox V₀ Z law wholeReference idealLog
  have hphysical (j : Fin m) : R j ≤ allocatedPhysicalChartRadius (G := G) B (Fin dim) Cinv 1 j :=
    (hsmall j).trans (allocatedProductChartRadius_le_charts B rowSets hgeom hcgeom
      hIgeom hngeom Cinv hCinv hCgeom j).2.1
  have hproduct (j : Fin m) : R j ≤ allocatedProductGridRadius (G := G) B rowSets Cinv j :=
    (hsmall j).trans (allocatedProductChartRadius_le_charts B rowSets hgeom hcgeom
      hIgeom hngeom Cinv hCinv hCgeom j).1
  obtain ⟨hmass, hZ, _⟩ := hcoarse block hb o bW C V hC hV hCp hVp hCpAccuracy hVpAccuracy
    Cinv hCinv hchart hphysical hσ1 hproduct μ ν μsmall hXPsp q hq hqPsp hτ hτP hτ1
    N hN hsizeN hsizeBox poly hpoly hmem hrank hRank cells hcells
    (fun _ _ => 0) (by intros; simp) bases hbases hbaseBox
  have hw : 0 ≤ w := allocatedSiteKernelMaskLog_nonneg m hP
  have hv : 0 ≤ v := allocatedIdealProfileLog_nonneg m hpAccuracy he
  have hPsamp0 : 0 ≤ Psamp := hP.trans hPsamp
  have hone : (1 : ℝ) ≤ Real.exp Psamp := Real.one_le_exp_iff.mpr hPsamp0
  have hstride (z : X) : (q z : ℝ) ≤ Real.exp Psamp :=
    (hqPsp z).trans (Real.exp_le_exp.mpr hPsamp)
  have hfamily (x : GoodKernel) (base : X → ℤ) :=
    exists_allocated_coarse_genuine_source_comparison
      (B := B) (U := U) (b := b) (hR := hR) (hσ := hσ) (hσ1 := hσ1) (S := S)
      (X := X) (modulus := modulus x) (q := q) (wholeReference := wholeReference x)
      (coverWitness := witnesses (index x)) (hb := hb) (o := o) (bW := bW) (d := d x)
      (δ := δ) (x := x.val) (hM := hMk) (selection := selection) (hx := x.property)
      (pAccuracy := pAccuracy) (w := w) (v := v) (Ecoarse := E + 2)
      (N := N) (base := base) (cells := cells) (p := poly) (hm := hmem)
      (C := Cinv) (hC := hCinv) (hchart := hchart) (hgeom := hgeom) (hcgeom := hcgeom)
      (hIgeom := hIgeom) (hngeom := hngeom) (hCgeom := hCgeom) (hsmall := hsmall)
      (D := C) (hD := hC) (Vcov := V) (hnum := hnum) (hVcov := fun j => (hV j).2)
      (Psp := Psp) (O := O) (E := E) (Z := Z) (P := Psamp) (Elog := 0)
      (εs := 1) (η := 1) (S₀ := Real.exp Psamp)
      hpAccuracy hw hv (by linarith) hG (hmodulusSize x)
      hP hDexp hdimP hXPsp hvars hKcov hO hE hMkPsp hZ.2.2.1 hZ.2.2.2
      (hgrid (index x)) hKgen hSampling hPsamp0 (hXPsp.trans hPsamp) hdimPsamp μsmall ν
      (Real.exp_pos _).le le_rfl (by norm_num) hτPsamp (by simpa using hone) hstride
      hsizeG hrank hRankG (by norm_num) le_rfl le_rfl (by norm_num) (by norm_num)
      hq hτ (hspatial x (fun g => (0 : ℤ) + (x.val g none : ℤ))) hpoly hqDim hδ hδ1 hξ he hδe hmass
  choose t ht F hF happrox using hfamily
  refine ⟨hmass, hZ, t, ht, F, hF, ?_⟩
  intro test htest genuine window hwindow hDwindow shift moduli residues hmoduli hmoduliM kernelLaw
  obtain ⟨hmass', _, hsource⟩ := hcoarse block hb o bW C V hC hV hCp hVp hCpAccuracy hVpAccuracy
    Cinv hCinv hchart hphysical hσ1 hproduct μ ν μsmall hXPsp q hq hqPsp hτ hτP hτ1
    N hN hsizeN hsizeBox poly hpoly hmem hrank hRank cells hcells test htest bases hbases hbaseBox
  have hsourceLaw := hsource window hwindow hDwindow shift moduli residues hmoduli hmoduliM
  let cover : GoodKernel → (X → ℤ) → ℂ := fun x base =>
    (law.fiberLaw (principalResidueLabel (refined x))).complexMean (fun r =>
      ∑ a : cells, (selectedResidueCellWeight q cells V₀ a : ℂ) *
        ∑ z ∈ spatialWindow (trimmedSpatialRootScale τ N q) 4,
          allocatedRecenteredResidueWeight (τ := τ) B U b S X (modulus x) q (wholeReference x)
            x.val hMk selection x.property N hW (mesh x) base cells
            (physicalCubeSiteTest (fun site => integerBoxTestExtension N (test site))) r a z *
          allocatedProductFullGridResidueProfile B U b hR hσ S (refined x) x.val hb o bW (d x)
            (witnesses (index x)) δ r (physicalCubeRowSample (O := fun j => (rowSets j : Type))
              U (d x) fullRows poly hmem
              (allocatedWholeResidueReconstruction B U b S X (modulus x) q (wholeReference x)
                x.val base r a.val z))) / (Z : ℂ)
  have hpoint (x : Kernel) (hx : Good x) (base : X → ℤ) (_hb : base ∈ bases) :
      ‖cover ⟨x, hx⟩ base - genuine ⟨x, hx⟩ base‖ ≤ Real.exp (-E) :=
    happrox ⟨x, hx⟩ base test htest
  have htransfer := kernelLaw.complexMean_goodPart_base_transfer bases hbases Good
    (fun x base => allocatedOriginalTupleSource B U b hR hσ S x X q hb o N hN hW hτ hξ
      base cells hmass (physicalCubeSiteTest test) Z poly hmem)
    (fun x hx base => cover ⟨x, hx⟩ base) (fun x hx base => genuine ⟨x, hx⟩ base)
    (Real.exp_pos (-E)).le hsourceLaw hpoint
  exact htransfer.trans_eq (by ring)

end Erdos3.VectorPolynomial

end

end OAI
