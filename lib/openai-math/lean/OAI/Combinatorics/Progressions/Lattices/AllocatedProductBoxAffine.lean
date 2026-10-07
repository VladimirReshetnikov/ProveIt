import OAI.Combinatorics.Progressions.Geometry.AllocatedOriginalBoxInputs
import OAI.Combinatorics.Progressions.Linear.AllocatedProductNormalizedKernel

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem affineScalarCubeWindowWeights_support {I : Type*} [Fintype I] [DecidableEq I]
    (L K M D : ℕ) (c : ℤ) (hL : 0 < L) (hKL : K ≤ L) (hDK : L ≤ D * K)
    (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M)
    (hsize : (Fintype.card I + 1) * M ≤ K) (x : IntegerScalarCubeBox I L)
    (hx : (affineScalarCubeWindowWeights I L K M D c hL hKL hDK m r hm hmM hsize).weight x ≠ 0) :
    (integerScalarCubeWeights I L hL).weight x ≠ 0 := by
  intro hzero
  have hbound := affineScalarCubeWindowWeights_weight_le I L K M D c hL hKL hDK m r hm hmM hsize x
  rw [hzero, mul_zero] at hbound
  exact hx (le_antisymm hbound
    ((affineScalarCubeWindowWeights I L K M D c hL hKL hDK m r hm hmM hsize).nonneg x))

theorem affineScalarCubeWindowWeights_pi_support {G I : Type*}
    [Fintype G] [DecidableEq G] [Fintype I] [DecidableEq I]
    (L M D : ℕ) (hL : 0 < L) (window : G → ℕ) (shift : G → ℤ)
    (hwindow : ∀ g, window g ≤ L) (hDwindow : ∀ g, L ≤ D * window g)
    (moduli : G → Option I → ℕ) (residues : ∀ g i, ZMod (moduli g i))
    (hmoduli : ∀ g i, 0 < moduli g i) (hmoduliM : ∀ g i, moduli g i ≤ M)
    (hsize : ∀ g, (Fintype.card I + 1) * M ≤ window g)
    (x : G → IntegerScalarCubeBox I L)
    (hx : (FiniteProbabilityWeights.pi (fun g =>
      affineScalarCubeWindowWeights I L (window g) M D (shift g) hL
        (hwindow g) (hDwindow g) (moduli g) (residues g) (hmoduli g) (hmoduliM g) (hsize g))).weight x ≠ 0) :
    ∀ g, (integerScalarCubeWeights I L hL).weight (x g) ≠ 0 := by
  intro g
  apply affineScalarCubeWindowWeights_support L (window g) M D (shift g) hL
    (hwindow g) (hDwindow g) (moduli g) (residues g) (hmoduli g) (hmoduliM g) (hsize g) (x g)
  change (∏ g, (affineScalarCubeWindowWeights I L (window g) M D (shift g) hL
    (hwindow g) (hDwindow g) (moduli g) (residues g) (hmoduli g) (hmoduliM g) (hsize g)).weight (x g)) ≠ 0 at hx
  exact Finset.prod_ne_zero_iff.mp hx g (Finset.mem_univ g)

namespace VectorPolynomial

open Module Submodule BooleanCubeKernel

variable {m dim : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type*) [Fintype X] [DecidableEq X] (stride : X → ℕ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (N : X → ℕ) (hN : ∀ a, 0 < N a)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (hξ1 : ξ ≤ 1) (hτ1 : τ ≤ 1 / 2) (hsizeN : ∀ a, 4 ≤ τ * (N a : ℝ))
variable (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (test : Finset (Fin dim) → (X → ℝ) → ℂ) (Z : ℝ)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

include hξ1 hτ1 hsizeN hbudget in
theorem allocatedOriginalTupleSource_affine_box_extension
    (M Dwin : ℕ) (window : G → ℕ) (shift : G → ℤ)
    (hwindow : ∀ g, window g ≤ S.value) (hDwindow : ∀ g, S.value ≤ Dwin * window g)
    (moduli : G → Option (Fin dim) → ℕ) (residues : ∀ g i, ZMod (moduli g i))
    (hmoduli : ∀ g i, 0 < moduli g i) (hmoduliM : ∀ g i, moduli g i ≤ M)
    (hsize : ∀ g, (Fintype.card (Fin dim) + 1) * M ≤ window g)
    (bases : Finset (X → ℤ))
    (hbases : ∀ base ∈ bases, base ∈ trimmedIntegerBox N (spatialTrimMargin τ N)) :
    let kernelLaw := FiniteProbabilityWeights.pi (fun g =>
      affineScalarCubeWindowWeights (Fin dim) S.value (window g) M Dwin (shift g) S.positive
        (hwindow g) (hDwindow g) (moduli g) (residues g) (hmoduli g) (hmoduliM g) (hsize g))
    kernelLaw.complexMean (fun x => 𝔼 base ∈ bases,
      allocatedOriginalTupleSource B U b hR hσ S x X stride hb o N hN hW hτ hξ base cells hmass
        (physicalCubeSiteTest (fun s => integerBoxTestExtension N (test s))) Z poly hmem) =
      kernelLaw.complexMean (fun x => 𝔼 base ∈ bases,
        allocatedOriginalTupleSource B U b hR hσ S x X stride hb o N hN hW hτ hξ base cells hmass
          (physicalCubeSiteTest test) Z poly hmem) := by
  intro kernelLaw
  exact allocatedOriginalTupleSource_box_extension_kernel_mean B U b hR hσ S X stride hb o
    N hN hW hτ hξ hξ1 hτ1 hsizeN hbudget cells hmass test Z poly hmem kernelLaw
    (fun x hx => affineScalarCubeWindowWeights_pi_support S.value M Dwin S.positive window shift
      hwindow hDwindow moduli residues hmoduli hmoduliM hsize x hx) bases hbases

end VectorPolynomial
end Erdos3

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

def AllocatedProductNormalizedAffineData (Psp E e pNum Pbase Qraw pAccuracy pSampling : ℝ) (hP : 0 ≤ Psp)
    (δ : ℝ≥0) (A Kraw Ksite : ℕ)
    (witnesses : (q : AllocatedRefinedPeriodIndex m Psp) →
      (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
      AllocatedFullGridResidueWitness (dim := dim) B U b S (q.val : ℕ) r.val)
    (M Dwin : ℕ) (hM : 0 < M) (hDwin : 0 < Dwin) (η : ℝ) (hη : 0 < η) : Prop :=
  let w := allocatedSiteKernelMaskLog m Psp
  let v := allocatedIdealProfileLog m pAccuracy e
  let Pfinal := sourceCoverParameter dim Kraw Psp pNum Qraw
    (allocatedSiteErrorFourierOutput m pSampling w v)
    (allocatedSeparatedGeometryLog m Psp pAccuracy pSampling w v (E + 1))
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

theorem allocatedProductNormalizedAffineData_of_kernel
    {Psp E e pNum Pbase Qraw pAccuracy pSampling : ℝ} (hP : 0 ≤ Psp)
    {δ : ℝ≥0} {A Kraw Ksite : ℕ}
    (witnesses : (q : AllocatedRefinedPeriodIndex m Psp) →
      (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
      AllocatedFullGridResidueWitness (dim := dim) B U b S (q.val : ℕ) r.val)
    (hkernel : AllocatedProductNormalizedKernelData.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ S Psp E e pNum Pbase Qraw pAccuracy pSampling hP δ A Kraw Ksite witnesses)
    (M Dwin : ℕ) (hM : 0 < M) (hDwin : 0 < Dwin) (η : ℝ) (hη : 0 < η) :
    AllocatedProductNormalizedAffineData.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ S Psp E e pNum Pbase Qraw pAccuracy pSampling hP δ A Kraw Ksite witnesses
      M Dwin hM hDwin η hη := by
  unfold AllocatedProductNormalizedAffineData
  intro w v Pfinal Mk hMk selection hqDim hcard _ hMkPsp hlarge Kernel Good GoodKernel
  obtain ⟨d, hd, hdb, modulus, hmodulus, hmodulusSize, hspatial, hcoefficient, hkernel⟩ :=
    hkernel hMk selection hqDim hMkPsp
  let _ : ∀ x, NeZero (d x) := fun x => ⟨(hd x).ne'⟩
  let _ : ∀ x, NeZero (modulus x) := fun x => ⟨(hmodulus x).ne'⟩
  refine ⟨d, hd, hdb, modulus, hmodulus, hmodulusSize, hspatial, hcoefficient, ?_⟩
  intro block _ _ _ _ _ _ hb o Kcov _ bW C V hC hV hCp hVp hCpAccuracy hVpAccuracy Cinv hCinv hchart hsmall
    hσ1 hproductSmall μ _ _ ν _ _ _ _ _ μsmall _ _ X _ _ hXPsp q hq hqPsp refined index _
    W hW indices ξ hξ sourceMesh mesh τ hτ hτP N hN hsizeN poly hpoly hmem
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

def AllocatedProductBoxAffineData (Psp E e pNum Pbase Qraw pAccuracy pSampling : ℝ) (hP : 0 ≤ Psp)
    (δ : ℝ≥0) (A Kraw Ksite : ℕ)
    (witnesses : (q : AllocatedRefinedPeriodIndex m Psp) →
      (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
      AllocatedFullGridResidueWitness (dim := dim) B U b S (q.val : ℕ) r.val)
    (M Dwin : ℕ) (hM : 0 < M) (hDwin : 0 < Dwin) (η : ℝ) (hη : 0 < η) : Prop :=
  let w := allocatedSiteKernelMaskLog m Psp
  let v := allocatedIdealProfileLog m pAccuracy e
  let Pfinal := sourceCoverParameter dim Kraw Psp pNum Qraw
    (allocatedSiteErrorFourierOutput m pSampling w v)
    (allocatedSeparatedGeometryLog m Psp pAccuracy pSampling w v (E + 1))
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
    let ξ := normalizedTupleNarrowWidth X indices selection Mk Psp ((E + 1) + 2)
    let hξ := normalizedTupleNarrowWidth_pos X indices selection Mk Psp ((E + 1) + 2)
    let sourceMesh := normalizedTupleRadius X selection Mk Psp ((E + 1) + 2) W / 4
    let mesh := min sourceMesh (allocatedOriginalCoverMesh m Psp pAccuracy w v (E + 1))
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
        N hW mesh base cells (physicalCubeSiteTest (fun site => integerBoxTestExtension N (test site)))
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

theorem allocatedProductBoxAffineData_of_normalized
    {Psp E e pNum Pbase Qraw pAccuracy pSampling : ℝ} (hP : 0 ≤ Psp)
    {δ : ℝ≥0} {A Kraw Ksite : ℕ}
    (witnesses : (q : AllocatedRefinedPeriodIndex m Psp) →
      (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
      AllocatedFullGridResidueWitness (dim := dim) B U b S (q.val : ℕ) r.val)
    (M Dwin : ℕ) (hM : 0 < M) (hDwin : 0 < Dwin) (η : ℝ) (hη : 0 < η)
    (haffine : AllocatedProductNormalizedAffineData.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ S Psp E e pNum Pbase Qraw pAccuracy pSampling hP δ A Kraw Ksite witnesses
      M Dwin hM hDwin η hη) :
    AllocatedProductBoxAffineData.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ S Psp E e pNum Pbase Qraw pAccuracy pSampling hP δ A Kraw Ksite witnesses
      M Dwin hM hDwin η hη := by
  unfold AllocatedProductBoxAffineData
  intro w v Pfinal Mk hMk selection hqDim hcard _ hMkPsp hlarge Kernel Good GoodKernel
  obtain ⟨d, hd, hdb, modulus, hmodulus, hmodulusSize, hspatial, hcoefficient, haffine⟩ :=
    haffine selection hqDim hcard hMkPsp hlarge
  let _ : ∀ x, NeZero (d x) := fun x => ⟨(hd x).ne'⟩
  let _ : ∀ x, NeZero (modulus x) := fun x => ⟨(hmodulus x).ne'⟩
  refine ⟨d, hd, hdb, modulus, hmodulus, hmodulusSize, hspatial, hcoefficient, ?_⟩
  intro block _ _ _ _ _ _ hb o Kcov _ bW C V hC hV hCp hVp hCpAccuracy hVpAccuracy Cinv hCinv hchart hsmall
    hσ1 hproductSmall μ _ _ ν _ _ _ _ _ μsmall _ _ X _ _ hXPsp q hq hqPsp refined index _
    W hW indices ξ hξ sourceMesh mesh τ hτ hτP hτ1 N hN hsizeN hsizeBox poly hpoly hmem
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

end OAI
