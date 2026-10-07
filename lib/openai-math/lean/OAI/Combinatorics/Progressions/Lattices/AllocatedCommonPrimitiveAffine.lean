import OAI.Combinatorics.Progressions.Linear.AllocatedCommonKernelLaw
import OAI.Combinatorics.Progressions.Linear.AllocatedConstructedKernelMixture

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

def AllocatedAffineGenuineKernelData (Psp E e pNum Pbase Qraw p₁ : ℝ) (hP : 0 ≤ Psp)
    (δ : ℝ≥0) (A Kraw Ksite : ℕ)
    (witnesses : (q : AllocatedRefinedPeriodIndex m Psp) →
      (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
      AllocatedResidueSiteWitness (dim := dim) B U b S (q.val : ℕ) r.val)
    (L : ℝ≥0) (Cc : activeAxes → ℝ)
    (M Dwin : ℕ) (hM : 0 < M) (hDwin : 0 < Dwin) (η : ℝ) (hη : 0 < η) : Prop :=
  let w := allocatedSiteKernelMaskLog m Psp
  let v := allocatedIdealProfileLog m p₁ e
  let Pfinal := sourceCoverParameter dim Kraw Psp pNum Qraw
    (allocatedSiteErrorFourierOutput m p₁ w v)
    (allocatedOriginalGeometryLog m Psp p₁ w v (E + 1))
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

theorem allocatedAffineGenuineKernelData_of_mixture
    {Psp E e pNum Pbase Qraw p₁ : ℝ} (hP : 0 ≤ Psp)
    {δ : ℝ≥0} {A Kraw Ksite : ℕ}
    (witnesses : (q : AllocatedRefinedPeriodIndex m Psp) →
      (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
      AllocatedResidueSiteWitness (dim := dim) B U b S (q.val : ℕ) r.val)
    {L : ℝ≥0} {Cc : activeAxes → ℝ}
    (hmixture : AllocatedGenuineKernelData.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ S Psp E e pNum Pbase Qraw p₁ hP δ A Kraw Ksite witnesses L Cc)
    (M Dwin : ℕ) (hM : 0 < M) (hDwin : 0 < Dwin) (η : ℝ) (hη : 0 < η) :
    AllocatedAffineGenuineKernelData.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ S Psp E e pNum Pbase Qraw p₁ hP δ A Kraw Ksite witnesses L Cc M Dwin hM hDwin η hη := by
  unfold AllocatedAffineGenuineKernelData
  intro w v Pfinal Mk hMk selection hqDim hcard _ hMkPsp hlarge Kernel Good GoodKernel
  obtain ⟨d, hd, hdb, modulus, hmodulus, hmodulusSize, hspatial, hcoefficient, hmixture⟩ :=
    hmixture hMk selection hqDim hMkPsp
  let : ∀ x, NeZero (d x) := fun x => ⟨(hd x).ne'⟩
  let : ∀ x, NeZero (modulus x) := fun x => ⟨(hmodulus x).ne'⟩
  refine ⟨d, hd, hdb, modulus, hmodulus, hmodulusSize, hspatial, hcoefficient, ?_⟩
  intro block _ _ _ _ _ _ hb o Kcov _ bW C V hC hV hCp hVp Cinv hCinv hchart hsmall
    Qsite hQsite Kcap hKcap hσ1 hcoverSmall
  obtain ⟨g, hg, hcoeff, hmassCover, hmixture⟩ := hmixture block hb o bW C V hC hV hCp hVp
    Cinv hCinv hchart hsmall Qsite hQsite Kcap hKcap hσ1 hcoverSmall
  refine ⟨g, hg, hcoeff, hmassCover, ?_⟩
  intro μ _ _ ν _ _ _ _ _ μsmall _ _ X _ _ hXPsp q hq hqPsp refined index _
    W hW indices ξ hξ sourceMesh mesh τ hτ hτP N hN hsizeN poly hpoly hmem
    rank hrank hRank cells hcells test htest bases hbases V₀ Z hZ H law
    coverValue wholeReference reconstruct weight cover
  obtain ⟨hmass, hmixture⟩ := hmixture μ ν μsmall hXPsp q hq hqPsp hτ hτP N hN hsizeN
    poly hpoly hmem hrank hRank cells hcells test htest bases hbases hZ
  refine ⟨hmass, ?_⟩
  intro window hwindow hDwindow shift moduli residues hmoduli hmoduliM kernelLaw
  have hbad := affineKernel_explicit_probability_le_of_card_le (Fin dim) G
    (by simpa only [Fintype.card_fin] using hcard) selection hM hDwin hη S.positive hlarge
    window hwindow hDwindow shift moduli residues hmoduli hmoduliM
  exact hmixture kernelLaw hbad

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

def AllocatedAccurateAffineData (Psp E e pNum Pbase Qraw p₁ : ℝ) (hP : 0 ≤ Psp)
    (δ : ℝ≥0) (A Kraw Ksite : ℕ)
    (witnesses : (q : AllocatedRefinedPeriodIndex m Psp) →
      (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
      AllocatedResidueSiteWitness (dim := dim) B U b S (q.val : ℕ) r.val)
    (L : ℝ≥0) (Cc : activeAxes → ℝ)
    (M Dwin : ℕ) (hM : 0 < M) (hDwin : 0 < Dwin)
    (hMkPsp : (scalarKernelCutoff (Fin dim) G M Dwin (Real.exp (-(E + 1))) : ℝ) ≤ Real.exp Psp)
    (hlarge : scalarKernelCutoff (Fin dim) G M Dwin (Real.exp (-(E + 1))) ≤ S.value) : Prop :=
  let Epoint := E + 1
  let η := Real.exp (-(E + 1))
  let hη := Real.exp_pos (-(E + 1))
  let w := allocatedSiteKernelMaskLog m Psp
  let v := allocatedIdealProfileLog m p₁ e
  let Pfinal := sourceCoverParameter dim Kraw Psp pNum Qraw
    (allocatedSiteErrorFourierOutput m p₁ w v)
    (allocatedOriginalGeometryLog m Psp p₁ w v (Epoint + 1))
  let Mk := scalarKernelCutoff (Fin dim) G M Dwin η
  let hMk := (scalarKernelCutoff_bounds (Fin dim) G hM hDwin hη).1
  ∀ (selection : Fin dim ↪ G) (_hqDim : dim ≤ m + 1)
    (_hcard : dim * (dim + 2) ≤ Fintype.card G) [Nonempty (Fin dim)]
    ,
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
    let ξ := normalizedTupleNarrowWidth X indices selection Mk Psp ((Epoint + 1) + 2)
    let hξ := normalizedTupleNarrowWidth_pos X indices selection Mk Psp ((Epoint + 1) + 2)
    let sourceMesh := normalizedTupleRadius X selection Mk Psp ((Epoint + 1) + 2) W / 4
    let mesh := min sourceMesh (allocatedOriginalCoverMesh m Psp p₁ w v (Epoint + 1))
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
      kernelLaw.goodPartBaseMean bases Good (fun x hx base => cover ⟨x, hx⟩ base)‖ ≤ Real.exp (-E)

theorem allocatedAccurateAffineData_of_mixture
    {Psp E e pNum Pbase Qraw p₁ : ℝ} (hP : 0 ≤ Psp)
    {δ : ℝ≥0} {A Kraw Ksite : ℕ}
    (witnesses : (q : AllocatedRefinedPeriodIndex m Psp) →
      (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
      AllocatedResidueSiteWitness (dim := dim) B U b S (q.val : ℕ) r.val)
    {L : ℝ≥0} {Cc : activeAxes → ℝ}
    (hmixture : AllocatedGenuineKernelData.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ S Psp (E + 1) e pNum Pbase Qraw p₁ hP δ A Kraw Ksite witnesses L Cc)
    (M Dwin : ℕ) (hM : 0 < M) (hDwin : 0 < Dwin)
    (hMkPsp : (scalarKernelCutoff (Fin dim) G M Dwin (Real.exp (-(E + 1))) : ℝ) ≤ Real.exp Psp)
    (hlarge : scalarKernelCutoff (Fin dim) G M Dwin (Real.exp (-(E + 1))) ≤ S.value) :
    AllocatedAccurateAffineData.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ S Psp E e pNum Pbase Qraw p₁ hP δ A Kraw Ksite witnesses L Cc M Dwin hM hDwin hMkPsp hlarge := by
  have herror : Real.exp (-(E + 1)) + Real.exp (-(E + 1)) ≤ Real.exp (-E) := by
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ = 2 * Real.exp (-(E + 1)) := by ring
      _ ≤ Real.exp 1 * Real.exp (-(E + 1)) := mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hAffine := allocatedAffineGenuineKernelData_of_mixture B U b hR hσ S hP witnesses hmixture
    M Dwin hM hDwin (Real.exp (-(E + 1))) (Real.exp_pos _)
  unfold AllocatedAccurateAffineData
  intro Epoint η hη w v Pfinal Mk hMk selection hqDim hcard _ Kernel Good GoodKernel
  obtain ⟨d, hd, hdb, modulus, hmodulus, hmodulusSize, hspatial, hcoefficient, hAffine⟩ :=
    hAffine selection hqDim hcard hMkPsp hlarge
  let : ∀ x, NeZero (d x) := fun x => ⟨(hd x).ne'⟩
  let : ∀ x, NeZero (modulus x) := fun x => ⟨(hmodulus x).ne'⟩
  refine ⟨d, hd, hdb, modulus, hmodulus, hmodulusSize, hspatial, hcoefficient, ?_⟩
  intro block _ _ _ _ _ _ hb o Kcov _ bW C V hC hV hCp hVp Cinv hCinv hchart hsmall
    Qsite hQsite Kcap hKcap hσ1 hcoverSmall
  obtain ⟨g, hg, hcoeff, hmassCover, hAffine⟩ := hAffine block hb o bW C V hC hV hCp hVp
    Cinv hCinv hchart hsmall Qsite hQsite Kcap hKcap hσ1 hcoverSmall
  refine ⟨g, hg, hcoeff, hmassCover, ?_⟩
  intro μ _ _ ν _ _ _ _ _ μsmall _ _ X _ _ hXPsp q hq hqPsp refined index _
    W hW indices ξ hξ sourceMesh mesh τ hτ hτP N hN hsizeN poly hpoly hmem
    rank hrank hRank cells hcells test htest bases hbases V₀ Z hZ H law
    coverValue wholeReference reconstruct weight cover
  obtain ⟨hmass, hAffine⟩ := hAffine μ ν μsmall hXPsp q hq hqPsp hτ hτP N hN hsizeN
    poly hpoly hmem hrank hRank cells hcells test htest bases hbases hZ
  refine ⟨hmass, ?_⟩
  intro window hwindow hDwindow shift moduli residues hmoduli hmoduliM kernelLaw
  exact (hAffine window hwindow hDwindow shift moduli residues hmoduli hmoduliM).trans herror

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

def AllocatedNormalizedAffineData (Psp E e pNum Pbase Qraw p₁ : ℝ) (hP : 0 ≤ Psp)
    (δ : ℝ≥0) (A Kraw Ksite : ℕ)
    (witnesses : (q : AllocatedRefinedPeriodIndex m Psp) →
      (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
      AllocatedResidueSiteWitness (dim := dim) B U b S (q.val : ℕ) r.val)
    (L : ℝ≥0) (Cc : activeAxes → ℝ)
    (M Dwin : ℕ) (hM : 0 < M) (hDwin : 0 < Dwin)
    (hMkPsp : (scalarKernelCutoff (Fin dim) G M Dwin (Real.exp (-(E + 1))) : ℝ) ≤ Real.exp Psp)
    (hlarge : scalarKernelCutoff (Fin dim) G M Dwin (Real.exp (-(E + 1))) ≤ S.value) : Prop :=
  let Epoint := E + 1
  let η := Real.exp (-(E + 1))
  let hη := Real.exp_pos (-(E + 1))
  let w := allocatedSiteKernelMaskLog m Psp
  let v := allocatedIdealProfileLog m p₁ e
  let Pfinal := sourceCoverParameter dim Kraw Psp pNum Qraw
    (allocatedSiteErrorFourierOutput m p₁ w v)
    (allocatedOriginalGeometryLog m Psp p₁ w v (Epoint + 1))
  let Mk := scalarKernelCutoff (Fin dim) G M Dwin η
  let hMk := (scalarKernelCutoff_bounds (Fin dim) G hM hDwin hη).1
  ∀ (selection : Fin dim ↪ G) (_hqDim : dim ≤ m + 1)
    (_hcard : dim * (dim + 2) ≤ Fintype.card G) [Nonempty (Fin dim)]
    ,
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
    let ξ := normalizedTupleNarrowWidth X indices selection Mk Psp ((Epoint + 1) + 2)
    let hξ := normalizedTupleNarrowWidth_pos X indices selection Mk Psp ((Epoint + 1) + 2)
    let sourceMesh := normalizedTupleRadius X selection Mk Psp ((Epoint + 1) + 2) W / 4
    let mesh := min sourceMesh (allocatedOriginalCoverMesh m Psp p₁ w v (Epoint + 1))
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
      kernelLaw.goodPartBaseMean bases Good (fun x hx base => cover ⟨x, hx⟩ base)‖ ≤ Real.exp (-E)

theorem allocatedAccurateAffineData_normalized
    {Psp E e pNum Pbase p₁ l F : ℝ} (hP : 0 ≤ Psp) (hE : 0 ≤ E)
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
      AllocatedResidueSiteWitness (dim := dim) B U b S (q.val : ℕ) r.val)
    {L : ℝ≥0} {Cc : activeAxes → ℝ}
    (M Dwin : ℕ) (hM : 0 < M) (hDwin : 0 < Dwin)
    (hMkPsp : (scalarKernelCutoff (Fin dim) G M Dwin (Real.exp (-(E + 1))) : ℝ) ≤ Real.exp Psp)
    (hlarge : scalarKernelCutoff (Fin dim) G M Dwin (Real.exp (-(E + 1))) ≤ S.value) :
    let Qraw := allocatedSourceSamplingBudget m dim A Pbase ((E + 1) + 1) l F
    AllocatedAccurateAffineData.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ S Psp E e pNum Pbase Qraw p₁ hP δ A Kraw Ksite witnesses L Cc
      M Dwin hM hDwin hMkPsp hlarge →
    AllocatedNormalizedAffineData.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ S Psp E e pNum Pbase Qraw p₁ hP δ A Kraw (max Ksite Knorm) witnesses L Cc
      M Dwin hM hDwin hMkPsp hlarge := by
  intro Qraw hAffine
  have hPbase0 : 0 ≤ Pbase := hP.trans hPbase
  have hEsource : 0 ≤ (E + 1) + 1 := by linarith
  have hQraw1 : 1 ≤ Qraw :=
    (allocatedSourceSamplingBudget_bounds m dim A hPbase0 hEsource (hPbase0.trans hl) hF).1
  have hQraw0 : 0 ≤ Qraw := zero_le_one.trans hQraw1
  unfold AllocatedNormalizedAffineData
  intro Epoint η hη w v Pfinal Mk hMk selection hqDim hcard _ Kernel Good GoodKernel
  have hFinal := sourceCoverParameter_bounds dim Kraw (pNum := pNum) (Qraw := Qraw)
    (F := allocatedSiteErrorFourierOutput m p₁ w v)
    (G := allocatedOriginalGeometryLog m Psp p₁ w v (Epoint + 1)) hP
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
  obtain ⟨d, hd, hdb, modulus, hmodulus, hmodulusSize, hspatial, hcoefficient, hAffine⟩ :=
    hAffine selection hqDim hcard
  let : ∀ x, NeZero (d x) := fun x => ⟨(hd x).ne'⟩
  let : ∀ x, NeZero (modulus x) := fun x => ⟨(hmodulus x).ne'⟩
  refine ⟨d, hd, hdb, modulus, hmodulus, hmodulusSize, hspatial, hcoefficient, ?_⟩
  intro block _ _ _ _ _ _ hb o Kcov _ bW C V hC hV hCp hVp Cinv hCinv hchart hsmall
    Qsite hQsite Kcap hKcap hσ1 hcoverSmall
  obtain ⟨g, hg, hcoeff, hmassCover, hAffine⟩ := hAffine block hb o bW C V hC hV hCp hVp
    Cinv hCinv hchart hsmall Qsite hQsite Kcap hKcap hσ1 hcoverSmall
  refine ⟨g, hg, hcoeff, hmassCover, ?_⟩
  intro μ _ _ ν _ _ _ _ _ μsmall _ _ X _ _ hXPsp q hq hqPsp refined index _
    W hW indices ξ hξ sourceMesh mesh τ hτ hτP N hN hsizeN poly hpoly hmem
    rank hrank hRank cells hcells test htest bases hbases V₀ Z H law
    coverValue wholeReference reconstruct weight cover
  obtain ⟨_, hnormal⟩ := hnorm B U b S hb o μ ν hR hσ hσ1 C V hC hV Cinv hCinv hchart
    hsmall A (hnum o C V hCp hVp) hP hEsource hPbase hm hdim hG hl hF
    hXPsp selection hMk hMkPsp q hq hqPsp hτ (hτP.trans (Real.exp_le_exp.mpr hpNum))
    N (fun t => hNormCut.trans (hsizeN t)) poly hpoly hmem hrank (hNormCut.trans hRank) cells hcells
  have hZ := hnormal bases hbases
  obtain ⟨hmass, hAffine⟩ := hAffine μ ν μsmall hXPsp q hq hqPsp hτ hτP N hN
    (fun t => hOldCut.trans (hsizeN t)) poly hpoly hmem hrank (hOldCut.trans hRank)
    cells hcells test htest bases hbases hZ.2.1.1
  exact ⟨hmass, hZ, hAffine⟩

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

def AllocatedPrimitiveAffineData (p c Psp E e pNum Pbase Qraw p₁ : ℝ) (hP : 0 ≤ Psp)
    (δ : ℝ≥0) (A Ksize : ℕ)
    (witnesses : (q : AllocatedRefinedPeriodIndex m Psp) →
      (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
      AllocatedResidueSiteWitness (dim := dim) B U b S (q.val : ℕ) r.val)
    (L : ℝ≥0) (Cc : activeAxes → ℝ)
    (M Dwin : ℕ) (hM : 0 < M) (hDwin : 0 < Dwin)
    (hMkPsp : (scalarKernelCutoff (Fin dim) G M Dwin (Real.exp (-(E + 1))) : ℝ) ≤ Real.exp Psp)
    (hlarge : scalarKernelCutoff (Fin dim) G M Dwin (Real.exp (-(E + 1))) ≤ S.value) : Prop :=
  let Epoint := E + 1
  let η := Real.exp (-(E + 1))
  let hη := Real.exp_pos (-(E + 1))
  let w := allocatedSiteKernelMaskLog m Psp
  let v := allocatedIdealProfileLog m p₁ e
  let sizeLog := (p + c + Psp + E + Ksize) ^ Ksize
  let Mk := scalarKernelCutoff (Fin dim) G M Dwin η
  let hMk := (scalarKernelCutoff_bounds (Fin dim) G hM hDwin hη).1
  ∀ (selection : Fin dim ↪ G) (_hqDim : dim ≤ m + 1)
    (_hcard : dim * (dim + 2) ≤ Fintype.card G) [Nonempty (Fin dim)]
    ,
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
    (_hCinvP : ∀ j, Cinv j ≤ Real.exp p)
    (Qsite : ℝ≥0)
    (_hQsite : ∀ a : activeAxes, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (ig a.val).1 (ig a.val).2) : ℝ) + 1) ≤ Qsite)
    (Kcap : ℝ≥0) (_hKcap : ∀ j, (R j)⁻¹ ≤ Kcap) (_hσ1 : ∀ j, σ j ≤ 1),
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
    let ξ := normalizedTupleNarrowWidth X indices selection Mk Psp ((Epoint + 1) + 2)
    let hξ := normalizedTupleNarrowWidth_pos X indices selection Mk Psp ((Epoint + 1) + 2)
    let sourceMesh := normalizedTupleRadius X selection Mk Psp ((Epoint + 1) + 2) W / 4
    let mesh := min sourceMesh (allocatedOriginalCoverMesh m Psp p₁ w v (Epoint + 1))
    ∀ {τ : ℝ} (hτ : 0 < τ) (_hτP : 1 / τ ≤ Real.exp pNum)
    (N : X → ℕ) (hN : ∀ t, 0 < N t)
    (_hsize : ∀ t, Real.exp sizeLog ≤ (N t : ℝ))
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
    {rank : ℝ}
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) rank (U j) (poly j))
    (_hRank : Real.exp sizeLog ≤ rank)
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
      kernelLaw.goodPartBaseMean bases Good (fun x hx base => cover ⟨x, hx⟩ base)‖ ≤ Real.exp (-E)

theorem allocatedNormalizedAffineData_primitive
    {p c Psp E e pNum Pbase Qraw p₁ : ℝ} (hp : 0 ≤ p) (hP : 0 ≤ Psp)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (hRsmall : ∀ j, R j ≤ allocatedSourceCoverRadius m p p)
    {δ : ℝ≥0} {A Kraw Ksite Ksize : ℕ}
    (witnesses : (q : AllocatedRefinedPeriodIndex m Psp) →
      (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
      AllocatedResidueSiteWitness (dim := dim) B U b S (q.val : ℕ) r.val)
    {L : ℝ≥0} {Cc : activeAxes → ℝ}
    (M Dwin : ℕ) (hM : 0 < M) (hDwin : 0 < Dwin)
    (hMkPsp : (scalarKernelCutoff (Fin dim) G M Dwin (Real.exp (-(E + 1))) : ℝ) ≤ Real.exp Psp)
    (hlarge : scalarKernelCutoff (Fin dim) G M Dwin (Real.exp (-(E + 1))) ≤ S.value) :
    let w := allocatedSiteKernelMaskLog m Psp
    let v := allocatedIdealProfileLog m p₁ e
    let Pfinal := sourceCoverParameter dim Kraw Psp pNum Qraw
      (allocatedSiteErrorFourierOutput m p₁ w v)
      (allocatedOriginalGeometryLog m Psp p₁ w v ((E + 1) + 1))
    (Pfinal + Ksite) ^ Ksite ≤ (p + c + Psp + E + Ksize) ^ Ksize →
    AllocatedNormalizedAffineData.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ S Psp E e pNum Pbase Qraw p₁ hP δ A Kraw Ksite witnesses L Cc
      M Dwin hM hDwin hMkPsp hlarge →
    AllocatedPrimitiveAffineData.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ S p c Psp E e pNum Pbase Qraw p₁ hP δ A Ksize witnesses L Cc
      M Dwin hM hDwin hMkPsp hlarge := by
  intro w v Pfinal hcut hSource
  have hCut := Real.exp_le_exp.mpr hcut
  unfold AllocatedPrimitiveAffineData
  intro Epoint η hη w' v' sizeLog Mk hMk selection hqDim hcard _ Kernel Good GoodKernel
  obtain ⟨d, hd, hdb, modulus, hmodulus, hmodulusSize, hspatial, hcoefficient, hSource⟩ :=
    hSource selection hqDim hcard
  let : ∀ x, NeZero (d x) := fun x => ⟨(hd x).ne'⟩
  let : ∀ x, NeZero (modulus x) := fun x => ⟨(hmodulus x).ne'⟩
  refine ⟨d, hd, hdb, modulus, hmodulus, hmodulusSize, hspatial, hcoefficient, ?_⟩
  intro block _ _ _ _ _ _ hb o Kcov _ bW C V hC hV hCp hVp Cinv hCinv hchart hCinvP
    Qsite hQsite Kcap hKcap hσ1
  have hcharts := fun j => allocatedSourceCoverRadius_le_charts B rowSets hp hp
    (by simpa only [Fintype.card_fin] using hqDim) hvars hI hn Cinv hCinv hCinvP j
  have hsmall := fun j => (hRsmall j).trans (hcharts j).1
  have hcoverSmall := fun j => (hRsmall j).trans (hcharts j).2
  obtain ⟨g, hg, hcoeff, hmassCover, hSource⟩ := hSource block hb o bW C V hC hV hCp hVp
    Cinv hCinv hchart hsmall Qsite hQsite Kcap hKcap hσ1 hcoverSmall
  refine ⟨g, hg, hcoeff, hmassCover, ?_⟩
  intro μ _ _ ν _ _ _ _ _ μsmall _ _ X _ _ hXPsp q hq hqPsp refined index _
    W hW indices ξ hξ sourceMesh mesh τ hτ hτP N hN hsizeN poly hpoly hmem
    rank hrank hRank cells hcells test htest bases hbases V₀ Z H law
    coverValue wholeReference reconstruct weight cover
  exact hSource μ ν μsmall hXPsp q hq hqPsp hτ hτP N hN
    (fun t => hCut.trans (hsizeN t)) poly hpoly hmem hrank (hCut.trans hRank)
    cells hcells test htest bases hbases

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

def AllocatedCommonAccurateAffineAt (p Psp E e t : ℝ) (hP : 0 ≤ Psp) (δ : ℝ≥0)
    (A T Kproj Kideal Ksite : ℕ) : Prop :=
  let Epoint := E + 1
  ∀ {c : ℝ}, 0 ≤ c →
    ∀ {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j),
    (∀ j, σ j ≤ t) → (∀ j, R j ≤ 1) →
    (∀ j, (R j)⁻¹ ≤ Real.exp c) → (∀ j, (σ j)⁻¹ ≤ Real.exp c) →
    let Eraw := Epoint + 1 + 4
    let Esite := allocatedOriginalCoverAccuracy Psp (Epoint + 1)
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
      ∀ (_hcard : dim * (dim + 2) ≤ Fintype.card G) [Nonempty (Fin dim)]
        (Tker : ℝ) (_hTker : 0 ≤ Tker)
        (_hbudget : allocatedKernelPrimitiveBudget p E Tker ≤ Psp)
        (M Dwin : ℕ) (hM : 0 < M) (hDwin : 0 < Dwin)
        (_hMT : (M : ℝ) ≤ Real.exp Tker) (_hDwinP : (Dwin : ℝ) ≤ Real.exp p),
      ∃ hMkPsp : (scalarKernelCutoff (Fin dim) G M Dwin (Real.exp (-(E + 1))) : ℝ) ≤ Real.exp Psp,
      ∃ hlarge : scalarKernelCutoff (Fin dim) G M Dwin (Real.exp (-(E + 1))) ≤ S.value,
        AllocatedAccurateAffineData.{uG,uI,uB,uJ,uQ,uX}
          B U b hR hσ S Psp E e pNum Pbase (allocatedSourceSamplingBudget m dim A Pbase (Epoint + 1) lateLog F)
          p₁ hP δ A (max T (max Kproj Kideal)) Ksite witnesses L Cc M Dwin hM hDwin hMkPsp hlarge

theorem allocatedCommonGenuineKernelAt_accurate_affine
    {p P E e t : ℝ} (hp : 0 ≤ p) (hP : 0 ≤ P) (hE : 0 ≤ E) (he : 0 ≤ e)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    {δ : ℝ≥0} {A T Kproj Kideal Ksite : ℕ}
    (hkernel : AllocatedCommonGenuineKernelAt.{uG,uI,uB,uJ,uQ,uX}
      (G := G) (dim := dim) B p P (E + 1) e t hP δ A T Kproj Kideal Ksite) :
    AllocatedCommonAccurateAffineAt.{uG,uI,uB,uJ,uQ,uX}
      (G := G) (dim := dim) B p P E e t hP δ A T Kproj Kideal Ksite := by
  unfold AllocatedCommonAccurateAffineAt
  intro Epoint c hc J _ U b R σ hR hσ hσt hR1 hRi hσi
  obtain ⟨witnesses, hFamily, hData⟩ := hkernel hc U b hR hσ hσt hR1 hRi hσi
  refine ⟨witnesses, hFamily, ?_⟩
  intro hcard _ Tker hTker hbudget M Dwin hM hDwin hMT hDwinP
  have hG : (Fintype.card G : ℝ) ≤ p :=
    (Nat.cast_le.mpr (allocatedKernelVariables_card_le_variables (G := G) B)).trans hvars
  have hdimNat : dim ≤ Fintype.card G :=
    (show dim ≤ dim * (dim + 2) by nlinarith).trans hcard
  have hdim : (dim : ℝ) ≤ p := (Nat.cast_le.mpr hdimNat).trans hG
  have hcut := allocatedCommonScale_kernel_cutoff (dim := dim) B U b hR hσ
    hp hc hP he (show 0 ≤ (E + 1) + 1 + 4 by linarith) hE hTker hdim hG hbudget
    hM hDwin hMT hDwinP
  refine ⟨hcut.2.1, hcut.2.2, ?_⟩
  exact allocatedAccurateAffineData_of_mixture B U b hR hσ _ hP witnesses hData
    M Dwin hM hDwin hcut.2.1 hcut.2.2

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

def AllocatedCommonNormalizedAffineAt (p Psp E e t : ℝ) (hP : 0 ≤ Psp) (δ : ℝ≥0)
    (A T Kproj Kideal Ksite : ℕ) : Prop :=
  let Epoint := E + 1
  ∀ {c : ℝ}, 0 ≤ c →
    ∀ {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j),
    (∀ j, σ j ≤ t) → (∀ j, R j ≤ 1) →
    (∀ j, (R j)⁻¹ ≤ Real.exp c) → (∀ j, (σ j)⁻¹ ≤ Real.exp c) →
    let Eraw := Epoint + 1 + 4
    let Esite := allocatedOriginalCoverAccuracy Psp (Epoint + 1)
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
      ∀ (_hcard : dim * (dim + 2) ≤ Fintype.card G) [Nonempty (Fin dim)]
        (Tker : ℝ) (_hTker : 0 ≤ Tker)
        (_hbudget : allocatedKernelPrimitiveBudget p E Tker ≤ Psp)
        (M Dwin : ℕ) (hM : 0 < M) (hDwin : 0 < Dwin)
        (_hMT : (M : ℝ) ≤ Real.exp Tker) (_hDwinP : (Dwin : ℝ) ≤ Real.exp p),
      ∃ hMkPsp : (scalarKernelCutoff (Fin dim) G M Dwin (Real.exp (-(E + 1))) : ℝ) ≤ Real.exp Psp,
      ∃ hlarge : scalarKernelCutoff (Fin dim) G M Dwin (Real.exp (-(E + 1))) ≤ S.value,
        AllocatedNormalizedAffineData.{uG,uI,uB,uJ,uQ,uX}
          B U b hR hσ S Psp E e pNum Pbase (allocatedSourceSamplingBudget m dim A Pbase (Epoint + 1) lateLog F)
          p₁ hP δ A (max T (max Kproj Kideal)) Ksite witnesses L Cc M Dwin hM hDwin hMkPsp hlarge

theorem allocatedCommonAccurateAffineAt_normalized
    {p P E e t : ℝ} (hp : 0 ≤ p) (hP : 0 ≤ P) (hE : 0 ≤ E) (he : 0 ≤ e)
    (hdim : dim ≤ m + 1) (hmP : ((m + 2 : ℕ) : ℝ) ≤ P) (hpP : p ≤ P)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    {δ : ℝ≥0} {A T Kproj Kideal Ksite Knorm : ℕ}
    (hT : 1 ≤ T) (hKsite : 1 ≤ Ksite) (hKnorm : 1 ≤ Knorm)
    (hnorm : AllocatedSourceNarrowNormalization.{uG,uI,uB,uJ,uX} m Knorm)
    (hcover : AllocatedCommonAccurateAffineAt.{uG,uI,uB,uJ,uQ,uX}
      (G := G) (dim := dim) B p P E e t hP δ A T Kproj Kideal Ksite) :
    AllocatedCommonNormalizedAffineAt.{uG,uI,uB,uJ,uQ,uX}
      (G := G) (dim := dim) B p P E e t hP δ A T Kproj Kideal (max Ksite Knorm) := by
  unfold AllocatedCommonNormalizedAffineAt
  intro Epoint c hc J _ U b R σ hR hσ hσt hR1 hRi hσi
    Eraw Esite D pNum S p₁ w v error lengthLog gainLog Pbase lateLog F Λ L Cc
  have hdimensions : AllocatedComparisonDimensions (G := G) B (Fin dim) jets D :=
    allocatedComparisonDimensions_of_primitive B
      (fun j => (Subtype.val : jets j → Finset (Fin dim)))
      (by simpa only [Fintype.card_fin] using hdim)
      (fun _ => Subtype.val_injective) hp hvars hI hn
  have hEraw : 0 ≤ Eraw := by dsimp only [Eraw, Epoint]; linarith
  obtain ⟨hNum, _, hcNum, hPNum, _⟩ := allocatedCommonScaleNumeric_bounds m hp hc hP hEraw
  have hw : 0 ≤ w := allocatedSiteKernelMaskLog_nonneg m hP
  have herror : 0 ≤ error := allocatedReferenceIdealError_nonneg m hdimensions.nonneg hP hEraw
  have hgain : 0 ≤ gainLog := allocatedProfileGainLog_nonneg m hdimensions.nonneg hP hw
  have hlength : 0 ≤ lengthLog := by
    have h := allocatedIdealScaleInput_bounds m hdimensions.nonneg hNum he hw herror
    exact h.2.1.trans h.2.2.2.2.2
  have hF : 0 ≤ F := allocatedActualProfileFourier_nonneg m hdimensions.nonneg hNum he hgain hlength
  obtain ⟨hBase1, _, hNumBase, _, _⟩ :=
    allocatedIdealSourceBudget_bounds m hdimensions.nonneg hNum he hw herror
  have hBase0 : 0 ≤ Pbase := zero_le_one.trans hBase1
  have hPBase : P ≤ Pbase := hPNum.trans hNumBase
  have hlate : Pbase ≤ lateLog := by
    have hcap : 0 ≤ (Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) : ℝ) *
        allocatedAmbientLog m Pbase := mul_nonneg (Nat.cast_nonneg _) (allocatedAmbientLog_nonneg m hBase0)
    dsimp only [lateLog, allocatedSpatialLateLog]
    linarith
  have hnum : ∀ (_o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
      (C V : Fin m → ℝ≥0), (∀ j, (C j : ℝ) ≤ Real.exp pNum) →
      (∀ j, (V j : ℝ) ≤ Real.exp pNum) → AllocatedSourceNumerics B U b S C V Pbase := by
    intro o C V hCp hVp
    exact allocatedIdealSource_numerics B U b o hdimensions hNum he hw herror hR hσ
      (fun j => (hRi j).trans (Real.exp_le_exp.mpr hcNum))
      (fun j => (hσi j).trans (Real.exp_le_exp.mpr hcNum)) C V hCp hVp
  have hmNorm : ((m + 1 : ℕ) : ℝ) ≤ P :=
    (Nat.cast_le.mpr (show m + 1 ≤ m + 2 by omega)).trans hmP
  have hdimNorm : ((dim + 1 : ℕ) : ℝ) ≤ P :=
    (Nat.cast_le.mpr (show dim + 1 ≤ m + 2 by omega)).trans hmP
  have hG : (Fintype.card G : ℝ) ≤ P :=
    (Nat.cast_le.mpr (allocatedKernelVariables_card_le_variables (G := G) B)).trans (hvars.trans hpP)
  obtain ⟨witnesses, hFamily, hData⟩ := hcover hc U b hR hσ hσt hR1 hRi hσi
  refine ⟨witnesses, hFamily, ?_⟩
  intro hcard _ Tker hTker hbudget M Dwin hM hDwin hMT hDwinP
  obtain ⟨hMkP, hlarge, hAffine⟩ := hData hcard Tker hTker hbudget M Dwin hM hDwin hMT hDwinP
  refine ⟨hMkP, hlarge, ?_⟩
  exact allocatedAccurateAffineData_normalized B U b hR hσ S hP hE hPBase hNumBase
    hmNorm hdimNorm hG hlate hF hnum (hT.trans (le_max_left _ _)) hKsite hKnorm hnorm
    witnesses M Dwin hM hDwin hMkP hlarge hAffine

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

def AllocatedCommonPrimitiveAffineAt (p Psp E e t : ℝ) (hP : 0 ≤ Psp) (δ : ℝ≥0)
    (A Ksize : ℕ) : Prop :=
  let Epoint := E + 1
  ∀ {c : ℝ}, 0 ≤ c →
    ∀ {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j),
    (∀ j, σ j ≤ t) → (∀ j, R j ≤ allocatedSourceCoverRadius m p p) →
    (∀ j, (R j)⁻¹ ≤ Real.exp c) → (∀ j, (σ j)⁻¹ ≤ Real.exp c) →
    let Eraw := Epoint + 1 + 4
    let Esite := allocatedOriginalCoverAccuracy Psp (Epoint + 1)
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
      ∀ (_hcard : dim * (dim + 2) ≤ Fintype.card G) [Nonempty (Fin dim)]
        (Tker : ℝ) (_hTker : 0 ≤ Tker)
        (_hbudget : allocatedKernelPrimitiveBudget p E Tker ≤ Psp)
        (M Dwin : ℕ) (hM : 0 < M) (hDwin : 0 < Dwin)
        (_hMT : (M : ℝ) ≤ Real.exp Tker) (_hDwinP : (Dwin : ℝ) ≤ Real.exp p),
      ∃ hMkPsp : (scalarKernelCutoff (Fin dim) G M Dwin (Real.exp (-(E + 1))) : ℝ) ≤ Real.exp Psp,
      ∃ hlarge : scalarKernelCutoff (Fin dim) G M Dwin (Real.exp (-(E + 1))) ≤ S.value,
        AllocatedPrimitiveAffineData.{uG,uI,uB,uJ,uQ,uX}
          B U b hR hσ S p c Psp E e pNum Pbase (allocatedSourceSamplingBudget m dim A Pbase (Epoint + 1) lateLog F)
          p₁ hP δ A Ksize witnesses L Cc M Dwin hM hDwin hMkPsp hlarge

theorem allocatedCommonNormalizedAffineAt_primitive
    {p P E e t : ℝ} (hp : 0 ≤ p) (hP : 0 ≤ P)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    {δ : ℝ≥0} {A T Kproj Kideal Ksite Ksize : ℕ}
    (hsize : ∀ {c : ℝ}, 0 ≤ c →
      (allocatedCommonCoverParameter (G := G) B dim A (max T (max Kproj Kideal)) p c P e (E + 1)
        + Ksite) ^ Ksite ≤ (p + c + P + E + Ksize) ^ Ksize)
    (hsource : AllocatedCommonNormalizedAffineAt.{uG,uI,uB,uJ,uQ,uX}
      (G := G) (dim := dim) B p P E e t hP δ A T Kproj Kideal Ksite) :
    AllocatedCommonPrimitiveAffineAt.{uG,uI,uB,uJ,uQ,uX}
      (G := G) (dim := dim) B p P E e t hP δ A Ksize := by
  unfold AllocatedCommonPrimitiveAffineAt
  intro Epoint c hc J _ U b R σ hR hσ hσt hRsmall hRi hσi
  have hR1 := fun j => (hRsmall j).trans (allocatedSourceCoverRadius_bounds (m := m) hp hp).2.2.1
  obtain ⟨witnesses, hFamily, hData⟩ := hsource hc U b hR hσ hσt hR1 hRi hσi
  refine ⟨witnesses, hFamily, ?_⟩
  intro hcard _ Tker hTker hbudget M Dwin hM hDwin hMT hDwinP
  obtain ⟨hMkP, hlarge, hData⟩ := hData hcard Tker hTker hbudget M Dwin hM hDwin hMT hDwinP
  refine ⟨hMkP, hlarge, ?_⟩
  exact allocatedNormalizedAffineData_primitive B U b hR hσ _ hp hP hvars hI hn hRsmall
    witnesses M Dwin hM hDwin hMkP hlarge (hsize hc) hData

end Erdos3.VectorPolynomial

end

end OAI
