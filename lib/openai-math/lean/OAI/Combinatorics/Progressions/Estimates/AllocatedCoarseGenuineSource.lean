import OAI.Combinatorics.Progressions.Dynamics.AllocatedBudgetedGenuineSource
import OAI.Combinatorics.Progressions.Estimates.AllocatedFixedCommonCover

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
theorem allocated_product_source_early_coarse_comparison
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
    (hδ : δ ≤ allocatedSitePrimitiveTolerance m pAccuracy w v (allocatedOriginalCoverAccuracy Psp (E + 2)))
    (hEbudget : allocatedOriginalCoverAccuracy Psp (E + 2) + 4 ≤ pAccuracy)
    (hmaskLog : allocatedSiteKernelMaskLog m Psp ≤ w)
    (hidealLog : allocatedIdealProfileLog m pAccuracy e ≤ v) :
  let shiftSize := allocatedOriginalCoverMesh m Psp pAccuracy w v (E + 2)
  ∀ (sourceMesh : ℝ), 0 < sourceMesh →
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
    (_hgeometry : allocatedSeparatedGeometryLog m Psp pAccuracy pSampling w v (E + 2) ≤ P₀)
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
    let coarse := allocatedProductCoarseMesh m X selection M modulus Psp pAccuracy w v (E + 2)
    let mesh := min (min sourceMesh coarse) shiftSize
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
      N hW coarse base cells test
    let hN : ∀ t, 0 < N t := fun t => Nat.cast_pos.mp ((Real.exp_pos _).trans_le (hsize t))
    ‖allocatedOriginalTupleSource B U b hR hσ S x X stride hb o N hN hW hρ hξ
        base cells hmass test Z p hmp -
      allocatedWholeIdealReference (τ := ρ) (ξ := ξ)
        B U b hR hσ S x
        (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) (j.val + 1) → Finset (Fin dim)))
        X hM selection hx modulus stride longReference hb o bW d
        N hW mesh base cells (physicalCubeEuclideanSample U d p hmp) test Z δideal‖ ≤ Real.exp (-(E + 2)) →
    ‖allocatedOriginalTupleSource B U b hR hσ S x X stride hb o N hN hW hρ hξ
        base cells hmass test Z p hmp -
      (law.fiberLaw (principalResidueLabel refined)).complexMean (fun r =>
        ∑ a : cells, (selectedResidueCellWeight stride cells V₀ a : ℂ) *
          ∑ v ∈ spatialWindow H 4, weight r a v * target r (point (reconstruct r a.val v))) / (Z : ℂ)‖ ≤
      Real.exp (-E) := by
  intro shiftSize sourceMesh hsourceMesh K hK hSampling δideal hδideal hδideal1 hδe hRi f
    x hb o Q _ bW d _ _ hσ1 Cinv hCinv hchartinv hsmall hperiod C V hC hV hCexp hVexp P₀ hP₀ hn hdim hbudget hgeometry
    _ _ _ μ _ _ ν _ _ p hp hmp R₁ S₀ ρ hS hSP hρ hρP hstride N hsize hrank hR₁
    W hW D hD hWD H point law target reference base cells ξ hξ V₀ hmass M hM hMP selection hx
    coarse mesh hroot hspatial longReference href test htest Z hZ hZi reconstruct weight hN hsource
  have hE1 : 0 ≤ E + 1 := by linarith only [hE]
  have htwo : (E + 1) + 1 = E + 2 := by ring
  have hδ' : δ ≤ allocatedSitePrimitiveTolerance m pAccuracy w v
      (allocatedOriginalCoverAccuracy Psp ((E + 1) + 1)) := by simpa only [htwo] using hδ
  have hEbudget' : allocatedOriginalCoverAccuracy Psp ((E + 1) + 1) + 4 ≤ pAccuracy := by
    simpa only [htwo] using hEbudget
  have hgeometry' : allocatedSeparatedGeometryLog m Psp pAccuracy pSampling w v ((E + 1) + 1) ≤ P₀ := by
    simpa only [htwo] using hgeometry
  have hcoarsePrevious := allocated_product_primitive_coarse_comparison B U b hR hσ S stride hs modulus δ
    witnesses hWitness hpAccuracy hAccuracySampling hw hv he hE1 hPsp hdimSp hGsp hXsp hperiodSp hdimSmall
    hvars hI hn₁ hJ M₀ hqM hM₀ hS₁ hδ' hEbudget' hmaskLog hidealLog (K := K)
  have hcoarseData := @hcoarsePrevious hK hSampling x hb o Q _ bW d _ _ δideal hδideal hδideal1 hδe hRi
    hσ1 Cinv hCinv hchartinv hsmall hperiod C V hC hV hCexp hVexp
    P₀ hP₀ hn hdim hbudget hgeometry' _ _ _ μ _ _ ν _ _ p hp hmp R₁ S₀ ρ
    hS hSP hρ hρP hstride N hsize hrank hR₁ W hW D hD hWD
    base cells ξ hξ hmass M hM hMP selection hx hroot hspatial Z hZ hZi
  dsimp only at hcoarseData
  simp only [htwo] at hcoarseData
  have hcoarse : 0 < coarse := hcoarseData.1
  have hsourceCoarse : 0 < min sourceMesh coarse := lt_min hsourceMesh hcoarse
  have hshift : 0 < shiftSize :=
    (allocatedOriginalCoverMesh_spec m hPsp hpAccuracy hw hv (by linarith : 0 ≤ E + 2)).1
  have hmesh : 0 < mesh := lt_min hsourceCoarse hshift
  have hmeshCoarse : mesh ≤ coarse := (min_le_left _ _).trans (min_le_right _ _)
  have hcoarseBound := hcoarseData.2.2 mesh hmesh hmeshCoarse test htest
  have hprevious := allocated_product_source_separated_exponential_comparison B U b hR hσ S stride hs modulus δ
    witnesses hWitness hpAccuracy hAccuracySampling hw hv he hE1 hPsp hdimSp hGsp hXsp hperiodSp hdimSmall
    hvars hI hn₁ hJ M₀ hqM hM₀ hS₁ hδ' hEbudget' hmaskLog hidealLog
  have hsource' : ‖allocatedOriginalTupleSource B U b hR hσ S x X stride hb o N hN hW hρ hξ
        base cells hmass test Z p hmp -
      allocatedWholeIdealReference (τ := ρ) (ξ := ξ) B U b hR hσ S x
        (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) (j.val + 1) → Finset (Fin dim)))
        X hM selection hx modulus stride longReference hb o bW d
        N hW (min (min sourceMesh coarse) (allocatedOriginalCoverMesh m Psp pAccuracy w v ((E + 1) + 1)))
        base cells (physicalCubeEuclideanSample U d p hmp) test Z δideal‖ ≤ Real.exp (-((E + 1) + 1)) := by
    simpa only [htwo] using hsource
  have hsourceBound := @hprevious (min sourceMesh coarse) hsourceCoarse K hK hSampling
    δideal hδideal hδideal1 hδe hRi x hb o Q _ bW d _ _ hσ1 Cinv hCinv hchartinv hsmall
    hperiod C V hC hV hCexp hVexp P₀ hP₀ hn hdim hbudget hgeometry' _ _ _ μ _ _ ν _ _
    p hp hmp R₁ S₀ ρ hS hSP hρ hρP hstride N hsize hrank hR₁ W hW D hD hWD
    base cells ξ hξ hmass M hM hMP selection hx hroot hspatial longReference href test htest Z hZ hZi hsource'
  dsimp only at hsourceBound hcoarseBound
  simp only [htwo] at hsourceBound
  have hsum : Real.exp (-(E + 1)) + Real.exp (-(E + 1)) ≤ Real.exp (-E) := by
    calc
      _ = 2 * Real.exp (-(E + 1)) := by ring
      _ ≤ Real.exp 1 * Real.exp (-(E + 1)) := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  exact ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hsourceBound hcoarseBound)).trans hsum

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

def AllocatedProductCoarseContract
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (pAccuracy pSampling w v e E Psp : ℝ) : Prop :=
  let shiftSize := allocatedOriginalCoverMesh m Psp pAccuracy w v (E + 2)
  ∀ (sourceMesh : ℝ), 0 < sourceMesh →
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
    (_hgeometry : allocatedSeparatedGeometryLog m Psp pAccuracy pSampling w v (E + 2) ≤ P₀)
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
    let coarse := allocatedProductCoarseMesh m X selection M modulus Psp pAccuracy w v (E + 2)
    let mesh := min (min sourceMesh coarse) shiftSize
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
      N hW coarse base cells test
    let hN : ∀ t, 0 < N t := fun t => Nat.cast_pos.mp ((Real.exp_pos _).trans_le (hsize t))
    ‖allocatedOriginalTupleSource B U b hR hσ S x X stride hb o N hN hW hρ hξ
        base cells hmass test Z p hmp -
      allocatedWholeIdealReference (τ := ρ) (ξ := ξ)
        B U b hR hσ S x
        (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) (j.val + 1) → Finset (Fin dim)))
        X hM selection hx modulus stride longReference hb o bW d
        N hW mesh base cells (physicalCubeEuclideanSample U d p hmp) test Z δideal‖ ≤ Real.exp (-(E + 2)) →
    ‖allocatedOriginalTupleSource B U b hR hσ S x X stride hb o N hN hW hρ hξ
        base cells hmass test Z p hmp -
      (law.fiberLaw (principalResidueLabel refined)).complexMean (fun r =>
        ∑ a : cells, (selectedResidueCellWeight stride cells V₀ a : ℂ) *
          ∑ v ∈ spatialWindow H 4, weight r a v * target r (point (reconstruct r a.val v))) / (Z : ℂ)‖ ≤
      Real.exp (-E)

include hWitness hs in
theorem allocatedProductCoarseContract_of_sampling
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
    (hδ : δ ≤ allocatedSitePrimitiveTolerance m pAccuracy w v (allocatedOriginalCoverAccuracy Psp (E + 2)))
    (hEbudget : allocatedOriginalCoverAccuracy Psp (E + 2) + 4 ≤ pAccuracy)
    (hmaskLog : allocatedSiteKernelMaskLog m Psp ≤ w)
    (hidealLog : allocatedIdealProfileLog m pAccuracy e ≤ v)
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))) :
    AllocatedProductCoarseContract.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ S stride modulus witnesses o pAccuracy pSampling w v e E Psp := by
  have hprevious := allocated_product_source_early_coarse_comparison B U b hR hσ S stride hs modulus δ
    witnesses hWitness hpAccuracy hAccuracySampling hw hv he hE hPsp hdimSp hGsp hXsp hperiodSp hdimSmall
    hvars hI hn₁ hJ M₀ hqM hM₀ hS₁ hδ hEbudget hmaskLog hidealLog
  unfold AllocatedProductCoarseContract
  intro shiftSize sourceMesh hsourceMesh K hK hSampling δideal hδideal hδideal1 hδe hRi f x hb Q instQ
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

theorem allocatedProductCoarseMesh_pos (m : ℕ) {dim : ℕ}
    {G : Type*} [Fintype G] (X : Type*) [Fintype X]
    (selection : Fin dim ↪ G) (M modulus : ℕ) (P pAccuracy w v E : ℝ) :
    0 < allocatedProductCoarseMesh m X selection M modulus P pAccuracy w v E := by
  have hκ : 0 ≤ 1 / (M : ℝ) := by positivity
  have hcap := anisotropicSpatialDensityCap_nonneg selection hκ
  have hlip := anisotropicSpatialDensityLip_nonneg selection hκ
  exact (spatialTupleCoarseMesh_spec (Fintype.card X)
    (mul_nonneg (pow_nonneg (Nat.cast_nonneg modulus) _) hcap)
    (Real.exp_pos (allocatedOriginalMassLog m P pAccuracy w v + 1)).le
    (mul_nonneg (pow_nonneg (Nat.cast_nonneg modulus) _)
      (mul_nonneg hlip (allocatedPrimitiveRootRatio (Real.exp P)).coe_nonneg)) (Real.exp_pos (-E))).1

def AllocatedProductCoarseRawData (Psp E e pNum Pbase Qraw pAccuracy pSampling : ℝ) (hP : 0 ≤ Psp)
    (δ : ℝ≥0) (A Kraw Ksite : ℕ)
    (witnesses : (q : AllocatedRefinedPeriodIndex m Psp) →
      (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
      AllocatedFullGridResidueWitness (dim := dim) B U b S (q.val : ℕ) r.val) : Prop :=
  let w := allocatedSiteKernelMaskLog m Psp
  let v := allocatedIdealProfileLog m pAccuracy e
  let Pfinal := sourceCoverParameter dim Kraw Psp pNum Qraw
    (allocatedSiteErrorFourierOutput m pSampling w v)
    (allocatedSeparatedGeometryLog m Psp pAccuracy pSampling w v (E + 2))
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
    let ξ := normalizedTupleNarrowWidth X indices selection Mk Psp ((E + 2) + 2)
    let hξ := normalizedTupleNarrowWidth_pos X indices selection Mk Psp ((E + 2) + 2)
    let mesh := allocatedProductCoarseMesh m X selection Mk modulus Psp pAccuracy w v (E + 2)
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

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

def AllocatedProductCoarseUniformSourceContract
    (S : LayerSamplerScale (G := G) B U b R σ) (Psp E e pAccuracy pSampling : ℝ) (hPsp : 0 ≤ Psp)
    (witnesses : (q : AllocatedRefinedPeriodIndex m Psp) →
      (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
      AllocatedFullGridResidueWitness (dim := dim) B U b S (q.val : ℕ) r.val) : Prop :=
  ∀ (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {X : Type uX} [Fintype X] [DecidableEq X] {M modulus : ℕ}
    (hM : (M : ℝ) ≤ Real.exp Psp) (hmodulus : modulus ≤ M ^ (m + 1))
    (hX : (Fintype.card X : ℝ) ≤ Psp) (hmodulusPos : 0 < modulus)
    (stride : X → ℕ) (hs : ∀ t, 0 < stride t)
    (hstride : ∀ t, (stride t : ℝ) ≤ Real.exp Psp),
    let index := allocatedRefinedPeriodIndex m hPsp hM hmodulus hX hmodulusPos stride hs hstride
    let _ : NeZero modulus := ⟨hmodulusPos.ne'⟩
    let _ : NeZero (residueRefinedPeriod modulus stride) :=
      ⟨(residueRefinedPeriod_pos hmodulusPos stride hs).ne'⟩
    AllocatedProductCoarseContract.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ S stride modulus (witnesses index) o pAccuracy pSampling
      (allocatedSiteKernelMaskLog m Psp) (allocatedIdealProfileLog m pAccuracy e) e E Psp

theorem allocatedProductCoarseRawData_of_source
    (S : LayerSamplerScale (G := G) B U b R σ)
    {Psp E e pNum pAccuracy pSampling Pbase Qraw : ℝ} {δ : ℝ≥0} {A Kraw Ksite : ℕ}
    (hPsp : 0 ≤ Psp) (hE : 0 ≤ E) (he : 0 ≤ e) (hpAccuracy : 0 ≤ pAccuracy)
    (hvarsGrowth : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp Psp)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp pAccuracy)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδe : (δ : ℝ)⁻¹ ≤ Real.exp e) (hKsite : 2 ≤ Ksite)
    (hSampling : AllocatedBooleanRowsSampling.{uX,uJ,uG,uI,uB,uQ}
      m dim Ksite rowTypes rows)
    (hraw : AllocatedRawSourceData.{uG,uI,uB,uJ,uQ,uX}
      (dim := dim) B U b hR hσ S Psp (E + 2) pNum Pbase Qraw δ A Kraw) :
    ∀ (witnesses : (q : AllocatedRefinedPeriodIndex m Psp) →
        (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
        AllocatedFullGridResidueWitness (dim := dim) B U b S (q.val : ℕ) r.val),
      AllocatedProductCoarseUniformSourceContract.{uG,uI,uB,uJ,uQ,uX} B U b hR hσ S Psp E e pAccuracy pSampling hPsp witnesses →
      AllocatedProductCoarseRawData.{uG,uI,uB,uJ,uQ,uX}
        B U b hR hσ S Psp E e pNum Pbase Qraw pAccuracy pSampling hPsp δ A Kraw Ksite witnesses := by
  intro witnesses hContracts
  unfold AllocatedProductCoarseRawData
  intro w v Pfinal
  obtain ⟨hPfinal, hPfinalSp, hdimFinal, hpNumFinal, _, hFourier, hGeometry⟩ :=
    sourceCoverParameter_bounds dim Kraw (pNum := pNum) (Qraw := Qraw)
      (F := allocatedSiteErrorFourierOutput m pSampling w v)
      (G := allocatedSeparatedGeometryLog m Psp pAccuracy pSampling w v (E + 2)) hPsp
  have hSourceCut : Real.exp ((Qraw + Kraw) ^ Kraw) ≤ Real.exp ((Pfinal + Ksite) ^ Ksite) :=
    sourceCoverParameter_threshold dim Kraw hPsp (by omega)
  intro x Mk hMk selection hx hqDim hMkPsp
  obtain ⟨d, hd, hdb, hraw⟩ := hraw x hMk selection hx hqDim hMkPsp
  let : NeZero d := ⟨hd.ne'⟩
  refine ⟨d, hd, hdb, ?_⟩
  intro modulus hmodulus
  let : NeZero modulus := ⟨hmodulus.ne'⟩
  intro _ hmodulusSize hspatialPeriod hcoefficientPeriod
  obtain ⟨s, hA, hinverse, hraw⟩ := hraw modulus hmodulus
    hmodulusSize hspatialPeriod hcoefficientPeriod
  refine ⟨s, hA, hinverse, ?_⟩
  intro block iLattice _ _ _ _ _ hb o Kcov iKcov bW C V hC hV hCp hVp hCpAccuracy hVpAccuracy Cinv hCinv hchart hsmall hσ1 hproductSmall μ _ _ ν iInvNu iProbNu
    iCompactSmall iMeasSmall iBorelSmall μsmall iInvSmall iProbSmall X _ _ hXPsp q hq hqPsp refined index
  obtain ⟨hRefined, hdiv, hRefinedBound, hsize, reference, residue, href, hresidue, hraw⟩ :=
    hraw block hb o bW C V hC hV hCp hVp Cinv hCinv hchart hsmall μ ν hXPsp q hq hqPsp
  let : NeZero (residueRefinedPeriod modulus q) := ⟨hRefined.ne'⟩
  refine ⟨hRefined, hdiv, hRefinedBound, hsize, reference, residue, href, hresidue, ?_⟩
  intro W hW indices ξ hξ mesh τ hτ hτP N hN hsizeN poly hpoly hmem
    rank hrank hRank base cells hcells test htest Z hZ V₀ H point law target wholeReference reconstruct weight
  let sourceMesh := normalizedTupleRadius X selection Mk Psp ((E + 2) + 2) W / 4
  have hsourceMesh : 0 < sourceMesh := by
    have ht : 0 < normalizedTupleTolerance X Psp ((E + 2) + 2) :=
      (spatialTupleTolerance_spec (Fintype.card X) (Real.exp_nonneg _)
        (Real.exp_nonneg _) (half_pos (Real.exp_pos _))).1
    have hLip := anisotropicSpatialDensityLip_nonneg selection (show 0 ≤ 1 / (Mk : ℝ) by positivity)
    exact div_pos (twoTermErrorWidth_spec (by positivity) ht).1 (by norm_num)
  have hw : 0 ≤ w := allocatedSiteKernelMaskLog_nonneg m hPsp
  have hv : 0 ≤ v := allocatedIdealProfileLog_nonneg m hpAccuracy he
  have hcoverMesh := (allocatedOriginalCoverMesh_spec m hPsp hpAccuracy hw hv (by linarith : 0 ≤ E + 2)).1
  have hmesh : 0 < mesh := allocatedProductCoarseMesh_pos m X selection Mk modulus
    Psp pAccuracy w v (E + 2)
  let fine := min (min sourceMesh mesh) (allocatedOriginalCoverMesh m Psp pAccuracy w v (E + 2))
  have hfine : 0 < fine := lt_min (lt_min hsourceMesh hmesh) hcoverMesh
  have hfineSource : fine ≤ sourceMesh := (min_le_left _ _).trans (min_le_left _ _)
  obtain ⟨hmass, hsource⟩ := hraw fine hfine hfineSource hτ hτP N hN
    (fun t => hSourceCut.trans (hsizeN t)) poly hpoly hmem hrank
    (hSourceCut.trans hRank) base cells hcells test htest Z hZ
  refine ⟨hmass, ?_⟩
  have hXFinal : (Fintype.card X : ℝ) ≤ Pfinal := hXPsp.trans hPfinalSp
  have hdimJoined : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ Pfinal := by
    apply le_trans _ hdimFinal
    simpa only [Fintype.card_prod, Fintype.card_option, Fintype.card_fin, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one] using
      mul_le_mul_of_nonneg_left hXPsp (Nat.cast_nonneg (dim + 1))
  let Prows (O : Fin m → Type) [∀ j, Fintype (O j)] (values : ∀ j, O j → Finset (Fin dim)) : Prop :=
    ∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (values j)).mulVecLin.range
  have hperiod : Prows rowTypes rows :=
    boundedBooleanJetRows_family_transport (fun j : Fin m => j.val + 1) Prows hcoefficientPeriod
      (fun j => fullBooleanRowSetFintype dim (j.val + 1))
  have hWscale : W ≤ (Fintype.card (LayerSamplerVariables G I n B) : ℝ) * S.value := by
    simp only [W, allocatedPhysicalRootBudget, Int.cast_zero, abs_zero, Finset.sum_const_zero, zero_add, le_refl]
  have hZpos : 0 < Z := lt_of_lt_of_le (by norm_num) hZ
  have hZi : Z⁻¹ ≤ 2 := (inv_le_iff_one_le_mul₀ hZpos).2 (by linarith)
  have hcontract := hContracts o hMkPsp hmodulusSize hXPsp hmodulus q hq hqPsp
  exact @hcontract sourceMesh hsourceMesh Ksite hKsite (@hSampling) δ hδ hδ1 hδe hRi
    x hb Kcov iKcov bW d inferInstance iLattice hσ1 Cinv hCinv hchart hproductSmall hperiod C V hC hV
    hCpAccuracy hVpAccuracy
    Pfinal (zero_le_one.trans hPfinal) hXFinal hdimJoined hFourier hGeometry
    iCompactSmall iMeasSmall iBorelSmall μsmall iInvSmall iProbSmall ν iInvNu iProbNu poly hpoly hmem
    rank (Real.exp Psp) τ
    (Real.exp_nonneg Psp) (Real.exp_le_exp.mpr hPfinalSp) hτ
    (hτP.trans (Real.exp_le_exp.mpr hpNumFinal)) hqPsp N hsizeN hrank hRank W hW
    (Fintype.card (LayerSamplerVariables G I n B) : ℝ) hvarsGrowth hWscale
    base cells ξ hξ hmass Mk hMk hMkPsp selection hx le_rfl
    (hspatialPeriod (fun g => (0 : ℤ) + (x g none : ℤ))) reference href
    (physicalCubeSiteTest test) (physicalCubeSiteTest_norm_le test htest) Z hZpos hZi hsource

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
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
variable {Psp E e pAccuracy pSampling : ℝ}

local notation "maskLog" => allocatedSiteKernelMaskLog m Psp
local notation "profileLog" => allocatedIdealProfileLog m pAccuracy e
local notation "accuracy" => allocatedOriginalCoverAccuracy Psp (E + 2)
local notation "tolerance" => allocatedSitePrimitiveTolerance m pAccuracy maskLog profileLog accuracy
local notation "cutoff" => allocatedRefinedPeriodCutoff m Psp

theorem allocatedProductCoarseUniformSourceContract_of_sampling
    (hPsp : 0 ≤ Psp) (hE : 0 ≤ E) (he : 0 ≤ e) (hpAccuracy : 0 ≤ pAccuracy)
    (hAccuracySampling : pAccuracy ≤ pSampling)
    (hmP : ((m + 1 : ℕ) : ℝ) ≤ Psp) (hdimSp : ((dim + 1 : ℕ) : ℝ) ≤ Psp)
    (hGsp : (Fintype.card G : ℝ) ≤ Psp) (hdimSmall : dim ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pAccuracy)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ pAccuracy) (hn : ∀ j, (n j : ℝ) ≤ pAccuracy)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ pAccuracy)
    (hcutoff : (cutoff : ℝ) ≤ Real.exp pAccuracy) (hS : (S.value : ℝ) ≤ Real.exp pSampling)
    (hEbudget : accuracy + 4 ≤ pAccuracy)
    (witnesses : (q : AllocatedRefinedPeriodIndex m Psp) →
      (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
      AllocatedFullGridResidueWitness (dim := dim) B U b S (q.val : ℕ) r.val)
    (hWitness : ∀ q r, AllocatedFullGridResidueSampling.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ S (q.val : ℕ) (witnesses q r) tolerance) :
    AllocatedProductCoarseUniformSourceContract.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ S Psp E e pAccuracy pSampling hPsp witnesses := by
  unfold AllocatedProductCoarseUniformSourceContract
  intro o X _ _ M modulus hM hmodulus hX hmodulusPos stride hs hstride index _ _
  have hperiodSp : (modulus : ℝ) ≤ Real.exp (Psp ^ 2) := by
    calc
      _ ≤ (M : ℝ) ^ (m + 1) := by exact_mod_cast hmodulus
      _ ≤ (Real.exp Psp) ^ (m + 1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hM _
      _ = Real.exp ((m + 1 : ℕ) * Psp) := (Real.exp_nat_mul Psp (m + 1)).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hmP hPsp])
  have hqM : residueRefinedPeriod modulus stride ≤ cutoff ^ (m + 1) :=
    allocatedRefinedPeriodIndex_power m hPsp index
  exact allocatedProductCoarseContract_of_sampling B U b hR hσ S stride hs modulus tolerance
    (witnesses index) (hWitness index) hpAccuracy hAccuracySampling (allocatedSiteKernelMaskLog_nonneg m hPsp)
    (allocatedIdealProfileLog_nonneg m hpAccuracy he) he hE hPsp hdimSp hGsp hX hperiodSp hdimSmall
    hvars hI hn hJ cutoff hqM hcutoff hS le_rfl hEbudget le_rfl le_rfl o

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
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
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

theorem exists_allocated_early_product_coarse_family
    {Psp p e E : ℝ} (hPsp : 0 ≤ Psp) (hp : 0 ≤ p) (he : 0 ≤ e) (hE : 0 ≤ E)
    (hmP : ((m + 1 : ℕ) : ℝ) ≤ Psp) (hdimSp : ((dim + 1 : ℕ) : ℝ) ≤ Psp)
    (hGsp : (Fintype.card G : ℝ) ≤ Psp) (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (hEbudget : allocatedOriginalCoverAccuracy Psp (E + 2) + 4 ≤ p)
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
    let w := allocatedSiteKernelMaskLog m Psp
    let v := allocatedIdealProfileLog m p e
    let accuracy := allocatedOriginalCoverAccuracy Psp (E + 2)
    let O := allocatedFullGridPrimitiveResourceLog m p w v accuracy
    ∃ witnesses : (q : AllocatedRefinedPeriodIndex m Psp) →
        (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
        AllocatedFullGridResidueWitness (dim := dim) B U b S (q.val : ℕ) r.val,
      (∀ q r a, ((witnesses q r).expansion a).Bounds (Real.exp O) (Real.exp O) (Real.exp O)
        ⟨Real.exp O, Real.exp_nonneg _⟩
        (Real.exp (allocatedInactiveSupportLog (allocatedComparisonDimension m p)))) ∧
      (∀ q r, AllocatedFullGridResidueSampling.{uG,uI,uB,uJ,uQ,uX}
        B U b hR hσ S (q.val : ℕ) (witnesses q r) (allocatedSitePrimitiveTolerance m p w v accuracy)) ∧
      ∀ (pSampling : ℝ), p ≤ pSampling → (S.value : ℝ) ≤ Real.exp pSampling →
        AllocatedProductCoarseUniformSourceContract.{uG,uI,uB,uJ,uQ,uX}
          B U b hR hσ S Psp E e p pSampling hPsp witnesses := by
  intro w v accuracy O
  have hw : 0 ≤ w := allocatedSiteKernelMaskLog_nonneg m hPsp
  have hv : 0 ≤ v := allocatedIdealProfileLog_nonneg m hp he
  have haccuracy : 0 ≤ accuracy := by
    have hsp := coefficientErrorSpatialLog_nonneg hPsp
    dsimp only [accuracy, allocatedOriginalCoverAccuracy]
    linarith
  obtain ⟨witnesses, hBounds, hSampling⟩ := exists_allocated_early_full_grid_family
    B U b hR hσ S hPsp hp hw hv haccuracy hα hvars hI hn hcutoff hsize hgamma hσ1 L hL hcP hsP hB
  refine ⟨witnesses, hBounds, hSampling, ?_⟩
  intro pSampling hEarlyLate hS
  exact allocatedProductCoarseUniformSourceContract_of_sampling
    B U b hR hσ S hPsp hE he hp hEarlyLate hmP hdimSp hGsp
    (by simpa only [Fintype.card_fin] using hα) hvars hI hn hJ hcutoff hS hEbudget witnesses hSampling

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq

variable {m dim : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {p cEarly cLate P e Eraw E : ℝ}

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "accuracy" => allocatedOriginalCoverAccuracy P (E + 2)
local notation "pAccuracy" => allocatedCommonRefinedSourceLog m p cEarly P e 0 accuracy
local notation "pSampling" => allocatedCommonRefinedSourceLog m p cLate P e Eraw accuracy
local notation "S" => allocatedCommonScale (G := G) B U b hR hσ p cLate P e Eraw
local notation "maskLog" => allocatedSiteKernelMaskLog m P
local notation "profileLog" => allocatedIdealProfileLog m pAccuracy e
local notation "resourceLog" => allocatedFullGridPrimitiveResourceLog m pAccuracy maskLog profileLog accuracy
local notation "tolerance" => allocatedSitePrimitiveTolerance m pAccuracy maskLog profileLog accuracy

theorem exists_original_common_early_coarse_source
    (hp : 0 ≤ p) (hcEarly : 0 ≤ cEarly) (hcLate : 0 ≤ cLate) (hEarlyLate : cEarly ≤ cLate)
    (hP : 0 ≤ P) (he : 0 ≤ e) (hEraw : 0 ≤ Eraw) (hE : 0 ≤ E)
    (hdimSmall : dim ≤ m + 1) (hmP : ((m + 2 : ℕ) : ℝ) ≤ P) (hpP : p ≤ P)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ 2 * p)
    (hR1 : ∀ j, R j ≤ 1) (hσ1 : ∀ j, σ j ≤ 1)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp cEarly) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp cLate)
    (hBlocks : ∀ (j : Fin m) (i : Fin (n j)), max
      (positiveModerateSpectrumBlockCount j.val (rowSets j).card
        ((layerTailDegree m + 2) * (rowSets j).card))
      (uniformSpectrumBlockCount j.val (rowSets j).card ((j.val + 1) * (rowSets j).card)) ≤
      Fintype.card (B ⟨j, Sum.inr i⟩)) :
    ∃ witnesses : (q : AllocatedRefinedPeriodIndex m P) →
        (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
        AllocatedFullGridResidueWitness (dim := dim) B U b S (q.val : ℕ) r.val,
      (∀ q r a, ((witnesses q r).expansion a).Bounds
        (Real.exp resourceLog) (Real.exp resourceLog) (Real.exp resourceLog)
        ⟨Real.exp resourceLog, Real.exp_nonneg _⟩
        (Real.exp (allocatedInactiveSupportLog (allocatedComparisonDimension m pAccuracy)))) ∧
      (∀ q r, AllocatedFullGridResidueSampling.{uG,uI,uB,uJ,uQ,uX}
        B U b hR hσ S (q.val : ℕ) (witnesses q r) tolerance) ∧
      AllocatedProductCoarseUniformSourceContract.{uG,uI,uB,uJ,uQ,uX}
        B U b hR hσ S P E e pAccuracy pSampling hP witnesses := by
  have hAccuracy : 0 ≤ accuracy := by
    have hsp := coefficientErrorSpatialLog_nonneg hP
    unfold allocatedOriginalCoverAccuracy
    linarith
  obtain ⟨hpAccuracy, hpBound, htwoP, _, _, hEbudget, hcutoffLog, hsourceLog, _, _, _⟩ :=
    allocatedCommonRefinedSourceLog_bounds m hp hcEarly hP he (by norm_num : (0 : ℝ) ≤ 0) hAccuracy
  have hcutoff : (allocatedRefinedPeriodCutoff m P : ℝ) ≤ Real.exp pAccuracy :=
    (allocatedRefinedPeriodCutoff_bounds m hP).2.trans (Real.exp_le_exp.mpr hcutoffLog)
  have hcutoffNonneg : 0 ≤ allocatedRefinedPeriodLog m P + 1 := by
    unfold allocatedRefinedPeriodLog
    positivity
  have hEnvelope : canonicalScalarSourceEnvelope m (allocatedRefinedPeriodCutoff m P) ≤
      Real.exp pAccuracy :=
    (canonicalScalarSourceEnvelope_le_exp m hcutoffNonneg
      (allocatedRefinedPeriodCutoff_bounds m hP).2).trans (Real.exp_le_exp.mpr hsourceLog)
  obtain ⟨_, hcP, hsources⟩ := canonicalScalarSourceEnvelope_bounds m (allocatedRefinedPeriodCutoff m P)
  have hcutoffPower : allocatedRefinedPeriodCutoff m P ≤ allocatedRefinedPeriodCutoff m P ^ (m + 1) := by
    calc
      _ = allocatedRefinedPeriodCutoff m P ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ (allocatedRefinedPeriodCutoff_bounds m hP).1 (by omega)
  have hsP : scalarCubePrimitiveEnvelope (Fin dim) scalarSourceTransitionBound 1 0
      (allocatedRefinedPeriodCutoff m P) ≤ Real.exp pAccuracy :=
    ((scalarCubePrimitiveEnvelope_mono (Fin dim) scalarSourceTransitionBound
      le_rfl le_rfl hcutoffPower).trans (hsources dim hdimSmall)).trans hEnvelope
  have hdimSp : ((dim + 1 : ℕ) : ℝ) ≤ P :=
    (Nat.cast_le.mpr (show dim + 1 ≤ m + 2 by omega)).trans hmP
  have hmOne : ((m + 1 : ℕ) : ℝ) ≤ P :=
    (Nat.cast_le.mpr (show m + 1 ≤ m + 2 by omega)).trans hmP
  have hGsp : (Fintype.card G : ℝ) ≤ P :=
    (Nat.cast_le.mpr (allocatedKernelVariables_card_le_variables (G := G) B)).trans (hvars.trans hpP)
  obtain ⟨witnesses, hBounds, hSampling, hContracts⟩ := exists_allocated_early_product_coarse_family
    B U b hR hσ S hP hpAccuracy he hE hmOne hdimSp hGsp
    (fun j => (hJ j).trans htwoP) hEbudget
    (by simpa only [Fintype.card_fin] using hdimSmall)
    (hvars.trans hpBound) (fun j => (hI j).trans hpBound) (fun j => (hn j).trans hpBound)
    hcutoff (allocatedCommonScale_cutoff_window (G := G) B U b hR hσ hdimSmall hp hcLate hP he hEraw)
    (fun _ => (principalProfileSize_le_radius (hR _).le _).trans (hR1 _))
    (fun _ => hσ1 _) scalarSourceTransitionBound scalarSourceTransitionBound_spec.2
    (hcP.trans hEnvelope) hsP
    (fun a => hBlocks (allocatedGridIntegerAxis B U b S a).1 (allocatedGridIntegerAxis B U b S a).2)
  have hOrder : pAccuracy ≤ pSampling := allocatedCommonRefinedSourceLog_mono m
    hp hcEarly hP he (by norm_num : (0 : ℝ) ≤ 0) le_rfl hEarlyLate le_rfl le_rfl hEraw le_rfl
  have hS : ((LayerSamplerScale.value S) : ℝ) ≤ Real.exp pSampling :=
    original_common_period_scale_upper B U b hR hσ hp hcLate hP he hEraw hAccuracy
      hdimSmall hvars hI hn (fun j => (hRi j).trans (Real.exp_le_exp.mpr hEarlyLate)) hσi
  exact ⟨witnesses, hBounds, hSampling, hContracts pSampling hOrder hS⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq

variable {m dim : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {p cEarly cLate P e E : ℝ}

local notation "Eraw" => (E + 2) + 4

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "accuracy" => allocatedOriginalCoverAccuracy P (E + 2)
local notation "pAccuracy" => allocatedCommonRefinedSourceLog m p cEarly P e 0 accuracy
local notation "pSampling" => allocatedCommonRefinedSourceLog m p cLate P e Eraw accuracy
local notation "S" => allocatedCommonScale (G := G) B U b hR hσ p cLate P e Eraw
local notation "maskLog" => allocatedSiteKernelMaskLog m P
local notation "profileLog" => allocatedIdealProfileLog m pAccuracy e
local notation "resourceLog" => allocatedFullGridPrimitiveResourceLog m pAccuracy maskLog profileLog accuracy
local notation "tolerance" => allocatedSitePrimitiveTolerance m pAccuracy maskLog profileLog accuracy

local notation "D" => allocatedComparisonDimension m p
local notation "pNum" => allocatedCommonScaleNumeric m p cLate P Eraw
local notation "error" => allocatedReferenceIdealError m D P Eraw
local notation "lengthLog" => allocatedIdealScaleLog m D pNum e maskLog error
local notation "gainLog" => allocatedProfileGainLog m D P maskLog
local notation "Pbase" => allocatedIdealSourceBudget m D pNum e maskLog error
local notation "lateLog" => allocatedSpatialLateLog (G := G) B Pbase Pbase
local notation "rawFourier" => allocatedProfileFourierOutput (allocatedActualProfileInput m D pNum e gainLog lengthLog)
local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

theorem exists_original_common_early_coarse_raw_cover
    (hp : 0 ≤ p) (hcEarly : 0 ≤ cEarly) (hcLate : 0 ≤ cLate) (hEarlyLate : cEarly ≤ cLate)
    (hP : 0 ≤ P) (he : 0 ≤ e) (hE : 0 ≤ E)
    (hdimSmall : dim ≤ m + 1) (hmP : ((m + 2 : ℕ) : ℝ) ≤ P) (hpP : p ≤ P)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ 2 * p)
    (hR1 : ∀ j, R j ≤ 1) (hσ1 : ∀ j, σ j ≤ 1)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp cEarly) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp cLate)
    (hBlocks : ∀ (j : Fin m) (i : Fin (n j)), max
      (positiveModerateSpectrumBlockCount j.val (rowSets j).card
        ((layerTailDegree m + 2) * (rowSets j).card))
      (uniformSpectrumBlockCount j.val (rowSets j).card ((j.val + 1) * (rowSets j).card)) ≤
      Fintype.card (B ⟨j, Sum.inr i⟩))
    {δ : ℝ≥0} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδe : (δ : ℝ)⁻¹ ≤ Real.exp e)
    {A T Kproj Kideal Ksite : ℕ} (hKsite : 2 ≤ Ksite)
    (hSampling : AllocatedBooleanRowsSampling.{uX,uJ,uG,uI,uB,uQ} m dim Ksite rowTypes rows)
    (hraw : AllocatedOriginalResidueWeightedMeshAtScale.{uG,uI,uB,uJ,uQ,uX}
      (G := G) (dim := dim) B U b hR hσ D P (E + 2) e pNum δ A T Kproj Kideal) :
    ∃ witnesses : (q : AllocatedRefinedPeriodIndex m P) →
        (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
        AllocatedFullGridResidueWitness (dim := dim) B U b S (q.val : ℕ) r.val,
      (∀ q r a, ((witnesses q r).expansion a).Bounds
        (Real.exp resourceLog) (Real.exp resourceLog) (Real.exp resourceLog)
        ⟨Real.exp resourceLog, Real.exp_nonneg _⟩
        (Real.exp (allocatedInactiveSupportLog (allocatedComparisonDimension m pAccuracy)))) ∧
      (∀ q r, AllocatedFullGridResidueSampling.{uG,uI,uB,uJ,uQ,uX}
        B U b hR hσ S (q.val : ℕ) (witnesses q r) tolerance) ∧
      AllocatedProductCoarseRawData.{uG,uI,uB,uJ,uQ,uX}
        B U b hR hσ S P E e pNum Pbase
        (allocatedSourceSamplingBudget m dim A Pbase (E + 2) lateLog rawFourier)
        pAccuracy pSampling hP δ A (max T (max Kproj Kideal)) Ksite witnesses := by
  have hEraw : 0 ≤ Eraw := by linarith
  have hAccuracy : 0 ≤ accuracy := by
    have hsp := coefficientErrorSpatialLog_nonneg hP
    unfold allocatedOriginalCoverAccuracy
    linarith
  obtain ⟨hpAccuracy, _, _, hcAccuracy, _, _, _, _, _, _, _⟩ :=
    allocatedCommonRefinedSourceLog_bounds m hp hcEarly hP he (by norm_num : (0 : ℝ) ≤ 0) hAccuracy
  obtain ⟨witnesses, hBounds, hWitnesses, hContracts⟩ :=
    exists_original_common_early_coarse_source.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ hp hcEarly hcLate hEarlyLate hP he hEraw hE
      hdimSmall hmP hpP hvars hI hn hJ hR1 hσ1 hRi hσi hBlocks
  refine ⟨witnesses, hBounds, hWitnesses, ?_⟩
  have hvarsGrowth : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp P :=
    (hvars.trans hpP).trans (by linarith [Real.add_one_le_exp P])
  exact allocatedProductCoarseRawData_of_source.{uG,uI,uB,uJ,uQ,uX}
    B U b hR hσ S hP hE he hpAccuracy hvarsGrowth
    (fun j => (hRi j).trans (Real.exp_le_exp.mpr hcAccuracy))
    hδ hδ1 hδe hKsite hSampling (allocatedRawSourceData_of_original B U b hR hσ hraw)
    witnesses hContracts

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq fullBooleanRowSetFintype

theorem allocatedProductCoarseInput_nonneg (m dim : ℕ) {P pAccuracy w v E : ℝ}
    (hP : 0 ≤ P) (hpAccuracy : 0 ≤ pAccuracy) (hw : 0 ≤ w) (hv : 0 ≤ v) (hE : 0 ≤ E) :
    0 ≤ allocatedProductCoarseInput m dim P pAccuracy w v E := by
  have hbase := (allocatedEarlyCoarseInput_bounds m dim (add_nonneg hP hE)).1
  have hsite := allocatedSiteSpatialMassLog_nonneg
    (allocatedComparisonDimension_bounds m hpAccuracy).1 hw hv
  have hmass : 0 ≤ allocatedOriginalMassLog m P pAccuracy w v := by
    unfold allocatedOriginalMassLog coefficientErrorVolumeLog
    positivity
  unfold allocatedProductCoarseInput
  positivity

universe uX uJ

variable {m dim : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (hσ1 : ∀ j, σ j ≤ 1)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type uX) [Fintype X] [DecidableEq X] (modulus : ℕ) [NeZero modulus] (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (coverWitness : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) →
  AllocatedFullGridResidueWitness (dim := dim) B U b S (residueRefinedPeriod modulus q) r.val)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (δ : ℝ≥0) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable {Psp pAccuracy w v Ecoarse : ℝ}
variable (N : X → ℕ) {τ : ℝ} (base : X → ℤ)
local notation "coarseMesh" => allocatedProductCoarseMesh m X selection M modulus Psp pAccuracy w v Ecoarse
local notation "partitionLog" => coarseSpatialPartitionLog
  (allocatedProductCoarseInput m dim Psp pAccuracy w v Ecoarse)
local notation "W" => allocatedPhysicalRootBudget B U b S (fun _ => 0)
local notation "hW" => allocatedPhysicalRootBudget_nonneg B U b S (fun _ => 0)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (hm : ∀ j e, coefficients (p j) e ∈ U j)

local notation "refined" => residueRefinedPeriod modulus q
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
local notation "H" => trimmedSpatialRootScale τ N q
local notation "factor" => ((30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
  (((1 + W) / (S.value : ℝ)) ^ dim) ^ Fintype.card X)
local notation "radius" => allocatedProductIdealSiteRadius (G := G) B rowSets
local notation "positiveRadius" => allocatedProductIdealSiteRadius_pos (G := G) B rowSets
local notation "amp" => ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d radius positiveRadius
local notation "spatialCap" => allocatedSpatialCoefficientCap X selection M modulus coarseMesh
local notation "law" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
local notation "residueLaw" => FiniteProbabilityWeights.fiberLaw (law) (principalResidueLabel refined)
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)
local notation "reconstruct" => allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base

local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "massCap" => (allocatedUniformGridVolumeCap B rowSets radius *
  (2 * ((2 : ℝ) ^ dim * (2 * (radius : ℝ))) + 1) ^
    Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes (Sigma.fst a)))

variable (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable {Dgeom cgeom : ℝ}
variable (hgeom : AllocatedComparisonDimensions (G := G) B (Fin dim)
  (fun j : Fin m => (boundedBooleanJetRows (Fin dim) (Fin.val j + 1) : Type)) Dgeom)
variable (hcgeom : 0 ≤ cgeom)
variable (hIgeom : ∀ j, (Fintype.card (I j) : ℝ) ≤ Dgeom)
variable (hngeom : ∀ j, (n j : ℝ) ≤ Dgeom)
variable (hCgeom : ∀ j, C j ≤ Real.exp cgeom)
variable (hsmall : ∀ j, R j ≤ allocatedProductChartRadius m Dgeom cgeom)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (D : Fin m → ℝ≥0)
variable (hD : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ D j * ‖v‖)
variable (Vcov : Fin m → ℝ≥0) {Psrc Elog P : ℝ}
variable (hnum : AllocatedSourceNumerics B U b S D Vcov Psrc)
variable (hVcov : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Vcov j)
variable {O E Z : ℝ}
local notation "elog" => allocatedGenuineComparisonErrorLog m Psp Dgeom cgeom partitionLog O E
local notation "precision" => Real.exp (-elog)
local notation "Qbudget" => allocatedCutoffSamplingLog m dim Psrc (normalizedSiteCutoffBound : ℝ) Elog P

include hσ1 hC hchart hgeom hcgeom hIgeom hngeom hCgeom hsmall hD hnum hVcov in
theorem exists_allocated_coarse_genuine_source_comparison
    (hpAccuracy : 0 ≤ pAccuracy) (hw : 0 ≤ w) (hv : 0 ≤ v) (hEcoarse : 0 ≤ Ecoarse)
    (hG : (Fintype.card G : ℝ) ≤ Psp) (hmodulus : modulus ≤ M ^ (m + 1))
    (hPsp : 0 ≤ Psp) (hDexp : Dgeom ≤ Real.exp Psp)
    (hdimP : ((dim + 1 : ℕ) : ℝ) ≤ Psp) (hXP : (Fintype.card X : ℝ) ≤ Psp)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Dgeom)
    (hKcov : ∀ j, (Fintype.card (Kcov j) : ℝ) ≤ Dgeom)
    (hO : 0 ≤ O) (hE : 0 ≤ E) (hMP : (M : ℝ) ≤ Real.exp Psp)
    (hJoint : 0 < Z) (hJointInv : Z⁻¹ ≤ 2)
    {Nt Vg Hs : {a // allocatedGridAxis (I := I) U b S.value a} → ℝ} {L : ℝ≥0}
    (hgrid : ∀ (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q))
      (a : {a // allocatedGridAxis (I := I) U b S.value a}),
      ((coverWitness r).expansion a).Bounds (Nt a) (Vg a) (Real.exp O) L (Hs a))
    {Ksample : ℕ} (hKsample : 2 ≤ Ksample)
    (hSampling : PhysicalAmbientRowsKernelSampling.{uX, uJ, 0} m dim Ksample rowTypes rows)
    (hP : 0 ≤ P) (hn : (Fintype.card X : ℝ) ≤ P)
    (hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P)
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    {Rrank S₀ εs η : ℝ} (hS : 0 ≤ S₀) (hSP : S₀ ≤ Real.exp P)
    (hεs : 0 < εs) (hτP : 1 / τ ≤ Real.exp P) (hεsP : 1 / εs ≤ Real.exp P)
    (hstride : ∀ z, (q z : ℝ) ≤ S₀)
    (hsize : ∀ z, Real.exp ((Qbudget + Ksample) ^ Ksample) ≤ (N z : ℝ))
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun z => (N z : ℝ)) Rrank (U j) (p j))
    (hRrank : Real.exp ((Qbudget + Ksample) ^ Ksample) ≤ Rrank)
    (hη : 0 < η) (hη1 : η ≤ 1) (hεs1 : εs ≤ 1) (hElog : 0 ≤ Elog) (hηE : η⁻¹ ≤ Real.exp Elog)
    (hq : ∀ z, 0 < q z) (hτ : 0 < τ)
    (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) selection))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hdimSmall : dim ≤ m + 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {ξ eδ : ℝ} (hξ : 0 < ξ)
    (heδ : 0 ≤ eδ)
    (hδexp : (δ : ℝ)⁻¹ ≤ Real.exp eδ)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight q cells
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z) :
    let _ : ∀ (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q))
      (a : {a // allocatedGridAxis (I := I) U b S.value a}) (k : ((coverWitness r).expansion a).Term),
      NeZero (((coverWitness r).expansion a).period k) :=
      fun r a k => ⟨((hgrid r a).period_pos k).ne'⟩
    let normalizedMesh : ℝ≥0 := ⟨coarseMesh,
      (allocatedProductCoarseMesh_pos m X selection M modulus Psp pAccuracy w v Ecoarse).le⟩
    ∃ t : Fin M, kernelPeriodCandidate (m + 1) t ≤ M ^ (m + 1) ∧
      ∃ F : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim)
          (allocatedPrincipalSides B U b S) → AllocatedFiniteIdealData (Fin dim) I n,
      (∀ y₀, (F y₀).Bounds B U b S rowSets x y₀ refined d (kernelPeriodCandidate (m + 1) t)
        hb o bW hR δ precision (allocatedFiniteIdealInputLog m Dgeom eδ elog) (layerKernelIndexBound m M)) ∧
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    ∀ (test : Finset (Fin dim) → (X → ℝ) → ℂ), (∀ s u, ‖test s u‖ ≤ 1) →
      let source := fun r : labels => ∑ a : cells, (selectedResidueCellWeight q cells V a : ℂ) *
        ∑ v ∈ spatialWindow H 4,
          allocatedRecenteredResidueWeight (τ := τ) B U b S X modulus q wholeReference x hM selection hx
            N hW coarseMesh base cells (physicalCubeSiteTest (fun s => integerBoxTestExtension N (test s))) r a v *
            allocatedProductFullGridResidueProfile B U b hR hσ S refined x hb o bW d coverWitness δ r
              (physicalCubeRowSample U d rows p hm (reconstruct r a.val v))
      let target := fun r : labels =>
        if hr : 0 < (law).mass (Finset.univ.filter (fun y => principalResidueLabel refined y = r)) then
          let rr : AllocatedPositiveResidue (dim := dim) B U b S refined := ⟨r, hr⟩
          ∑ a : cells, (selectedResidueCellWeight q cells V a : ℂ) *
            ((integerBoxCubeCount N dim : ℂ) *
              𝔼 cube : SupportedCube dim (integerBox N : Set (X → ℤ)),
                allocatedAmbientNormalizedSpatialApproximation (τ := τ) B U b S X modulus q wholeReference
                  coverWitness hb o bW d x hM selection hx N hW normalizedMesh base cells p hm rr a
                  (kernelPeriodCandidate (m + 1) t) (F ((coverWitness rr).representative)).coefficient
                  (F ((coverWitness rr).representative)).factor test
                  ((physicalCubeParametersEquiv X dim).symm cube.val))
        else 0
      ‖(residueLaw).complexMean source / (Z : ℂ) -
          (residueLaw).complexMean target / (Z : ℂ)‖ ≤ Real.exp (-E) := by
  intro gridPeriod normalizedMesh
  obtain ⟨hmesh, hmesh4, _, hspatial⟩ := allocatedProductCoarseMesh_partition_budget m X selection
    hPsp hpAccuracy hw hv hEcoarse hG hXP hM hMP hmodulus
  have hmargin : 3 + 2 * coarseMesh ≤ 4 := by linarith
  have hs : 0 ≤ partitionLog := (coarseSpatialLogs_nonneg
    (allocatedProductCoarseInput_nonneg m dim hPsp hpAccuracy hw hv hEcoarse)).2
  exact exists_allocated_budgeted_genuine_source_comparison
    (B := B) (U := U) (b := b) (hR := hR) (hσ := hσ) (hσ1 := hσ1) (S := S)
    (X := X) (modulus := modulus) (q := q) (wholeReference := wholeReference)
    (coverWitness := coverWitness) (hb := hb) (o := o) (bW := bW) (d := d)
    (δ := δ) (x := x) (hM := hM) (selection := selection) (hx := hx) (N := N) (mesh := coarseMesh)
    (base := base) (cells := cells) (p := p) (hm := hm) (C := C) (hC := hC) (hchart := hchart)
    (hgeom := hgeom) (hcgeom := hcgeom) (hIgeom := hIgeom) (hngeom := hngeom)
    (hCgeom := hCgeom) (hsmall := hsmall) (D := D) (hD := hD) (Vcov := Vcov)
    (hnum := hnum) (hVcov := hVcov)
    hPsp hDexp hdimP hXP hvars hKcov hs hO hE hMP hspatial hJoint hJointInv
    hgrid hKsample hSampling hP hn hdim μ ν hS hSP hεs hτP hεsP hstride hsize hrank hRrank
    hη hη1 hεs1 hElog hηE hq hτ hmesh hmargin hperiod hp hdimSmall hδ hδ1 hξ heδ hδexp hZ

end Erdos3.VectorPolynomial

end

end OAI
