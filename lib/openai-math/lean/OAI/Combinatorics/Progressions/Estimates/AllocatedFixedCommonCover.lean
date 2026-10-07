import OAI.Combinatorics.Progressions.Estimates.AllocatedProductRawCoverData
import OAI.Combinatorics.Progressions.Estimates.AllocatedProductSeparatedRawData

namespace OAI

section

namespace Erdos3.VectorPolynomial

universe uG uI uB uGeom uCover uSpace

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped ContDiff BigOperators Classical NNReal

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
variable {dim : ℕ}

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) ((j : ℕ) + 1) → Finset (Fin dim)))

section FixedScale

variable {J : Fin m → Type uGeom} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

def AllocatedRawSourceData (S : LayerSamplerScale (G := G) B U b R σ)
    (Psp E pNum Pbase Qraw : ℝ) (δ : ℝ≥0) (A Kraw : ℕ) : Prop :=
  ∀ (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    {Mk : ℕ} (hMk : 0 < Mk) (selection : Fin dim ↪ G)
    (hx : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
    (_hqDim : dim ≤ m + 1) (_hMkPsp : (Mk : ℝ) ≤ Real.exp Psp),
  ∃ (d : ℕ) (hd : 0 < d),
    let : NeZero d := ⟨hd.ne'⟩
    (d : ℝ) ≤ Real.exp ((Pbase + A) ^ A) ∧
  ∀ (modulus : ℕ) (hmodulus : 0 < modulus),
    let : NeZero modulus := ⟨hmodulus.ne'⟩
    ∀ (_hmodulusSize : modulus ≤ Mk ^ (m + 1))
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
    {Kcov : Fin m → Type uCover} [∀ j, Fintype (Kcov j)]
    (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hCp : ∀ j, (C j : ℝ) ≤ Real.exp pNum) (_hVp : ∀ j, (V j : ℝ) ≤ Real.exp pNum)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B (Fin dim) Cinv 1 j)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    {X : Type uSpace} [Fintype X] [DecidableEq X]
    (_hXPsp : (Fintype.card X : ℝ) ≤ Psp)
    (q : X → ℕ) (_hq : ∀ t, 0 < q t) (_hqPsp : ∀ t, (q t : ℝ) ≤ Real.exp Psp),
    let refined := residueRefinedPeriod modulus q
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
    let ξ := normalizedTupleNarrowWidth X indices selection Mk Psp (E + 2)
    let hξ := normalizedTupleNarrowWidth_pos X indices selection Mk Psp (E + 2)
    let mesh := normalizedTupleRadius X selection Mk Psp (E + 2) W / 4
    ∀ (small : ℝ) (_hsmall : 0 < small) (_hsmallMesh : small ≤ mesh)
    {τ : ℝ} (hτ : 0 < τ) (_hτP : 1 / τ ≤ Real.exp pNum)
    (N : X → ℕ) (hN : ∀ t, 0 < N t)
    (_hsize : ∀ t, Real.exp ((Qraw + Kraw) ^ Kraw) ≤ (N t : ℝ))
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
    {rank : ℝ}
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) rank (U j) (poly j))
    (_hRank : Real.exp ((Qraw + Kraw) ^ Kraw) ≤ rank)
    (base : X → ℤ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
    (_hcells : cells.Nonempty)
    (test : Finset (Fin dim) → (X → ℝ) → ℂ) (_htest : ∀ site v, ‖test site v‖ ≤ 1)
    (Z : ℝ) (_hZ : 1 / 2 ≤ Z),
    ∃ hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
      (narrowTrimmedSpatialWidths (G := G) (J := indices) W τ ξ N) z,
    ‖allocatedOriginalTupleSource B U b hR hσ S x X q hb o N hN hW hτ hξ base cells hmass
        (physicalCubeSiteTest test) Z poly hmem -
      allocatedWholeIdealReference (τ := τ) (ξ := ξ)
        B U b hR hσ S x jetRows X hMk selection hx modulus q reference hb o bW d
        N hW small base cells (physicalCubeEuclideanSample U d poly hmem) (physicalCubeSiteTest test) Z δ‖ ≤
      Real.exp (-E)

theorem allocatedRawSourceData_of_original
    {D Psp E e pNum : ℝ} {δ : ℝ≥0} {A T Kproj Kideal : ℕ}
    (hraw : AllocatedOriginalResidueWeightedMeshAtScale.{uG,uI,uB,uGeom,uCover,uSpace}
      (G := G) (dim := dim) B U b hR hσ D Psp E e pNum δ A T Kproj Kideal) :
    let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * Psp
    let error := allocatedReferenceIdealError m D Psp (E + 4)
    let S := allocatedIdealScale (G := G) B U b hR hσ D pNum e w error
    let gainLog := allocatedProfileGainLog m D Psp w
    let lengthLog := allocatedIdealScaleLog m D pNum e w error
    let Pbase := allocatedIdealSourceBudget m D pNum e w error
    let l := allocatedSpatialLateLog (G := G) B Pbase Pbase
    let F := allocatedProfileFourierOutput (allocatedActualProfileInput m D pNum e gainLog lengthLog)
    let Qraw := allocatedSourceSamplingBudget m dim A Pbase E l F
    AllocatedRawSourceData.{uG,uI,uB,uGeom,uCover,uSpace}
      (dim := dim) B U b hR hσ S Psp E pNum Pbase Qraw δ A (max T (max Kproj Kideal)) := by
  exact hraw.2

end FixedScale

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

def AllocatedUniformSourceContract
    (S : LayerSamplerScale (G := G) B U b R σ) (Psp E e p₁ : ℝ) (hPsp : 0 ≤ Psp)
    (witnesses : (q : AllocatedRefinedPeriodIndex m Psp) →
      (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
      AllocatedResidueSiteWitness (dim := dim) B U b S (q.val : ℕ) r.val) : Prop :=
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
    AllocatedSourceCoverContract.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ S stride modulus (witnesses index) o p₁
      (allocatedSiteKernelMaskLog m Psp) (allocatedIdealProfileLog m p₁ e) e E Psp

theorem allocatedRawCoverData_of_source
    (S : LayerSamplerScale (G := G) B U b R σ)
    {Psp E e pNum p₁ Pbase Qraw : ℝ} {δ : ℝ≥0} {A Kraw Ksite : ℕ}
    (hPsp : 0 ≤ Psp) (hE : 0 ≤ E) (he : 0 ≤ e) (hp₁ : 0 ≤ p₁)
    (hpNum₁ : pNum ≤ p₁)
    (hvarsGrowth : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp Psp)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp p₁)
    (hδ : 0 < δ) (hδe : (δ : ℝ)⁻¹ ≤ Real.exp e) (hKsite : 2 ≤ Ksite)
    (hSampling : AllocatedBooleanRowsSampling.{uX,uJ,uG,uI,uB,uQ}
      m dim Ksite rowTypes rows)
    (hraw : AllocatedRawSourceData.{uG,uI,uB,uJ,uQ,uX}
      (dim := dim) B U b hR hσ S Psp (E + 1) pNum Pbase Qraw δ A Kraw) :
    ∀ (witnesses : (q : AllocatedRefinedPeriodIndex m Psp) →
        (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
        AllocatedResidueSiteWitness (dim := dim) B U b S (q.val : ℕ) r.val),
      AllocatedUniformSourceContract.{uG,uI,uB,uJ,uQ,uX} B U b hR hσ S Psp E e p₁ hPsp witnesses →
      AllocatedRawCoverData.{uG,uI,uB,uJ,uQ,uX}
        B U b hR hσ S Psp E e pNum Pbase Qraw p₁ hPsp δ A Kraw Ksite witnesses := by
  intro witnesses hContracts
  unfold AllocatedRawCoverData
  intro w v Pfinal
  obtain ⟨hPfinal, hPfinalSp, hdimFinal, hpNumFinal, _, hFourier, hGeometry⟩ :=
    sourceCoverParameter_bounds dim Kraw (pNum := pNum) (Qraw := Qraw)
      (F := allocatedSiteErrorFourierOutput m p₁ w v)
      (G := allocatedOriginalGeometryLog m Psp p₁ w v (E + 1)) hPsp
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
  intro block iLattice _ _ _ _ _ hb o Kcov iKcov bW C V hC hV hCp hVp Cinv hCinv hchart hsmall μ _ _ ν iInvNu iProbNu
    iCompactSmall iMeasSmall iBorelSmall μsmall iInvSmall iProbSmall X _ _ hXPsp q hq hqPsp refined index
  obtain ⟨hRefined, hdiv, hRefinedBound, hsize, reference, residue, href, hresidue, hraw⟩ :=
    hraw block hb o bW C V hC hV hCp hVp Cinv hCinv hchart hsmall μ ν hXPsp q hq hqPsp
  let : NeZero (residueRefinedPeriod modulus q) := ⟨hRefined.ne'⟩
  refine ⟨hRefined, hdiv, hRefinedBound, hsize, reference, residue, href, hresidue, ?_⟩
  intro W hW indices ξ hξ sourceMesh mesh τ hτ hτP N hN hsizeN poly hpoly hmem
    rank hrank hRank base cells hcells test htest Z hZ V₀ H point law target wholeReference reconstruct weight
  have hsourceMesh : 0 < sourceMesh := by
    have ht : 0 < normalizedTupleTolerance X Psp ((E + 1) + 2) :=
      (spatialTupleTolerance_spec (Fintype.card X) (Real.exp_nonneg _)
        (Real.exp_nonneg _) (half_pos (Real.exp_pos _))).1
    have hLip := anisotropicSpatialDensityLip_nonneg selection (show 0 ≤ 1 / (Mk : ℝ) by positivity)
    exact div_pos (twoTermErrorWidth_spec (by positivity) ht).1 (by norm_num)
  have hw : 0 ≤ w := allocatedSiteKernelMaskLog_nonneg m hPsp
  have hv : 0 ≤ v := allocatedIdealProfileLog_nonneg m hp₁ he
  have hcoverMesh := (allocatedOriginalCoverMesh_spec m hPsp hp₁ hw hv (by linarith : 0 ≤ E + 1)).1
  have hmesh : 0 < mesh := lt_min hsourceMesh hcoverMesh
  obtain ⟨hmass, hsource⟩ := hraw mesh hmesh (min_le_left _ _) hτ hτP N hN
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
  exact @hcontract sourceMesh hsourceMesh Ksite hKsite (@hSampling) δ hδ hδe hRi
    x hb Kcov iKcov bW d inferInstance iLattice hperiod C V hC hV
    (fun j => (hCp j).trans (Real.exp_le_exp.mpr hpNum₁))
    (fun j => (hVp j).trans (Real.exp_le_exp.mpr hpNum₁))
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

def AllocatedProductUniformSourceContract
    (S : LayerSamplerScale (G := G) B U b R σ) (Psp E e p₁ : ℝ) (hPsp : 0 ≤ Psp)
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
    AllocatedProductSourceContract.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ S stride modulus (witnesses index) o p₁
      (allocatedSiteKernelMaskLog m Psp) (allocatedIdealProfileLog m p₁ e) e E Psp

theorem allocatedProductRawCoverData_of_source
    (S : LayerSamplerScale (G := G) B U b R σ)
    {Psp E e pNum p₁ Pbase Qraw : ℝ} {δ : ℝ≥0} {A Kraw Ksite : ℕ}
    (hPsp : 0 ≤ Psp) (hE : 0 ≤ E) (he : 0 ≤ e) (hp₁ : 0 ≤ p₁)
    (hpNum₁ : pNum ≤ p₁)
    (hvarsGrowth : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp Psp)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp p₁)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδe : (δ : ℝ)⁻¹ ≤ Real.exp e) (hKsite : 2 ≤ Ksite)
    (hSampling : AllocatedBooleanRowsSampling.{uX,uJ,uG,uI,uB,uQ}
      m dim Ksite rowTypes rows)
    (hraw : AllocatedRawSourceData.{uG,uI,uB,uJ,uQ,uX}
      (dim := dim) B U b hR hσ S Psp (E + 1) pNum Pbase Qraw δ A Kraw) :
    ∀ (witnesses : (q : AllocatedRefinedPeriodIndex m Psp) →
        (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
        AllocatedFullGridResidueWitness (dim := dim) B U b S (q.val : ℕ) r.val),
      AllocatedProductUniformSourceContract.{uG,uI,uB,uJ,uQ,uX} B U b hR hσ S Psp E e p₁ hPsp witnesses →
      AllocatedProductRawCoverData.{uG,uI,uB,uJ,uQ,uX}
        B U b hR hσ S Psp E e pNum Pbase Qraw p₁ hPsp δ A Kraw Ksite witnesses := by
  intro witnesses hContracts
  unfold AllocatedProductRawCoverData
  intro w v Pfinal
  obtain ⟨hPfinal, hPfinalSp, hdimFinal, hpNumFinal, _, hFourier, hGeometry⟩ :=
    sourceCoverParameter_bounds dim Kraw (pNum := pNum) (Qraw := Qraw)
      (F := allocatedSiteErrorFourierOutput m p₁ w v)
      (G := allocatedOriginalGeometryLog m Psp p₁ w v (E + 1)) hPsp
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
  intro block iLattice _ _ _ _ _ hb o Kcov iKcov bW C V hC hV hCp hVp Cinv hCinv hchart hsmall hσ1 hproductSmall μ _ _ ν iInvNu iProbNu
    iCompactSmall iMeasSmall iBorelSmall μsmall iInvSmall iProbSmall X _ _ hXPsp q hq hqPsp refined index
  obtain ⟨hRefined, hdiv, hRefinedBound, hsize, reference, residue, href, hresidue, hraw⟩ :=
    hraw block hb o bW C V hC hV hCp hVp Cinv hCinv hchart hsmall μ ν hXPsp q hq hqPsp
  let : NeZero (residueRefinedPeriod modulus q) := ⟨hRefined.ne'⟩
  refine ⟨hRefined, hdiv, hRefinedBound, hsize, reference, residue, href, hresidue, ?_⟩
  intro W hW indices ξ hξ sourceMesh mesh τ hτ hτP N hN hsizeN poly hpoly hmem
    rank hrank hRank base cells hcells test htest Z hZ V₀ H point law target wholeReference reconstruct weight
  have hsourceMesh : 0 < sourceMesh := by
    have ht : 0 < normalizedTupleTolerance X Psp ((E + 1) + 2) :=
      (spatialTupleTolerance_spec (Fintype.card X) (Real.exp_nonneg _)
        (Real.exp_nonneg _) (half_pos (Real.exp_pos _))).1
    have hLip := anisotropicSpatialDensityLip_nonneg selection (show 0 ≤ 1 / (Mk : ℝ) by positivity)
    exact div_pos (twoTermErrorWidth_spec (by positivity) ht).1 (by norm_num)
  have hw : 0 ≤ w := allocatedSiteKernelMaskLog_nonneg m hPsp
  have hv : 0 ≤ v := allocatedIdealProfileLog_nonneg m hp₁ he
  have hcoverMesh := (allocatedOriginalCoverMesh_spec m hPsp hp₁ hw hv (by linarith : 0 ≤ E + 1)).1
  have hmesh : 0 < mesh := lt_min hsourceMesh hcoverMesh
  obtain ⟨hmass, hsource⟩ := hraw mesh hmesh (min_le_left _ _) hτ hτP N hN
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
    (fun j => (hCp j).trans (Real.exp_le_exp.mpr hpNum₁))
    (fun j => (hVp j).trans (Real.exp_le_exp.mpr hpNum₁))
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

def AllocatedProductSeparatedUniformSourceContract
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
    AllocatedProductSeparatedContract.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ S stride modulus (witnesses index) o pAccuracy pSampling
      (allocatedSiteKernelMaskLog m Psp) (allocatedIdealProfileLog m pAccuracy e) e E Psp

theorem allocatedProductSeparatedRawData_of_source
    (S : LayerSamplerScale (G := G) B U b R σ)
    {Psp E e pNum pAccuracy pSampling Pbase Qraw : ℝ} {δ : ℝ≥0} {A Kraw Ksite : ℕ}
    (hPsp : 0 ≤ Psp) (hE : 0 ≤ E) (he : 0 ≤ e) (hpAccuracy : 0 ≤ pAccuracy)
    (hvarsGrowth : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp Psp)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp pAccuracy)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδe : (δ : ℝ)⁻¹ ≤ Real.exp e) (hKsite : 2 ≤ Ksite)
    (hSampling : AllocatedBooleanRowsSampling.{uX,uJ,uG,uI,uB,uQ}
      m dim Ksite rowTypes rows)
    (hraw : AllocatedRawSourceData.{uG,uI,uB,uJ,uQ,uX}
      (dim := dim) B U b hR hσ S Psp (E + 1) pNum Pbase Qraw δ A Kraw) :
    ∀ (witnesses : (q : AllocatedRefinedPeriodIndex m Psp) →
        (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
        AllocatedFullGridResidueWitness (dim := dim) B U b S (q.val : ℕ) r.val),
      AllocatedProductSeparatedUniformSourceContract.{uG,uI,uB,uJ,uQ,uX} B U b hR hσ S Psp E e pAccuracy pSampling hPsp witnesses →
      AllocatedProductSeparatedRawData.{uG,uI,uB,uJ,uQ,uX}
        B U b hR hσ S Psp E e pNum Pbase Qraw pAccuracy pSampling hPsp δ A Kraw Ksite witnesses := by
  intro witnesses hContracts
  unfold AllocatedProductSeparatedRawData
  intro w v Pfinal
  obtain ⟨hPfinal, hPfinalSp, hdimFinal, hpNumFinal, _, hFourier, hGeometry⟩ :=
    sourceCoverParameter_bounds dim Kraw (pNum := pNum) (Qraw := Qraw)
      (F := allocatedSiteErrorFourierOutput m pSampling w v)
      (G := allocatedSeparatedGeometryLog m Psp pAccuracy pSampling w v (E + 1)) hPsp
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
  intro W hW indices ξ hξ sourceMesh mesh τ hτ hτP N hN hsizeN poly hpoly hmem
    rank hrank hRank base cells hcells test htest Z hZ V₀ H point law target wholeReference reconstruct weight
  have hsourceMesh : 0 < sourceMesh := by
    have ht : 0 < normalizedTupleTolerance X Psp ((E + 1) + 2) :=
      (spatialTupleTolerance_spec (Fintype.card X) (Real.exp_nonneg _)
        (Real.exp_nonneg _) (half_pos (Real.exp_pos _))).1
    have hLip := anisotropicSpatialDensityLip_nonneg selection (show 0 ≤ 1 / (Mk : ℝ) by positivity)
    exact div_pos (twoTermErrorWidth_spec (by positivity) ht).1 (by norm_num)
  have hw : 0 ≤ w := allocatedSiteKernelMaskLog_nonneg m hPsp
  have hv : 0 ≤ v := allocatedIdealProfileLog_nonneg m hpAccuracy he
  have hcoverMesh := (allocatedOriginalCoverMesh_spec m hPsp hpAccuracy hw hv (by linarith : 0 ≤ E + 1)).1
  have hmesh : 0 < mesh := lt_min hsourceMesh hcoverMesh
  obtain ⟨hmass, hsource⟩ := hraw mesh hmesh (min_le_left _ _) hτ hτP N hN
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
variable {p c P e E : ℝ}

local notation "Eraw" => (E + 1) + 4
local notation "Esite" => allocatedOriginalCoverAccuracy P (E + 1)
local notation "D" => allocatedComparisonDimension m p
local notation "pNum" => allocatedCommonScaleNumeric m p c P Eraw
local notation "S" => allocatedCommonScale (G := G) B U b hR hσ p c P e Eraw
local notation "sourceParameter" => allocatedCommonRefinedSourceLog m p c P e Eraw Esite
local notation "maskLog" => allocatedSiteKernelMaskLog m P
local notation "profileLog" => allocatedIdealProfileLog m sourceParameter e
local notation "error" => allocatedReferenceIdealError m D P Eraw
local notation "lengthLog" => allocatedIdealScaleLog m D pNum e maskLog error
local notation "gainLog" => allocatedProfileGainLog m D P maskLog
local notation "Pbase" => allocatedIdealSourceBudget m D pNum e maskLog error
local notation "lateLog" => allocatedSpatialLateLog (G := G) B Pbase Pbase
local notation "rawFourier" => allocatedProfileFourierOutput (allocatedActualProfileInput m D pNum e gainLog lengthLog)

local notation "cutoff" => allocatedRefinedPeriodCutoff m P
local notation "scalarEnvelope" => canonicalScalarSourceEnvelope m cutoff
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
local notation "activeAxes" => {a : {a // allocatedGridAxis (I := I) U b (LayerSamplerScale.value S) a} //
  allocatedActiveGrid B U b S a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "Λ" => allocatedSiteSpectrumLog m sourceParameter maskLog profileLog Esite
local notation "siteLip" => (NNReal.mk (Real.exp (1 + 6 * Λ + 12)) (Real.exp_nonneg _) + 4 : ℝ≥0)
local notation "coefficientCap" => (fun a : activeAxes =>
  allocatedGridPointCap B scalarEnvelope (ig (Subtype.val a)) (rowSets (Sigma.fst (ig (Subtype.val a)))) *
    Real.exp (Fintype.card (Finset (Fin dim)) * (4 * Λ + 8) + Λ))

theorem exists_original_common_raw_cover
    (hp : 0 ≤ p) (hc : 0 ≤ c) (hP : 0 ≤ P) (he : 0 ≤ e) (hE : 0 ≤ E)
    (hdimSmall : dim ≤ m + 1) (hmP : ((m + 2 : ℕ) : ℝ) ≤ P) (hpP : p ≤ P)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (hR1 : ∀ j, R j ≤ 1)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp c) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp c)
    (hBlocks : ∀ j i, siteSpectrumBlockCount m ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    {δ : ℝ≥0} (hδ : 0 < δ) (hδe : (δ : ℝ)⁻¹ ≤ Real.exp e)
    {A T Kproj Kideal Ksite : ℕ} (hKsite : 2 ≤ Ksite)
    (hSampling : AllocatedBooleanRowsSampling.{uX,uJ,uG,uI,uB,uQ} m dim Ksite rowTypes rows)
    (hraw : AllocatedOriginalResidueWeightedMeshAtScale.{uG,uI,uB,uJ,uQ,uX}
      (G := G) (dim := dim) B U b hR hσ D P (E + 1) e pNum δ A T Kproj Kideal) :
    ∃ witnesses : (q : AllocatedRefinedPeriodIndex m P) →
        (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
        AllocatedResidueSiteWitness (dim := dim) B U b S (q.val : ℕ) r.val,
      AllocatedPointwiseResidueCoverFamily.{uG,uI,uB,uJ,uQ,uX,0}
        B U b hR hσ S (fun q : AllocatedRefinedPeriodIndex m P => (q.val : ℕ))
        witnesses siteLip coefficientCap ∧
      AllocatedRawCoverData.{uG,uI,uB,uJ,uQ,uX}
        B U b hR hσ S P E e pNum Pbase
        (allocatedSourceSamplingBudget m dim A Pbase (E + 1) lateLog rawFourier)
        sourceParameter hP δ A (max T (max Kproj Kideal)) Ksite witnesses := by
  have hEraw : 0 ≤ Eraw := by linarith
  have hEsite : 0 ≤ Esite := by
    have hsp := coefficientErrorSpatialLog_nonneg hP
    unfold allocatedOriginalCoverAccuracy
    linarith
  obtain ⟨hp₁, _, _, hcp₁, _, _, _, _, _, hnum, _⟩ :=
    allocatedCommonRefinedSourceLog_bounds m hp hc hP he hEraw hEsite
  obtain ⟨witnesses, _, _, hFamily, hContracts⟩ :=
    exists_original_common_source_cover.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ hp hc hP he hEraw hE hdimSmall hmP hpP hvars hI hn hR1 hRi hσi hBlocks
  refine ⟨witnesses, hFamily, ?_⟩
  have hvarsGrowth : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp P :=
    (hvars.trans hpP).trans (by linarith [Real.add_one_le_exp P])
  exact allocatedRawCoverData_of_source.{uG,uI,uB,uJ,uQ,uX}
    B U b hR hσ S hP hE he hp₁ hnum hvarsGrowth
    (fun j => (hRi j).trans (Real.exp_le_exp.mpr hcp₁))
    hδ hδe hKsite hSampling (allocatedRawSourceData_of_original B U b hR hσ hraw) witnesses hContracts

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
variable {p c P e E : ℝ}

local notation "Eraw" => (E + 1) + 4
local notation "Esite" => allocatedOriginalCoverAccuracy P (E + 1)
local notation "D" => allocatedComparisonDimension m p
local notation "pNum" => allocatedCommonScaleNumeric m p c P Eraw
local notation "S" => allocatedCommonScale (G := G) B U b hR hσ p c P e Eraw
local notation "sourceParameter" => allocatedCommonRefinedSourceLog m p c P e Eraw Esite
local notation "maskLog" => allocatedSiteKernelMaskLog m P
local notation "profileLog" => allocatedIdealProfileLog m sourceParameter e
local notation "error" => allocatedReferenceIdealError m D P Eraw
local notation "lengthLog" => allocatedIdealScaleLog m D pNum e maskLog error
local notation "gainLog" => allocatedProfileGainLog m D P maskLog
local notation "Pbase" => allocatedIdealSourceBudget m D pNum e maskLog error
local notation "lateLog" => allocatedSpatialLateLog (G := G) B Pbase Pbase
local notation "rawFourier" => allocatedProfileFourierOutput (allocatedActualProfileInput m D pNum e gainLog lengthLog)

local notation "cutoff" => allocatedRefinedPeriodCutoff m P
local notation "scalarEnvelope" => canonicalScalarSourceEnvelope m cutoff
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
local notation "activeAxes" => {a : {a // allocatedGridAxis (I := I) U b (LayerSamplerScale.value S) a} //
  allocatedActiveGrid B U b S a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "Λ" => allocatedSiteSpectrumLog m sourceParameter maskLog profileLog Esite
local notation "siteLip" => (NNReal.mk (Real.exp (1 + 6 * Λ + 12)) (Real.exp_nonneg _) + 4 : ℝ≥0)
local notation "coefficientCap" => (fun a : activeAxes =>
  allocatedGridPointCap B scalarEnvelope (ig (Subtype.val a)) (rowSets (Sigma.fst (ig (Subtype.val a)))) *
    Real.exp (Fintype.card (Finset (Fin dim)) * (4 * Λ + 8) + Λ))

theorem exists_original_common_genuine_cover
    (hp : 0 ≤ p) (hc : 0 ≤ c) (hP : 0 ≤ P) (he : 0 ≤ e) (hE : 0 ≤ E)
    (hdimSmall : dim ≤ m + 1) (hmP : ((m + 2 : ℕ) : ℝ) ≤ P) (hpP : p ≤ P)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (hR1 : ∀ j, R j ≤ 1)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp c) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp c)
    (hBlocks : ∀ j i, siteSpectrumBlockCount m ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    {δ : ℝ≥0} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδe : (δ : ℝ)⁻¹ ≤ Real.exp e)
    {A T Kproj Kideal Ksite : ℕ} (hKsite : 2 ≤ Ksite)
    (hSampling : AllocatedBooleanRowsSampling.{uX,uJ,uG,uI,uB,uQ} m dim Ksite rowTypes rows)
    (hraw : AllocatedOriginalResidueWeightedMeshAtScale.{uG,uI,uB,uJ,uQ,uX}
      (G := G) (dim := dim) B U b hR hσ D P (E + 1) e pNum δ A T Kproj Kideal) :
    ∃ witnesses : (q : AllocatedRefinedPeriodIndex m P) →
        (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
        AllocatedResidueSiteWitness (dim := dim) B U b S (q.val : ℕ) r.val,
      AllocatedPointwiseResidueCoverFamily.{uG,uI,uB,uJ,uQ,uX,0}
        B U b hR hσ S (fun q : AllocatedRefinedPeriodIndex m P => (q.val : ℕ))
        witnesses siteLip coefficientCap ∧
      AllocatedGenuineCoverData.{uG,uI,uB,uJ,uQ,uX}
        B U b hR hσ S P E e pNum Pbase
        (allocatedSourceSamplingBudget m dim A Pbase (E + 1) lateLog rawFourier)
        sourceParameter hP δ A (max T (max Kproj Kideal)) Ksite witnesses siteLip coefficientCap := by
  obtain ⟨witnesses, hFamily, hCover⟩ :=
    exists_original_common_raw_cover.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ hp hc hP he hE hdimSmall hmP hpP hvars hI hn hR1 hRi hσi hBlocks
      hδ hδe hKsite hSampling hraw
  exact ⟨witnesses, hFamily, allocatedGenuineCoverData_of_raw B U b hR hσ S hP hδ hδ1
    witnesses hCover hFamily⟩

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

def AllocatedCommonGenuineCoverAt (p Psp E e t : ℝ) (hP : 0 ≤ Psp) (δ : ℝ≥0)
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
      AllocatedGenuineCoverData.{uG,uI,uB,uJ,uQ,uX}
        B U b hR hσ S Psp E e pNum Pbase (allocatedSourceSamplingBudget m dim A Pbase (E + 1) lateLog F)
        p₁ hP δ A (max T (max Kproj Kideal)) Ksite witnesses L Cc

theorem allocatedCommonOriginalMesh_genuine_cover
    {p Psp E e t : ℝ} {δ : ℝ≥0} {A T Kproj Kideal : ℕ}
    (hp : 0 ≤ p) (hPsp : 0 ≤ Psp) (hE : 0 ≤ E) (he : 0 ≤ e)
    (hdim : dim ≤ m + 1) (hmPsp : ((m + 2 : ℕ) : ℝ) ≤ Psp) (hpPsp : p ≤ Psp)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (hBlocks : ∀ j i, siteSpectrumBlockCount m ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδe : (δ : ℝ)⁻¹ ≤ Real.exp e)
    (hraw : AllocatedCommonResidueWeightedOriginalMeshAt.{uG,uI,uB,uJ,uQ,uX}
      (G := G) (dim := dim) B p Psp (E + 1) e t δ A T Kproj Kideal) :
    ∃ Ksite : ℕ, 2 ≤ Ksite ∧
      AllocatedCommonGenuineCoverAt.{uG,uI,uB,uJ,uQ,uX}
        (G := G) (dim := dim) B p Psp E e t hPsp δ A T Kproj Kideal Ksite := by
  obtain ⟨Ksite, hKsite, hSampling⟩ :=
    exists_allocated_boolean_rows_sampling.{uX,uJ,uG,uI,uB,uQ} m dim
  refine ⟨Ksite, hKsite, ?_⟩
  intro c hc J _ U b R σ hR hσ hσt hR1 hRi hσi
  exact exists_original_common_genuine_cover B U b hR hσ hp hc hPsp he hE hdim hmPsp hpPsp
    hvars hI hn hR1 hRi hσi hBlocks hδ hδ1 hδe hKsite
    (hSampling (fun j => fullBooleanRowSetFintype dim (j.val + 1)))
    (hraw hc U b hR hσ hσt hR1 hRi hσi)

theorem exists_allocated_common_genuine_cover
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    {p Psp E : ℝ} (hp : 0 ≤ p) (hPsp : 0 ≤ Psp) (hE : 0 ≤ E)
    (hdim : dim ≤ m + 1) (hmPsp : ((m + 2 : ℕ) : ℝ) ≤ Psp) (hpPsp : p ≤ Psp)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (hBlocks : ∀ j i, siteSpectrumBlockCount m ≤ Fintype.card (B ⟨j, Sum.inr i⟩)) :
    ∃ K : ℕ, 2 ≤ K ∧
      let D := allocatedComparisonDimension m p
      let target := profileReferenceErrorLog Psp (E + 1 + 4)
      let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * Psp
      let gainLog := allocatedProfileGainLog m D Psp w
      let ε := physicalIdealErrorShare target gainLog
      let e := physicalIdealSmoothingLog (B := B) (O := fun a : LayerSamplerAxis I n => jets a.1)
        (α := Fin dim) (layerSamplerDegree I n) A T target gainLog
      ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧
        (δ : ℝ) = booleanRegularizationRadius (B := B)
          (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim) (layerSamplerDegree I n)
          (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
          A T (ε / 2) ∧ (δ : ℝ)⁻¹ ≤ Real.exp e ∧
        let t := booleanMassPerturbationScale (B := B)
          (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim)
          ((G × Option (Fin dim)) ⊕ (Σ a, SamplerCoefficientSlot G B (layerSamplerDegree I n) a))
          (layerSamplerDegree I n)
          (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
          A T m 1 (ε / 2)
        0 < t ∧ t ≤ 1 ∧
          ∃ A₀ T₀ Kproj Ksite : ℕ, 2 ≤ A₀ ∧ 2 ≤ T₀ ∧ 2 ≤ Kproj ∧ 2 ≤ Ksite ∧
            AllocatedCommonGenuineCoverAt.{uG,uI,uB,uJ,uQ,uX} (G := G) (dim := dim)
              B p Psp E e t hPsp δ A₀ T₀ Kproj K Ksite := by
  have hE1 : 0 ≤ E + 1 := by linarith
  obtain ⟨K, hK, δ, hδ, hδ1, hδeq, hδe, ht, ht1, A₀, T₀, Kproj, hA₀, hT₀, hKproj, hraw⟩ :=
    exists_allocated_common_residue_weighted_original_mesh.{uG,uI,uB,uJ,uQ,uX}
      (G := G) (dim := dim) B ψ hψ hrange hzero hone A T hLip hTransition
      hp hPsp hE1 hdim hmPsp hpPsp hvars hI hn
  have htarget : 0 ≤ profileReferenceErrorLog Psp (E + 1 + 4) := by
    have hs := coefficientErrorSpatialLog_nonneg hPsp
    unfold profileReferenceErrorLog
    linarith
  have hw : 0 ≤ (m * 2 ^ (m + 1) : ℕ) * Psp := mul_nonneg (Nat.cast_nonneg _) hPsp
  have hgain := allocatedProfileGainLog_nonneg m (allocatedComparisonDimension_bounds m hp).1 hPsp hw
  have he := physicalIdealSmoothingLog_nonneg (B := B)
    (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim)
    (layerSamplerDegree I n) A T htarget hgain
  obtain ⟨Ksite, hKsite, hcover⟩ := allocatedCommonOriginalMesh_genuine_cover B hp hPsp hE he
    hdim hmPsp hpPsp hvars hI hn hBlocks hδ hδ1 hδe hraw
  exact ⟨K, hK, δ, hδ, hδ1, hδeq, hδe, ht, ht1, A₀, T₀, Kproj, Ksite,
    hA₀, hT₀, hKproj, hKsite, hcover⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq

variable {m dim : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

def AllocatedCommonRawCoverAt (p P E e t : ℝ) (hP : 0 ≤ P) (δ : ℝ≥0)
    (A T Kproj Kideal Ksite : ℕ) : Prop :=
  ∀ {c : ℝ}, 0 ≤ c → ∀ {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j),
    (∀ j, σ j ≤ t) → (∀ j, R j ≤ 1) →
    (∀ j, (R j)⁻¹ ≤ Real.exp c) → (∀ j, (σ j)⁻¹ ≤ Real.exp c) →
    let Eraw := E + 1 + 4
    let Esite := allocatedOriginalCoverAccuracy P (E + 1)
    let D := allocatedComparisonDimension m p
    let pNum := allocatedCommonScaleNumeric m p c P Eraw
    let S := allocatedCommonScale (G := G) B U b hR hσ p c P e Eraw
    let p₁ := allocatedCommonRefinedSourceLog m p c P e Eraw Esite
    let w := allocatedSiteKernelMaskLog m P
    let v := allocatedIdealProfileLog m p₁ e
    let error := allocatedReferenceIdealError m D P Eraw
    let lengthLog := allocatedIdealScaleLog m D pNum e w error
    let gainLog := allocatedProfileGainLog m D P w
    let Pbase := allocatedIdealSourceBudget m D pNum e w error
    let lateLog := allocatedSpatialLateLog (G := G) B Pbase Pbase
    let F := allocatedProfileFourierOutput (allocatedActualProfileInput m D pNum e gainLog lengthLog)
    let Qraw := allocatedSourceSamplingBudget m dim A Pbase (E + 1) lateLog F
    let activeAxes := {a : {a // allocatedGridAxis (I := I) U b S.value a} //
      allocatedActiveGrid B U b S a}
    let ig := allocatedGridIntegerAxis B U b S
    let scalarEnvelope := canonicalScalarSourceEnvelope m (allocatedRefinedPeriodCutoff m P)
    let Λ := allocatedSiteSpectrumLog m p₁ w v Esite
    let L : ℝ≥0 := ⟨Real.exp (1 + 6 * Λ + 12), Real.exp_nonneg _⟩ + 4
    let Cc := fun a : activeAxes =>
      allocatedGridPointCap B scalarEnvelope (ig a.val) (rowSets (ig a.val).1) *
        Real.exp (Fintype.card (Finset (Fin dim)) * (4 * Λ + 8) + Λ)
    ∃ witnesses : (q : AllocatedRefinedPeriodIndex m P) →
        (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
        AllocatedResidueSiteWitness (dim := dim) B U b S (q.val : ℕ) r.val,
      AllocatedPointwiseResidueCoverFamily.{uG,uI,uB,uJ,uQ,uX,0}
        B U b hR hσ S (fun q : AllocatedRefinedPeriodIndex m P => (q.val : ℕ)) witnesses L Cc ∧
      AllocatedRawCoverData.{uG,uI,uB,uJ,uQ,uX}
        B U b hR hσ S P E e pNum Pbase Qraw p₁ hP δ A (max T (max Kproj Kideal)) Ksite witnesses

theorem allocatedCommonRawCoverAt_of_source
    {p P E e t : ℝ} {δ : ℝ≥0} {A T Kproj Kideal Ksite : ℕ}
    (hp : 0 ≤ p) (hP : 0 ≤ P) (hE : 0 ≤ E) (he : 0 ≤ e)
    (hdim : dim ≤ m + 1) (hmP : ((m + 2 : ℕ) : ℝ) ≤ P) (hpP : p ≤ P)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (hBlocks : ∀ j i, siteSpectrumBlockCount m ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (hδ : 0 < δ) (hδe : (δ : ℝ)⁻¹ ≤ Real.exp e) (hKsite : 2 ≤ Ksite)
    (hSampling : AllocatedBooleanRowsSampling.{uX,uJ,uG,uI,uB,uQ} m dim Ksite rowTypes rows)
    (hraw : AllocatedCommonResidueWeightedOriginalMeshAt.{uG,uI,uB,uJ,uQ,uX}
      (G := G) (dim := dim) B p P (E + 1) e t δ A T Kproj Kideal) :
    AllocatedCommonRawCoverAt.{uG,uI,uB,uJ,uQ,uX}
      (G := G) (dim := dim) B p P E e t hP δ A T Kproj Kideal Ksite := by
  unfold AllocatedCommonRawCoverAt
  intro c hc J _ U b R σ hR hσ hσt hR1 hRi hσi
  exact exists_original_common_raw_cover.{uG,uI,uB,uJ,uQ,uX}
    B U b hR hσ hp hc hP he hE hdim hmP hpP hvars hI hn hR1 hRi hσi hBlocks
    hδ hδe hKsite hSampling (hraw hc U b hR hσ hσt hR1 hRi hσi)

theorem allocatedCommonRawCoverAt_genuine
    {p P E e t : ℝ} (hP : 0 ≤ P) {δ : ℝ≥0} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {A T Kproj Kideal Ksite : ℕ}
    (hraw : AllocatedCommonRawCoverAt.{uG,uI,uB,uJ,uQ,uX}
      (G := G) (dim := dim) B p P E e t hP δ A T Kproj Kideal Ksite) :
    AllocatedCommonGenuineCoverAt.{uG,uI,uB,uJ,uQ,uX}
      (G := G) (dim := dim) B p P E e t hP δ A T Kproj Kideal Ksite := by
  unfold AllocatedCommonGenuineCoverAt
  intro c hc J _ U b R σ hR hσ hσt hR1 hRi hσi
  obtain ⟨witnesses, hFamily, hCompare⟩ := hraw hc U b hR hσ hσt hR1 hRi hσi
  exact ⟨witnesses, hFamily,
    allocatedGenuineCoverData_of_raw B U b hR hσ _ hP hδ hδ1 witnesses hCompare hFamily⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped ContDiff BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq

variable {m dim : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) (Fin.val j + 1))
local notation "hLayer" => layerSamplerDegree I n
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

def AllocatedRegularizedCommonCover (p P E : ℝ) (hP : 0 ≤ P) (A T : ℝ≥0) (Ksite : ℕ) : Prop :=
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
          AllocatedCommonRawCoverAt.{uG,uI,uB,uJ,uQ,uX}
            (G := G) (dim := dim) B p P E e t hP δ A₀ T₀ Kproj Kideal Ksite ∧
          AllocatedCommonGenuineCoverAt.{uG,uI,uB,uJ,uQ,uX}
            (G := G) (dim := dim) B p P E e t hP δ A₀ T₀ Kproj Kideal Ksite

theorem allocatedRegularizedCommonCover_of_cutoff
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    {p P E : ℝ} (hp : 0 ≤ p) (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hdim : dim ≤ m + 1) (hmP : ((m + 2 : ℕ) : ℝ) ≤ P) (hpP : p ≤ P)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (hBlocks : ∀ j i, siteSpectrumBlockCount m ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    {Ksite : ℕ} (hKsite : 2 ≤ Ksite)
    (hSampling : AllocatedBooleanRowsSampling.{uX,uJ,uG,uI,uB,uQ} m dim Ksite rowTypes rows) :
    AllocatedRegularizedCommonCover.{uG,uI,uB,uJ,uQ,uX}
      (G := G) (dim := dim) B p P E hP A T Ksite := by
  unfold AllocatedRegularizedCommonCover
  intro D target w gainLog ε e eTail
  have htarget : 0 ≤ target := by
    have hs := coefficientErrorSpatialLog_nonneg hP
    dsimp only [target, profileReferenceErrorLog]
    linarith
  have hw : 0 ≤ w := mul_nonneg (Nat.cast_nonneg _) hP
  have hgain : 0 ≤ gainLog :=
    allocatedProfileGainLog_nonneg m (allocatedComparisonDimension_bounds m hp).1 hP hw
  have he : 0 ≤ e := physicalIdealSmoothingLog_nonneg hLayer A T htarget hgain
  have heTail : 0 ≤ eTail :=
    physicalIdealTailLog_nonneg G (G × Option (Fin dim)) hLayer A T m htarget hgain
  obtain ⟨Kideal, hKideal, δ, hδ, hδ1, hδeq, hδe, ht, ht1, A₀, T₀, Kproj, hA₀, hT₀, hKproj, hraw⟩ :=
    exists_allocated_common_residue_weighted_original_mesh.{uG,uI,uB,uJ,uQ,uX}
      (G := G) (dim := dim) B ψ hψ hrange hzero hone A T hLip hTransition
      hp hP (show 0 ≤ E + 1 by linarith) hdim hmP hpP hvars hI hn
  refine ⟨he, heTail, Kideal, hKideal, δ, hδ, hδ1, hδeq, hδe, ht, ht1, ?_,
    A₀, T₀, Kproj, hA₀, hT₀, hKproj, ?_⟩
  · let : ∀ a : LayerSamplerAxis I n, Nonempty (jets a.1) :=
      fun _ => ⟨⟨∅, by simp⟩⟩
    exact physicalIdeal_tail_inverse_le_exp G (G × Option (Fin dim))
      hLayer (fun _ => Nat.succ_pos _) A T m htarget hgain
  · have hcover : AllocatedCommonRawCoverAt.{uG,uI,uB,uJ,uQ,uX}
        (G := G) (dim := dim) B p P E e _ hP δ A₀ T₀ Kproj Kideal Ksite :=
      allocatedCommonRawCoverAt_of_source B hp hP hE he hdim hmP hpP
        hvars hI hn hBlocks hδ hδe hKsite hSampling hraw
    exact ⟨hcover, allocatedCommonRawCoverAt_genuine B hP hδ hδ1 hcover⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped ContDiff BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq

theorem exists_fixed_regularized_common_cover :
    ∃ A : ℝ≥0, 1 ≤ A ∧ ∀ m dim : ℕ, ∃ Ksite : ℕ, 2 ≤ Ksite ∧
      ∀ {G : Type uG} [Fintype G] [DecidableEq G]
        {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
        (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
        {p P E : ℝ}, 0 ≤ p → ∀ hP : 0 ≤ P, 0 ≤ E →
        dim ≤ m + 1 → ((m + 2 : ℕ) : ℝ) ≤ P → p ≤ P →
        (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p →
        (∀ j, (Fintype.card (I j) : ℝ) ≤ p) → (∀ j, (n j : ℝ) ≤ p) →
        (∀ j i, siteSpectrumBlockCount m ≤ Fintype.card (B ⟨j, Sum.inr i⟩)) →
        AllocatedRegularizedCommonCover.{uG,uI,uB,uJ,uQ,uX}
          (G := G) (dim := dim) B p P E hP A scalarSourceTransitionBound Ksite := by
  obtain ⟨A, hA, ψ, hψ, hrange, hzero, hone, hLip⟩ := exists_smooth_sublevel_cutoff
  refine ⟨A, hA, ?_⟩
  intro m dim
  obtain ⟨Ksite, hKsite, hSampling⟩ :=
    exists_allocated_boolean_rows_sampling.{uX,uJ,uG,uI,uB,uQ} m dim
  refine ⟨Ksite, hKsite, ?_⟩
  intro G _ _ I _ n B _ p P E hp hP hE hdim hmP hpP hvars hI hn hBlocks
  exact allocatedRegularizedCommonCover_of_cutoff.{uG,uI,uB,uJ,uQ,uX}
    B ψ hψ hrange hzero hone A scalarSourceTransitionBound hLip scalarSourceTransitionBound_spec.2
    hp hP hE hdim hmP hpP hvars hI hn hBlocks hKsite
    (hSampling (fun j => fullBooleanRowSetFintype dim (j.val + 1)))

end Erdos3.VectorPolynomial

end

end OAI
