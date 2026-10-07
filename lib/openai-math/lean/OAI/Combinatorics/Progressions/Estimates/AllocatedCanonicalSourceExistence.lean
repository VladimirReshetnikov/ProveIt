import OAI.Combinatorics.Progressions.Estimates.AllocatedOriginalCommonResources
import OAI.Combinatorics.Progressions.Estimates.AllocatedUniformCommonCover
import OAI.Combinatorics.Progressions.Probability.FullScalarCubeWindowLaw

namespace OAI

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

def AllocatedCanonicalGenuineData (p g Psp E e pNum Pbase Qraw pAccuracy pSampling O : ℝ) (hP : 0 ≤ Psp)
    (δ : ℝ≥0) (A Kraw Ksite Kgen : ℕ)
    (witnesses : (q : AllocatedRefinedPeriodIndex m Psp) →
      (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
      AllocatedFullGridResidueWitness (dim := dim) B U b S (q.val : ℕ) r.val)
    (M Dwin : ℕ) (hM : 0 < M) (hDwin : 0 < Dwin) (η : ℝ) (hη : 0 < η) : Prop :=
  let Dgeom := allocatedComparisonDimension m p
  let cgeom := g
  let pc := p
  let gc := g
  let Pτ := Psp
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
    (_hCgeom : ∀ j, Cinv j ≤ Real.exp g)
    (_hCovEarly : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp g)
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
    let τ := Real.exp (-Psp)
    let hτ := Real.exp_pos (-Psp)
    let Psamp : ℝ := (dim + 2 : ℕ) * Psp
    let sourceThreshold := (Pfinal + Ksite) ^ Ksite
    let genuineThreshold := (allocatedCutoffSamplingLog m dim Pbase
      (normalizedSiteCutoffBound : ℝ) 0 Psamp + Kgen) ^ Kgen
    let threshold := allocatedCanonicalCubeThreshold Psp sourceThreshold genuineThreshold
    ∀ (N : X → ℕ) (hN : ∀ t, 0 < N t)
    (_hsize : ∀ t, Real.exp threshold ≤ (N t : ℝ))
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
    {rank : ℝ}
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) rank (U j) (poly j))
    (_hRank : Real.exp threshold ≤ rank)
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
    ∃ hnormalizer : |Z - 1| ≤ Real.exp (-Qraw) ∧
      Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z ∧ Z⁻¹ ≤ 2,
    ∃ t : GoodKernel → (X → ℤ) → Fin Mk,
      (∀ x base, kernelPeriodCandidate (m + 1) (t x base) ≤ Mk ^ (m + 1)) ∧
    ∃ F : GoodKernel → (X → ℤ) →
        PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S) →
        AllocatedFiniteIdealData (Fin dim) I n,
      (∀ x base y₀, (F x base y₀).Bounds B U b S rowSets x.val y₀ (refined x) (d x)
        (kernelPeriodCandidate (m + 1) (t x base)) hb o bW hR δ (Real.exp (-idealLog))
        (allocatedFiniteIdealInputLog m Dgeom e idealLog) (layerKernelIndexBound m Mk)) ∧
      (∀ x base,
        let _ : ∀ (r : AllocatedPositiveResidue (dim := dim) B U b S (refined x))
            (a : {a // allocatedGridAxis (I := I) U b S.value a})
            (k : ((witnesses (index x) r).expansion a).Term),
            NeZero (((witnesses (index x) r).expansion a).period k) :=
          fun r a k => ⟨(hgridPeriod (index x) r a k).ne'⟩
        AllocatedCoarseFamilyResources (Kcov := Kcov) (τ := τ)
          B U b S X (modulus x) q (wholeReference x) (witnesses (index x))
          (d x) x.val hMk selection x.property N (kernelPeriodCandidate (m + 1) (t x base))
          (F x base) base (allocatedFiniteIdealInputLog m Dgeom e idealLog)
          Psp pAccuracy w v (E + 2) Dgeom O pc gc Pτ Z) ∧
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
    (∀ (window : G → ℕ) (hwindow : ∀ g, window g ≤ S.value)
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
      kernelLaw.goodPartBaseMean bases Good (fun x hx base => genuine ⟨x, hx⟩ base)‖ ≤ 2 * Real.exp (-E) + η) ∧
    ‖(allocatedOriginalPathLaw B U b hb o hR hσ S X poly hmem N hN hW hτ hξ
        q cells hmass bases _hbases hnormalizer.2.2.1).complexMean (fun z =>
          𝔼 cube : SupportedCube dim (integerBox
            (Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)) :
              Set (LayerSamplerVariables G I n B → ℤ)),
            physicalCubeSiteTest test
              (physicalCubeRootDifferences cube.val.2 cube.val.1 z.1.val z.2.val)) -
      (FiniteProbabilityWeights.pi (fun _ : G =>
        integerScalarCubeWeights (Fin dim) S.value S.positive)).goodPartBaseMean
          bases Good (fun x hx base => genuine ⟨x, hx⟩ base)‖ ≤ 2 * Real.exp (-E) + η

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

theorem allocatedCanonicalGenuineData_of_resources
    {p g Psp E e pNum Pbase Qraw pAccuracy pSampling O : ℝ}
    (hp : 0 ≤ p) (hg : 0 ≤ g) (hP : 0 ≤ Psp) (he : 0 ≤ e) (hE : 0 ≤ E)
    (hpAccuracy : 0 ≤ pAccuracy) (hO : 0 ≤ O)
    (hDsp : allocatedComparisonDimension m p ≤ Psp)
    (hmP : ((m + 2 : ℕ) : ℝ) ≤ Psp) (hPNum : Psp ≤ pNum)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ 2 * p)
    (hRadius : ∀ j, R j = allocatedCommonProductRadius m p g) (hσ1 : ∀ j, σ j ≤ 1)
    (hNumerics : ∀ (_o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
      (C V : Fin m → ℝ≥0), (∀ j, (C j : ℝ) ≤ Real.exp pNum) →
      (∀ j, (V j : ℝ) ≤ Real.exp pNum) → AllocatedSourceNumerics B U b S C V Pbase)
    {δ : ℝ≥0} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδe : (δ : ℝ)⁻¹ ≤ Real.exp e)
    {A Kraw Ksite Kgen : ℕ}
    (witnesses : (q : AllocatedRefinedPeriodIndex m Psp) →
      (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
      AllocatedFullGridResidueWitness (dim := dim) B U b S (q.val : ℕ) r.val)
    (M Dwin : ℕ) (hM : 0 < M) (hDwin : 0 < Dwin) (η : ℝ) (hη : 0 < η)
    (hData : AllocatedOriginalGenuineResourcesData.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ S Psp E e pNum Pbase Qraw pAccuracy pSampling
      (allocatedComparisonDimension m p) g O p g Psp hP δ A Kraw Ksite Kgen
      witnesses M Dwin hM hDwin η hη) :
    AllocatedCanonicalGenuineData.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ S p g Psp E e pNum Pbase Qraw pAccuracy pSampling O hP δ
      A Kraw Ksite Kgen witnesses M Dwin hM hDwin η hη := by
  unfold AllocatedCanonicalGenuineData
  intro Dgeom cgeom pc gc Pτ
  obtain ⟨hgridPeriod, hData⟩ := hData
  refine ⟨hgridPeriod, ?_⟩
  intro w v Pfinal Mk hMk selection hqDim hcard _ hMkPsp hlarge hKgen hSampling
    Kernel Good GoodKernel
  have hpD := (allocatedComparisonDimension_bounds m hp).2.2.1
  have hG : (Fintype.card G : ℝ) ≤ Psp :=
    (Nat.cast_le.mpr (allocatedKernelVariables_card_le_variables (G := G) B)).trans
      (hvars.trans (hpD.trans hDsp))
  have hdimP : ((dim + 1 : ℕ) : ℝ) ≤ Psp :=
    (Nat.cast_le.mpr (show dim + 1 ≤ m + 2 by omega)).trans hmP
  have hDexp : Dgeom ≤ Real.exp Psp :=
    hDsp.trans (by linarith [Real.add_one_le_exp Psp])
  have hP1 : 1 ≤ Psp :=
    (show (1 : ℝ) ≤ (m + 2 : ℕ) by exact_mod_cast (show 1 ≤ m + 2 by omega)).trans hmP
  obtain ⟨d, hd, hdb, modulus, hmodulus, hmodulusSize, hspatial, hcoefficient, hData⟩ :=
    hData selection hqDim hcard hMkPsp hlarge hG hdimP hDexp hpAccuracy he hE hg hO
      hp hg hP hδ hδ1 hδe hKgen hSampling
  let _ : ∀ x, NeZero (d x) := fun x => ⟨(hd x).ne'⟩
  let _ : ∀ x, NeZero (modulus x) := fun x => ⟨(hmodulus x).ne'⟩
  refine ⟨d, hd, hdb, modulus, hmodulus, hmodulusSize, hspatial, hcoefficient, ?_⟩
  intro block _ _ _ _ _ _ hb o Kcov _ bW C V hC hV hCp hVp hCpAccuracy hVpAccuracy
    Cinv hCinv hchart hCgeom hCovEarly μ _ _ ν _ _ _ _ _ μsmall _ _ X _ _ hXPsp q hq hqPsp
    refined index _ W hW indices ξ hξ mesh τ hτ Psamp sourceThreshold genuineThreshold threshold
    N hN hsize poly hpoly hmem rank hrank hRank cells hcells bases hbases hbaseBox
  obtain ⟨hgeom, hvarsD, hID, hnD, hKcov, hradius⟩ :=
    allocatedCanonicalSourceGeometry B U b hb bW hp hg hqDim hvars hI hn hJ
  have hsmall : ∀ j, R j ≤ allocatedProductChartRadius m Dgeom g := by
    intro j
    rw [hRadius j]
    exact hradius
  have htrim := allocatedCanonicalTrim_bounds hP1
  have hτP : 1 / τ ≤ Real.exp pNum := htrim.2.2.trans_le (Real.exp_le_exp.mpr hPNum)
  have hsamp := allocatedCanonicalSampling_bounds dim X hP hXPsp
  have hsizeParts (z : X) := allocatedCanonicalCubeThreshold_bounds Psp sourceThreshold genuineThreshold (hsize z)
  have hRankParts := allocatedCanonicalCubeThreshold_bounds Psp sourceThreshold genuineThreshold hRank
  have hresult := hData block hb o bW C V hC hV hCp hVp hCpAccuracy hVpAccuracy Cinv hCinv hchart
    hgeom hvarsD hID hnD hKcov hCgeom hsmall hRadius hCovEarly hσ1
    μ ν μsmall hXPsp q hq hqPsp hτ hτP htrim.2.2.le htrim.2.1
    (hNumerics o C V hCp hVp) hsamp.1 hsamp.2.1 hsamp.2.2 N hN
    (fun z => (hsizeParts z).1) (fun z => (hsizeParts z).2.2) (fun z => (hsizeParts z).2.1)
    poly hpoly hmem hrank hRankParts.1 hRankParts.2.1 cells hcells bases hbases hbaseBox
  obtain ⟨hmass, hnormalizer, t, ht, F, hF, hresources, hcompare⟩ := hresult
  refine ⟨hmass, hnormalizer, t, ht, F, hF, hresources, ?_⟩
  intro test htest
  refine ⟨hcompare test htest, ?_⟩
  have hDfull : S.value ≤ Dwin * S.value :=
    Nat.le_mul_of_pos_left S.value hDwin
  have hfull := hcompare test htest (fun _ => S.value) (fun _ => le_rfl)
    (fun _ => hDfull) (fun _ => 0) (fun _ _ => 1) (fun _ _ => 0)
    (fun _ _ => Nat.zero_lt_one) (fun _ _ => hM)
  simp only [affineScalarCubeWindowWeights_full_one] at hfull
  rw [allocatedOriginalPathLaw_cube_source]
  exact hfull

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
variable {σ : Fin m → ℝ} (hσ : ∀ j, 0 < σ j)
variable {p g cLate P e E : ℝ} (hp : 0 ≤ p) (hg : 0 ≤ g)

local notation "R" => (fun _ : Fin m => allocatedCommonProductRadius m p g)
local notation "hR" => (fun _ : Fin m => And.left (And.right (allocatedCommonProductRadius_bounds m hp hg)))
local notation "cEarly" => g + allocatedCommonProductRadiusLog m p g

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

include hp hg hσ in
theorem exists_canonical_common_genuine_source
    (hcLate : 0 ≤ cLate) (hEarlyLate : cEarly ≤ cLate)
    (hP : 0 ≤ P) (he : 0 ≤ e) (hE : 0 ≤ E)
    (hdimSmall : dim ≤ m + 1) (hmP : ((m + 2 : ℕ) : ℝ) ≤ P)
    (hDP : allocatedComparisonDimension m p ≤ P)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ 2 * p)
    (hσ1 : ∀ j, σ j ≤ 1) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp cLate)
    (hBlocks : ∀ (j : Fin m) (i : Fin (n j)), max
      (positiveModerateSpectrumBlockCount j.val (rowSets j).card
        ((layerTailDegree m + 2) * (rowSets j).card))
      (uniformSpectrumBlockCount j.val (rowSets j).card ((j.val + 1) * (rowSets j).card)) ≤
      Fintype.card (B ⟨j, Sum.inr i⟩))
    {δ : ℝ≥0} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδe : (δ : ℝ)⁻¹ ≤ Real.exp e)
    {A T Kproj Kideal Ksite Knorm : ℕ} (hT : 1 ≤ T) (hKsite : 2 ≤ Ksite)
    (hKnorm : 1 ≤ Knorm)
    (hnorm : AllocatedSourceNarrowNormalization.{uG,uI,uB,uJ,uX} m Knorm)
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
      ∀ (Kgen : ℕ) (M Dwin : ℕ) (hM : 0 < M) (hDwin : 0 < Dwin) (η : ℝ) (hη : 0 < η),
        AllocatedCanonicalGenuineData.{uG,uI,uB,uJ,uQ,uX}
          B U b hR hσ S p g P E e pNum Pbase
          (allocatedSourceSamplingBudget m dim A Pbase (E + 2) lateLog rawFourier)
          pAccuracy pSampling resourceLog hP δ A
          (max T (max Kproj Kideal)) (max Ksite Knorm) Kgen witnesses
          M Dwin hM hDwin η hη := by
  have hRadius := allocatedCommonProductRadius_bounds m hp hg
  have hcEarly : 0 ≤ cEarly := add_nonneg hg hRadius.1
  have hRi : ∀ j : Fin m, (R j)⁻¹ ≤ Real.exp cEarly := by
    intro j
    rw [hRadius.2.2.2.1]
    exact Real.exp_le_exp.mpr (le_add_of_nonneg_left hg)
  have hpP : p ≤ P := (allocatedComparisonDimension_bounds m hp).2.2.1.trans hDP
  have hEraw : 0 ≤ Eraw := by linarith only [hE]
  have haccuracy : 0 ≤ accuracy := by
    have hs := coefficientErrorSpatialLog_nonneg hP
    unfold allocatedOriginalCoverAccuracy
    linarith
  have hpAccuracy : 0 ≤ pAccuracy :=
    (allocatedCommonRefinedSourceLog_bounds m hp hcEarly hP he (le_refl (0 : ℝ)) haccuracy).1
  have hw : 0 ≤ maskLog := allocatedSiteKernelMaskLog_nonneg m hP
  have hv : 0 ≤ profileLog := allocatedIdealProfileLog_nonneg m hpAccuracy he
  have hresource : 0 ≤ resourceLog := allocatedFullGridPrimitiveResourceLog_nonneg m hpAccuracy hw hv haccuracy
  have hdimensions : AllocatedComparisonDimensions (G := G) B (Fin dim) rowTypes D :=
    allocatedComparisonDimensions_of_primitive B rows
      (by simpa only [Fintype.card_fin] using hdimSmall)
      (fun _ => Subtype.val_injective) hp hvars hI hn
  obtain ⟨hNum, _, hcNum, hPNum, _⟩ := allocatedCommonScaleNumeric_bounds m hp hcLate hP hEraw
  have herror : 0 ≤ error := allocatedReferenceIdealError_nonneg m hdimensions.nonneg hP hEraw
  have hnum : ∀ (_o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
      (C V : Fin m → ℝ≥0), (∀ j, (C j : ℝ) ≤ Real.exp pNum) →
      (∀ j, (V j : ℝ) ≤ Real.exp pNum) → AllocatedSourceNumerics B U b S C V Pbase := by
    intro o C V hCp hVp
    exact allocatedIdealSource_numerics B U b o hdimensions hNum he hw herror hR hσ
      (fun j => ((hRi j).trans (Real.exp_le_exp.mpr hEarlyLate)).trans (Real.exp_le_exp.mpr hcNum))
      (fun j => (hσi j).trans (Real.exp_le_exp.mpr hcNum)) C V hCp hVp
  obtain ⟨witnesses, hBounds, hWitnesses, hData⟩ :=
    exists_original_common_genuine_resource_source B U b hR hσ hp hcEarly hcLate hEarlyLate hP he hE
      hdimSmall hmP hpP hvars hI hn hJ (fun _ => hRadius.2.2.1) hσ1 hRi hσi hBlocks
      hδ hδ1 hδe hT hKsite hKnorm hnorm hSampling hraw
  refine ⟨witnesses, hBounds, hWitnesses, ?_⟩
  intro Kgen M Dwin hM hDwin η hη
  exact allocatedCanonicalGenuineData_of_resources B U b hR hσ S hp hg hP he hE hpAccuracy hresource
    hDP hmP hPNum hvars hI hn hJ (fun _ => rfl) hσ1 hnum hδ hδ1 hδe
    witnesses M Dwin hM hDwin η hη (hData D g p g P Kgen M Dwin hM hDwin η hη)

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

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rowTypes" => (fun j => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

def AllocatedUniversalCanonicalSourceAt (p P E e t : ℝ) (hp : 0 ≤ p) (hP : 0 ≤ P)
    (δ : ℝ≥0) (A T Kproj Kideal Ksite Knorm Kgen : ℕ) : Prop :=
  ∀ {g : ℝ} (hg : 0 ≤ g),
    let hR := fun _ : Fin m => And.left (And.right (allocatedCommonProductRadius_bounds m hp hg))
    let cEarly := g + allocatedCommonProductRadiusLog m p g
    ∀ {cLate : ℝ} (_hcLate : 0 ≤ cLate), cEarly ≤ cLate →
    ∀ {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
      (U : ∀ j, Submodule ℝ (J j → ℝ))
      (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
      {σ : Fin m → ℝ} (hσ : ∀ j, 0 < σ j),
      (∀ j, σ j ≤ t) → (∀ j, (σ j)⁻¹ ≤ Real.exp cLate) →
      (∀ j, (Fintype.card (J j) : ℝ) ≤ 2 * p) →
    let Eraw := (E + 2) + 4
    let accuracy := allocatedOriginalCoverAccuracy P (E + 2)
    let D := allocatedComparisonDimension m p
    let pNum := allocatedCommonScaleNumeric m p cLate P Eraw
    let S := allocatedCommonScale (G := G) B U b hR hσ p cLate P e Eraw
    let pAccuracy := allocatedCommonRefinedSourceLog m p cEarly P e 0 accuracy
    let pSampling := allocatedCommonRefinedSourceLog m p cLate P e Eraw accuracy
    let w := allocatedSiteKernelMaskLog m P
    let v := allocatedIdealProfileLog m pAccuracy e
    let O := allocatedFullGridPrimitiveResourceLog m pAccuracy w v accuracy
    let tolerance := allocatedSitePrimitiveTolerance m pAccuracy w v accuracy
    let error := allocatedReferenceIdealError m D P Eraw
    let lengthLog := allocatedIdealScaleLog m D pNum e w error
    let gainLog := allocatedProfileGainLog m D P w
    let Pbase := allocatedIdealSourceBudget m D pNum e w error
    let lateLog := allocatedSpatialLateLog (G := G) B Pbase Pbase
    let rawFourier := allocatedProfileFourierOutput (allocatedActualProfileInput m D pNum e gainLog lengthLog)
    ∃ witnesses : (q : AllocatedRefinedPeriodIndex m P) →
        (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
        AllocatedFullGridResidueWitness (dim := dim) B U b S (q.val : ℕ) r.val,
      (∀ q r a, ((witnesses q r).expansion a).Bounds
        (Real.exp O) (Real.exp O) (Real.exp O) ⟨Real.exp O, Real.exp_nonneg _⟩
        (Real.exp (allocatedInactiveSupportLog (allocatedComparisonDimension m pAccuracy)))) ∧
      (∀ q r, AllocatedFullGridResidueSampling.{uG,uI,uB,uJ,uQ,uX}
        B U b hR hσ S (q.val : ℕ) (witnesses q r) tolerance) ∧
      ∀ (M Dwin : ℕ) (hM : 0 < M) (hDwin : 0 < Dwin) (η : ℝ) (hη : 0 < η),
        AllocatedCanonicalGenuineData.{uG,uI,uB,uJ,uQ,uX}
          B U b hR hσ S p g P E e pNum Pbase
          (allocatedSourceSamplingBudget m dim A Pbase (E + 2) lateLog rawFourier)
          pAccuracy pSampling O hP δ A (max T (max Kproj Kideal)) (max Ksite Knorm) Kgen
          witnesses M Dwin hM hDwin η hη

theorem allocatedUniversalCanonicalSourceAt_of_mesh
    {p P E e t : ℝ} (hp : 0 ≤ p) (hP : 0 ≤ P) (hE : 0 ≤ E) (he : 0 ≤ e) (ht1 : t ≤ 1)
    (hdim : dim ≤ m + 1) (hmP : ((m + 2 : ℕ) : ℝ) ≤ P)
    (hDP : allocatedComparisonDimension m p ≤ P)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (hBlocks : ∀ (j : Fin m) (i : Fin (n j)), max
      (positiveModerateSpectrumBlockCount j.val (rowSets j).card
        ((layerTailDegree m + 2) * (rowSets j).card))
      (uniformSpectrumBlockCount j.val (rowSets j).card ((j.val + 1) * (rowSets j).card)) ≤
      Fintype.card (B ⟨j, Sum.inr i⟩))
    {δ : ℝ≥0} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδe : (δ : ℝ)⁻¹ ≤ Real.exp e)
    {A T Kproj Kideal Ksite Knorm Kgen : ℕ}
    (hT : 1 ≤ T) (hKsite : 2 ≤ Ksite) (hKnorm : 1 ≤ Knorm)
    (hnorm : AllocatedSourceNarrowNormalization.{uG,uI,uB,uJ,uX} m Knorm)
    (hSampling : AllocatedBooleanRowsSampling.{uX,uJ,uG,uI,uB,uQ} m dim Ksite rowTypes rows)
    (hraw : AllocatedCommonResidueWeightedOriginalMeshAt.{uG,uI,uB,uJ,uQ,uX}
      (G := G) (dim := dim) B p P (E + 2) e t δ A T Kproj Kideal) :
    AllocatedUniversalCanonicalSourceAt.{uG,uI,uB,uJ,uQ,uX}
      (G := G) (dim := dim) B p P E e t hp hP δ A T Kproj Kideal Ksite Knorm Kgen := by
  intro g hg hR cEarly cLate hcLate hEarlyLate J _ U b σ hσ hσt hσi hJ
    Eraw accuracy D pNum S pAccuracy pSampling w v O tolerance error lengthLog gainLog Pbase lateLog rawFourier
  have hradius := allocatedCommonProductRadius_bounds m hp hg
  have hRi : ∀ j : Fin m, (allocatedCommonProductRadius m p g)⁻¹ ≤ Real.exp cLate := by
    intro j
    rw [hradius.2.2.2.1]
    exact Real.exp_le_exp.mpr ((le_add_of_nonneg_left hg).trans hEarlyLate)
  obtain ⟨witnesses, hBounds, hWitnesses, hData⟩ :=
    exists_canonical_common_genuine_source B U b hσ hp hg hcLate hEarlyLate hP he hE
      hdim hmP hDP hvars hI hn hJ (fun j => (hσt j).trans ht1) hσi hBlocks
      hδ hδ1 hδe hT hKsite hKnorm hnorm hSampling
      (hraw hcLate U b hR hσ hσt (fun _ => hradius.2.2.1) hRi hσi)
  refine ⟨witnesses, hBounds, hWitnesses, ?_⟩
  intro M Dwin hM hDwin η hη
  exact hData Kgen M Dwin hM hDwin η hη

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
local notation "rowTypes" => (fun j => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

def AllocatedFlexibleCanonicalSourceAt (p P E : ℝ) (hp : 0 ≤ p) (hP : 0 ≤ P)
    (A T : ℝ≥0) (Ksite Knorm Kgen Kideal A₀ T₀ Kproj : ℕ) : Prop :=
  let D := allocatedComparisonDimension m p
  let target := profileReferenceErrorLog P ((E + 2) + 4)
  let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * P
  let gainLog := allocatedProfileGainLog m D P w
  let ε := physicalIdealErrorShare target gainLog
  let e := physicalIdealSmoothingLog (B := B) (O := fun a : LayerSamplerAxis I n => jets a.1)
    (α := Fin dim) hLayer A T target gainLog
  let eTail := physicalIdealTailLog (B := B) (O := fun a : LayerSamplerAxis I n => jets a.1)
    (α := Fin dim) G (G × Option (Fin dim)) hLayer A T m target gainLog
  0 ≤ e ∧ 0 ≤ eTail ∧
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
        ∀ (e' t' : ℝ), e ≤ e' → t' ≤ t →
          AllocatedUniversalCanonicalSourceAt.{uG,uI,uB,uJ,uQ,uX}
            (G := G) (dim := dim) B p P E e' t' hp hP δ A₀ T₀ Kproj Kideal Ksite Knorm Kgen

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
local notation "rowTypes" => (fun j => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

def AllocatedInitializedCanonicalSourceAt (p P E : ℝ) (hp : 0 ≤ p) (hP : 0 ≤ P)
    (A T : ℝ≥0) (Ksite Knorm Kgen Kideal A₀ T₀ Kproj : ℕ) : Prop :=
  let D := allocatedComparisonDimension m p
  let target := profileReferenceErrorLog P ((E + 2) + 4)
  let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * P
  let gainLog := allocatedProfileGainLog m D P w
  let ε := physicalIdealErrorShare target gainLog
  let e := physicalIdealSmoothingLog (B := B) (O := fun a : LayerSamplerAxis I n => jets a.1)
    (α := Fin dim) hLayer A T target gainLog
  let eTail := physicalIdealTailLog (B := B) (O := fun a : LayerSamplerAxis I n => jets a.1)
    (α := Fin dim) G (G × Option (Fin dim)) hLayer A T m target gainLog
  0 ≤ e ∧ 0 ≤ eTail ∧
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
          AllocatedUniversalCanonicalSourceAt.{uG,uI,uB,uJ,uQ,uX}
            (G := G) (dim := dim) B p P E e t hp hP δ A₀ T₀ Kproj Kideal Ksite Knorm Kgen

def AllocatedInitializedCanonicalSource (p P E : ℝ) (hp : 0 ≤ p) (hP : 0 ≤ P)
    (A T : ℝ≥0) (Ksite Knorm Kgen : ℕ) : Prop :=
  let D := allocatedComparisonDimension m p
  let target := profileReferenceErrorLog P ((E + 2) + 4)
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
          AllocatedUniversalCanonicalSourceAt.{uG,uI,uB,uJ,uQ,uX}
            (G := G) (dim := dim) B p P E e t hp hP δ A₀ T₀ Kproj Kideal Ksite Knorm Kgen

theorem AllocatedInitializedCanonicalSourceAt.to_source
    {p P E : ℝ} {hp : 0 ≤ p} {hP : 0 ≤ P} {A T : ℝ≥0}
    {Ksite Knorm Kgen Kideal A₀ T₀ Kproj : ℕ}
    (hKideal : 2 ≤ Kideal) (hA₀ : 2 ≤ A₀) (hT₀ : 2 ≤ T₀) (hKproj : 2 ≤ Kproj)
    (h : AllocatedInitializedCanonicalSourceAt.{uG,uI,uB,uJ,uQ,uX}
      (G := G) (dim := dim) B p P E hp hP A T Ksite Knorm Kgen Kideal A₀ T₀ Kproj) :
    AllocatedInitializedCanonicalSource.{uG,uI,uB,uJ,uQ,uX}
      (G := G) (dim := dim) B p P E hp hP A T Ksite Knorm Kgen := by
  unfold AllocatedInitializedCanonicalSource
  intro D target w gainLog ε e eTail
  obtain ⟨he, heTail, δ, hδ, hδ1, hδeq, hδe, ht, ht1, hti, hsource⟩ := h
  exact ⟨he, heTail, Kideal, hKideal, δ, hδ, hδ1, hδeq, hδe, ht, ht1, hti,
    A₀, T₀, Kproj, hA₀, hT₀, hKproj, hsource⟩

theorem allocatedInitializedCanonicalSource_of_cutoff
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    {p P E : ℝ} (hp : 0 ≤ p) (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hdim : dim ≤ m + 1) (hmP : ((m + 2 : ℕ) : ℝ) ≤ P)
    (hDP : allocatedComparisonDimension m p ≤ P)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (hBlocks : ∀ (j : Fin m) (i : Fin (n j)), max
      (positiveModerateSpectrumBlockCount j.val (rowSets j).card
        ((layerTailDegree m + 2) * (rowSets j).card))
      (uniformSpectrumBlockCount j.val (rowSets j).card ((j.val + 1) * (rowSets j).card)) ≤
      Fintype.card (B ⟨j, Sum.inr i⟩))
    {Ksite Knorm Kgen : ℕ} (hKsite : 2 ≤ Ksite) (hKnorm : 1 ≤ Knorm)
    (hnorm : AllocatedSourceNarrowNormalization.{uG,uI,uB,uJ,uX} m Knorm)
    (hSampling : AllocatedBooleanRowsSampling.{uX,uJ,uG,uI,uB,uQ} m dim Ksite rowTypes rows) :
    AllocatedInitializedCanonicalSource.{uG,uI,uB,uJ,uQ,uX}
      (G := G) (dim := dim) B p P E hp hP A T Ksite Knorm Kgen := by
  unfold AllocatedInitializedCanonicalSource
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
  have hpP : p ≤ P := (allocatedComparisonDimension_bounds m hp).2.2.1.trans hDP
  obtain ⟨Kideal, hKideal, δ, hδ, hδ1, hδeq, hδe, ht, ht1, A₀, T₀, Kproj, hA₀, hT₀, hKproj, hraw⟩ :=
    exists_allocated_common_residue_weighted_original_mesh.{uG,uI,uB,uJ,uQ,uX}
      (G := G) (dim := dim) B ψ hψ hrange hzero hone A T hLip hTransition
      hp hP (show 0 ≤ E + 2 by linarith) hdim hmP hpP hvars hI hn
  refine ⟨he, heTail, Kideal, hKideal, δ, hδ, hδ1, hδeq, hδe, ht, ht1, ?_,
    A₀, T₀, Kproj, hA₀, hT₀, hKproj, ?_⟩
  · let _ : ∀ a : LayerSamplerAxis I n, Nonempty (jets a.1) :=
      fun _ => ⟨⟨∅, by simp⟩⟩
    exact physicalIdeal_tail_inverse_le_exp G (G × Option (Fin dim))
      hLayer (fun _ => Nat.succ_pos _) A T m htarget hgain
  · exact allocatedUniversalCanonicalSourceAt_of_mesh B hp hP hE he ht1 hdim hmP hDP
      hvars hI hn hBlocks hδ hδ1 hδe (by omega) hKsite hKnorm hnorm hSampling hraw

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped ContDiff BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq

theorem exists_uniform_flexible_canonical_sources :
    ∃ A T : ℝ≥0, 1 ≤ A ∧ 1 ≤ T ∧ ∀ m dim : ℕ,
      let rowSets := fun j : Fin m => boundedBooleanJetRows (Fin dim) (j.val + 1)
      ∃ Ksite Knorm Kgen Kideal A₀ T₀ Kproj : ℕ,
        2 ≤ Ksite ∧ 2 ≤ Knorm ∧ 2 ≤ Kgen ∧
        2 ≤ Kideal ∧ 2 ≤ A₀ ∧ 2 ≤ T₀ ∧ 2 ≤ Kproj ∧
        PhysicalAmbientRowsKernelSampling.{uX,uJ,0} m dim Kgen
          (fun j => (rowSets j : Type)) (fun _ => Subtype.val) ∧
        ∀ {G : Type uG} [Fintype G] [DecidableEq G]
          {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
          (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
          {p P E : ℝ} (hp : 0 ≤ p) (hP : 0 ≤ P), 0 ≤ E →
          dim ≤ m + 1 → ((m + 2 : ℕ) : ℝ) ≤ P → allocatedComparisonDimension m p ≤ P →
          (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p →
          (∀ j, (Fintype.card (I j) : ℝ) ≤ p) → (∀ j, (n j : ℝ) ≤ p) →
          (∀ (j : Fin m) (i : Fin (n j)), max
            (positiveModerateSpectrumBlockCount j.val (rowSets j).card
              ((layerTailDegree m + 2) * (rowSets j).card))
            (uniformSpectrumBlockCount j.val (rowSets j).card ((j.val + 1) * (rowSets j).card)) ≤
            Fintype.card (B ⟨j, Sum.inr i⟩)) →
          AllocatedFlexibleCanonicalSourceAt.{uG,uI,uB,uJ,uQ,uX}
            (G := G) (dim := dim) B p P E hp hP A T Ksite Knorm Kgen Kideal A₀ T₀ Kproj := by
  obtain ⟨A, hA, ψ, hψ, hrange, hzero, hone, hLip⟩ := exists_smooth_sublevel_cutoff
  obtain ⟨T, hT, hTransition⟩ := exists_smoothTransition_lipschitz
  refine ⟨A, T, hA, hT, ?_⟩
  intro m dim rowSets
  obtain ⟨Ksite, hKsite, hSampling⟩ :=
    exists_allocated_boolean_rows_sampling.{uX,uJ,uG,uI,uB,uQ} m dim
  obtain ⟨Knorm, hKnorm, hnorm⟩ :=
    exists_allocatedSourceNarrowNormalization.{uG,uI,uB,uJ,uX} m
  obtain ⟨Kgen, hKgen, hGen⟩ :=
    exists_physical_ambient_rows_kernel_sampling.{uX,uJ,0} m dim
  obtain ⟨Kideal, A₀, T₀, Kproj, hKideal, hA₀, hT₀, hKproj, hsource⟩ :=
    exists_uniform_allocated_flexible_original_mesh.{uG,uI,uB,uJ,uQ,uX} m dim
  refine ⟨Ksite, Knorm, Kgen, Kideal, A₀, T₀, Kproj,
    hKsite, hKnorm, hKgen, hKideal, hA₀, hT₀, hKproj,
    hGen (fun j => fullBooleanRowSetFintype dim (j.val + 1)), ?_⟩
  intro G _ _ I _ n B _ p P E hp hP hE hdim hmP hDP hvars hI hn hBlocks
  unfold AllocatedFlexibleCanonicalSourceAt
  intro D target w gainLog ε e eTail
  have htarget : 0 ≤ target := by
    have hs := coefficientErrorSpatialLog_nonneg hP
    dsimp only [target, profileReferenceErrorLog]
    linarith
  have hw : 0 ≤ w := mul_nonneg (Nat.cast_nonneg _) hP
  have hgain : 0 ≤ gainLog :=
    allocatedProfileGainLog_nonneg m (allocatedComparisonDimension_bounds m hp).1 hP hw
  have he : 0 ≤ e := physicalIdealSmoothingLog_nonneg (layerSamplerDegree I n) A T htarget hgain
  have heTail : 0 ≤ eTail :=
    physicalIdealTailLog_nonneg G (G × Option (Fin dim)) (layerSamplerDegree I n) A T m htarget hgain
  have hpP : p ≤ P := (allocatedComparisonDimension_bounds m hp).2.2.1.trans hDP
  obtain ⟨δ, hδ, hδ1, hδeq, hδe, ht, ht1, hraw⟩ :=
    hsource B ψ hψ hrange hzero hone A T hLip hTransition
      hp hP (show 0 ≤ E + 2 by linarith) hdim hmP hpP hvars hI hn
  refine ⟨he, heTail, δ, hδ, hδ1, hδeq, hδe, ht, ht1, ?_, ?_⟩
  · let _ : ∀ a : LayerSamplerAxis I n,
        Nonempty (BoundedBooleanJet (Fin dim) (a.1.val + 1)) :=
      fun _ => ⟨⟨∅, by simp⟩⟩
    exact physicalIdeal_tail_inverse_le_exp G (G × Option (Fin dim))
      (layerSamplerDegree I n) (fun _ => Nat.succ_pos _) A T m htarget hgain
  · intro e' t' hee htt
    exact allocatedUniversalCanonicalSourceAt_of_mesh B hp hP hE (he.trans hee)
      (htt.trans ht1) hdim hmP hDP hvars hI hn hBlocks hδ hδ1
      (hδe.trans (Real.exp_le_exp.mpr hee)) (by omega) hKsite (by omega) hnorm
      (hSampling (fun j => fullBooleanRowSetFintype dim (j.val + 1))) (hraw e' t' hee htt)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped ContDiff BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq

theorem exists_uniform_initialized_canonical_sources :
    ∃ A T : ℝ≥0, 1 ≤ A ∧ 1 ≤ T ∧ ∀ m dim : ℕ,
      let rowSets := fun j : Fin m => boundedBooleanJetRows (Fin dim) (j.val + 1)
      ∃ Ksite Knorm Kgen Kideal A₀ T₀ Kproj : ℕ,
        2 ≤ Ksite ∧ 2 ≤ Knorm ∧ 2 ≤ Kgen ∧
        2 ≤ Kideal ∧ 2 ≤ A₀ ∧ 2 ≤ T₀ ∧ 2 ≤ Kproj ∧
        PhysicalAmbientRowsKernelSampling.{uX,uJ,0} m dim Kgen
          (fun j => (rowSets j : Type)) (fun _ => Subtype.val) ∧
        ∀ {G : Type uG} [Fintype G] [DecidableEq G]
          {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
          (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
          {p P E : ℝ} (hp : 0 ≤ p) (hP : 0 ≤ P), 0 ≤ E →
          dim ≤ m + 1 → ((m + 2 : ℕ) : ℝ) ≤ P → allocatedComparisonDimension m p ≤ P →
          (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p →
          (∀ j, (Fintype.card (I j) : ℝ) ≤ p) → (∀ j, (n j : ℝ) ≤ p) →
          (∀ (j : Fin m) (i : Fin (n j)), max
            (positiveModerateSpectrumBlockCount j.val (rowSets j).card
              ((layerTailDegree m + 2) * (rowSets j).card))
            (uniformSpectrumBlockCount j.val (rowSets j).card ((j.val + 1) * (rowSets j).card)) ≤
            Fintype.card (B ⟨j, Sum.inr i⟩)) →
          AllocatedInitializedCanonicalSourceAt.{uG,uI,uB,uJ,uQ,uX}
            (G := G) (dim := dim) B p P E hp hP A T Ksite Knorm Kgen Kideal A₀ T₀ Kproj := by
  obtain ⟨A, hA, ψ, hψ, hrange, hzero, hone, hLip⟩ := exists_smooth_sublevel_cutoff
  obtain ⟨T, hT, hTransition⟩ := exists_smoothTransition_lipschitz
  refine ⟨A, T, hA, hT, ?_⟩
  intro m dim rowSets
  obtain ⟨Ksite, hKsite, hSampling⟩ :=
    exists_allocated_boolean_rows_sampling.{uX,uJ,uG,uI,uB,uQ} m dim
  obtain ⟨Knorm, hKnorm, hnorm⟩ :=
    exists_allocatedSourceNarrowNormalization.{uG,uI,uB,uJ,uX} m
  obtain ⟨Kgen, hKgen, hGen⟩ :=
    exists_physical_ambient_rows_kernel_sampling.{uX,uJ,0} m dim
  obtain ⟨Kideal, A₀, T₀, Kproj, hKideal, hA₀, hT₀, hKproj, hsource⟩ :=
    exists_uniform_allocated_common_residue_weighted_original_mesh.{uG,uI,uB,uJ,uQ,uX} m dim
  refine ⟨Ksite, Knorm, Kgen, Kideal, A₀, T₀, Kproj,
    hKsite, hKnorm, hKgen, hKideal, hA₀, hT₀, hKproj,
    hGen (fun j => fullBooleanRowSetFintype dim (j.val + 1)), ?_⟩
  intro G _ _ I _ n B _ p P E hp hP hE hdim hmP hDP hvars hI hn hBlocks
  unfold AllocatedInitializedCanonicalSourceAt
  intro D target w gainLog ε e eTail
  have htarget : 0 ≤ target := by
    have hs := coefficientErrorSpatialLog_nonneg hP
    dsimp only [target, profileReferenceErrorLog]
    linarith
  have hw : 0 ≤ w := mul_nonneg (Nat.cast_nonneg _) hP
  have hgain : 0 ≤ gainLog :=
    allocatedProfileGainLog_nonneg m (allocatedComparisonDimension_bounds m hp).1 hP hw
  have he : 0 ≤ e := physicalIdealSmoothingLog_nonneg (layerSamplerDegree I n) A T htarget hgain
  have heTail : 0 ≤ eTail :=
    physicalIdealTailLog_nonneg G (G × Option (Fin dim)) (layerSamplerDegree I n) A T m htarget hgain
  have hpP : p ≤ P := (allocatedComparisonDimension_bounds m hp).2.2.1.trans hDP
  obtain ⟨δ, hδ, hδ1, hδeq, hδe, ht, ht1, hraw⟩ :=
    hsource B ψ hψ hrange hzero hone A T hLip hTransition
      hp hP (show 0 ≤ E + 2 by linarith) hdim hmP hpP hvars hI hn
  refine ⟨he, heTail, δ, hδ, hδ1, hδeq, hδe, ht, ht1, ?_, ?_⟩
  · let _ : ∀ a : LayerSamplerAxis I n,
        Nonempty (BoundedBooleanJet (Fin dim) (a.1.val + 1)) :=
      fun _ => ⟨⟨∅, by simp⟩⟩
    exact physicalIdeal_tail_inverse_le_exp G (G × Option (Fin dim))
      (layerSamplerDegree I n) (fun _ => Nat.succ_pos _) A T m htarget hgain
  · exact allocatedUniversalCanonicalSourceAt_of_mesh B hp hP hE he ht1 hdim hmP hDP
      hvars hI hn hBlocks hδ hδ1 hδe (by omega) hKsite (by omega) hnorm
      (hSampling (fun j => fullBooleanRowSetFintype dim (j.val + 1))) hraw

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped ContDiff BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq

theorem exists_initialized_canonical_sources :
    ∃ A T : ℝ≥0, 1 ≤ A ∧ 1 ≤ T ∧ ∀ m dim : ℕ,
      let rowSets := fun j : Fin m => boundedBooleanJetRows (Fin dim) (j.val + 1)
      ∃ Ksite Knorm Kgen : ℕ, 2 ≤ Ksite ∧ 2 ≤ Knorm ∧ 2 ≤ Kgen ∧
        PhysicalAmbientRowsKernelSampling.{uX,uJ,0} m dim Kgen
          (fun j => (rowSets j : Type)) (fun _ => Subtype.val) ∧
        ∀ {G : Type uG} [Fintype G] [DecidableEq G]
          {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
          (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
          {p P E : ℝ} (hp : 0 ≤ p) (hP : 0 ≤ P), 0 ≤ E →
          dim ≤ m + 1 → ((m + 2 : ℕ) : ℝ) ≤ P → allocatedComparisonDimension m p ≤ P →
          (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p →
          (∀ j, (Fintype.card (I j) : ℝ) ≤ p) → (∀ j, (n j : ℝ) ≤ p) →
          (∀ (j : Fin m) (i : Fin (n j)), max
            (positiveModerateSpectrumBlockCount j.val (rowSets j).card
              ((layerTailDegree m + 2) * (rowSets j).card))
            (uniformSpectrumBlockCount j.val (rowSets j).card ((j.val + 1) * (rowSets j).card)) ≤
            Fintype.card (B ⟨j, Sum.inr i⟩)) →
          AllocatedInitializedCanonicalSource.{uG,uI,uB,uJ,uQ,uX}
            (G := G) (dim := dim) B p P E hp hP A T Ksite Knorm Kgen := by
  obtain ⟨A, T, hA, hT, hsource⟩ :=
    exists_uniform_initialized_canonical_sources.{uG,uI,uB,uJ,uQ,uX}
  refine ⟨A, T, hA, hT, ?_⟩
  intro m dim rowSets
  obtain ⟨Ksite, Knorm, Kgen, Kideal, A₀, T₀, Kproj,
    hKsite, hKnorm, hKgen, hKideal, hA₀, hT₀, hKproj, hGen, hsource⟩ := hsource m dim
  refine ⟨Ksite, Knorm, Kgen, hKsite, hKnorm, hKgen, hGen, ?_⟩
  intro G _ _ I _ n B _ p P E hp hP hE hdim hmP hDP hvars hI hn hBlocks
  exact (hsource B hp hP hE hdim hmP hDP hvars hI hn hBlocks).to_source
    B hKideal hA₀ hT₀ hKproj

end Erdos3.VectorPolynomial

end

end OAI
