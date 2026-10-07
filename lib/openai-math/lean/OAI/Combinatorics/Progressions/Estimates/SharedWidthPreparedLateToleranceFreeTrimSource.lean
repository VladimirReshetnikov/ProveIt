import OAI.Combinatorics.Progressions.Estimates.PreparedLateToleranceCertifiedSource
import OAI.Combinatorics.Progressions.Estimates.SharedWidthPreparedModularGeneralDirectDetectionFreeTrim

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

section Consumer

variable {m s : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
local notation "selectedRows" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin (s + 1))))
variable (selection : Fin (s + 1) ↪ G) (stride N : Fin nX → ℕ)
variable (Pdetect : Polynomial ℕ) (u pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
local notation "pDetect" => allocatedModelTestLog u pModel
local notation "qDetect" => allocatedModelTestLog u pModel
local notation "Ctail" => (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j))
local notation "Kslice" => Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))
variable (α τ : ℝ)
variable {P : ℝ}

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "jetRows" => selectedRows
local notation "activeB" => (fun a : {a // ¬grid a} => B (Subtype.val a))
local notation "activeDegree" => (fun a : {a // ¬grid a} => degree (Subtype.val a))
local notation "L" => principalAxisLength (fun a => ¬grid a) (allocatedPrincipalSides B U basis S)
local notation "positiveLengths" => (fun j : Tuple => allocatedPrincipalSides_pos B U basis S
  (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j)))

variable (Q : Fin m → Type) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "source" => allocatedCoefficientSource B U basis hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U basis hR hσ S
local notation "reference" => allocatedLongJetReference B U basis S jetRows
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
local notation "jetHaar" => Measure.pi (fun j =>
  @Measure.pi (selectedRows j) _ (fullBooleanRowSetFintype (s + 1) (Fin.val j + 1)) _
    (fun _ : selectedRows j => ν j))
local notation "density" => allocatedCoefficientDensity B U basis hb o hR hσ S

variable [CompactSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable [BorelSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable (μrows : Measure (CoefficientTorus (K := Fin (s + 1)) U))
variable [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]

variable [MeasurableSpace (SiteTorus (Finset (Fin (s + 1))) U)]
variable [BorelSpace (SiteTorus (Finset (Fin (s + 1))) U)]

def PreparedModularGeneralDirectDetectionFreeTrimPreparedSharedWidthInterface
    (Pchart Qstride Pmaster Plate _pGain Pphysical coarseTarget : ℝ) : Prop :=
    ∀ (_hstride : ∀ i, 0 < stride i) (_hstrideBound : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    (C : Fin m → ℝ) (_hC : ∀ j, 0 ≤ C j) (_hCbound : ∀ j, C j ≤ Real.exp Pchart)
    (_hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (Cforward : Fin m → ℝ≥0)
    (_hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) v‖ ≤ Cforward j * ‖v‖)
    (_hForward : ∀ j, (Cforward j : ℝ) ≤ Real.exp Pchart)
    (_hVtail : ∀ j, (Vtail j : ℝ) ≤ Real.exp Pchart)
    (_hVactual : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ Vtail j)
    (_hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Pchart)
    (_hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Pchart),
    ∀ (hτSpatial : 0 < τ), τ⁻¹ ≤ Real.exp Pphysical →
    τ ≤ 1 / 2 → (nX : ℝ) * τ ≤ 1 / 2 →
    let r := preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m s) (s + 1) Pmaster Plate
    let W := allocatedPhysicalRootBudget B U basis S (fun _ => 0)
    ∀ {ξn : ℝ} (hξn : 0 < ξn), ξn ≤ normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection
      (allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α)
      Pphysical coarseTarget → ξn⁻¹ ≤ Real.exp Plate →
    let hW := allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0)
    ∀ (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
      (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
      (_hp : ∀ j, DegreeLE (1 : (Fin nX) → ℕ) (j.val + 1) (poly j))
      (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
      {Rrank : ℝ},
    (∀ i, Real.exp r.required ≤ (N i : ℝ)) →
    (∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
    Real.exp r.required ≤ Rrank →
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξn N
    cells.Nonempty →
    let bases := trimmedIntegerBox N (spatialTrimMargin τ N)
    let Z := selectedJointDensityMass bases stride cells V
      (allocatedJointBaseDensity B U basis hb o hR hσ S (Fin nX) poly hmem)
    ∃ (hN : ∀ i, 0 < N i) (hbases : bases.Nonempty) (hbox : (integerBox N).Nonempty)
      (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z)
      (hnormalizer : |Z - 1| ≤ Real.exp (-r.E) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z ∧ Z⁻¹ ≤ 2)
      (_hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i),
    let Path := bases × rectangularWeightIndices 0 V 1
    let pathLaw := allocatedOriginalPathLaw B U basis hb o hR hσ S (Fin nX) poly hmem N
      hN hW hτSpatial hξn stride cells hmass bases hbases hnormalizer.2.2.1
    let sides := Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S)
    let Sites := integerBox sides
    let e : Sites → LayerSamplerVariables G I n B → ℤ := Subtype.val
    ∀ {Tests : Path → Type} [∀ z, Nonempty (Tests z)]
      {Ldetect : ∀ z, Tests z → Type} [∀ z j, LieRing (Ldetect z j)] [∀ z j, LieAlgebra ℚ (Ldetect z j)]
      {dims : ∀ z, Tests z → ℕ}
      [∀ z j, TopologicalSpace (ℝ ⊗[ℚ] Ldetect z j)]
      [∀ z j, IsTopologicalAddGroup (ℝ ⊗[ℚ] Ldetect z j)]
      [∀ z j, ContinuousSMul ℝ (ℝ ⊗[ℚ] Ldetect z j)] [∀ z j, T2Space (ℝ ⊗[ℚ] Ldetect z j)]
      (Ddetect : ∀ z j, RationalFilteredNilmanifold (Ldetect z j) s (dims z j))
      (Vdetect : ∀ z j, (Ddetect z j).Niltest (fun _ : LayerSamplerVariables G I n B => 1))
      (slices : ∀ z, Tests z → Finset Sites)
      (cdetect : ∀ z, Tests z → LayerSamplerVariables G I n B → ℤ)
      (stepdetect : ∀ z, Tests z → ℕ)
      (Hdetect : ∀ z, Tests z → LayerSamplerVariables G I n B → ℕ),
    (∀ z j, 0 < stepdetect z j) →
    (∀ z j, (slices z j).image e = commonStrideBox (cdetect z j) (stepdetect z j) (Hdetect z j)) →
    (∀ z j, IsDenseCommonStrideBox
      (Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S)) pSlice ((slices z j).image e)) →
    (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pdetect.eval₂ (Nat.castRingHom ℝ) qDetect →
    (∀ z j, (Vdetect z j).ComplexityLE (Pdetect.eval₂ (Nat.castRingHom ℝ) qDetect)) →
    (∀ z j, ((Vdetect z j).normBound : ℝ) ≤ 1) →
    let budget := r.nativeBudget
    ∀ (signal : (Fin nX → ℤ) → ℂ),
    (∀ t, ‖signal t‖ ≤ 1) → (∀ t, t ∉ integerBox N → signal t = 0) →
    α ≤ sampledSliceSeminorm pathLaw
      (fun z t => jointIntegerPhysicalSite (e t) (z.1.val, z.2.val)) slices
      (fun z j t => star ((Vdetect z j).eval
        (commonStrideIndex (cdetect z j) (stepdetect z j) (e t)))) signal →
    ∃ twistData : NormalizedPolynomialTwist (Fin nX) (Σ j, J j)
      (Real.exp budget) (Real.exp budget) ⟨Real.exp budget, Real.exp_nonneg _⟩,
      ∃ Fnative : integerBox N → ℂ,
        Nonempty (NativeSampleModel (fun _ : Fin nX => 1) s budget
          (fun t : integerBox N => t.val) Fnative) ∧
        Real.exp (-budget) ≤
          ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) hbox).correlation
            (fun t => signal t.val) (fun t => star (twistData.eval N poly t.val) * Fnative t)‖

end Consumer

theorem exists_preparedModularGeneralDirectDetectionLateFloorFreeTrim_sharedWidth (m s : ℕ) (Pdetect : Polynomial ℕ) :
    let Cdetect := sampledSupportedSlicedDetectionConstant s Pdetect
    let Cresource := Classical.choose (exists_preparedModularGeneral_uniform_resource_budget m)
    let Aalloc := Classical.choose (exists_preparedModularCanonicalDetectorAllocationBudget m)
    let Cgeom := Classical.choose (exists_detected_canonical_native_source_geometry.{0,0,0,0,0} m s Cdetect)
    let Aearly := Classical.choose (exists_preparedModularGeneralCanonicalEarlyParameters m s Cdetect)
    let Cphysical := Classical.choose (exists_detectedCanonicalPhysicalBudget m Aearly Cgeom)
    ∃ C Cscale : ℕ, 2 ≤ C ∧ 2 ≤ Cscale ∧
    ∀ {X J₀ : Type} (L : RankPreparationFamily X J₀ m) {M nX : ℕ},
      (∀ j, Fintype.card (L j).Coord ≤ M) →
      ∀ {P pSlice u Qstride : ℝ},
      0 < m → ∀ hs : s ≤ m, 0 ≤ P → (M : ℝ) ≤ P →
      pSlice ∈ Set.Icc 0 P → u ∈ Set.Icc 0 P → Qstride ∈ Set.Icc 0 P → (nX : ℝ) ≤ P →
      let Jalloc := modularInitialBlockCount m (nX + m * M)
      let pnum : ℝ := enlargedPreparedCommonSamplerDimension m M Jalloc
      let Palloc := (P + Aalloc) ^ Aalloc
      let G := EnlargedPreparedCommonKernel m Jalloc
      let I := PreparedSamplerContinuous L
      let n := preparedSamplerTransverse L
      let B := EnlargedPreparedCommonSamplerBlock L Jalloc
      let selection := enlargedPreparedCommonCanonicalSelection m Jalloc s hs
      let A := Classical.choose (exists_allocatedCanonicalSlice_early_radius.{0,0,0,0} m)
      let Pearly := Palloc + (2 * Palloc + A) ^ A + 2
      let rowSets := fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)
      let _T := allocatedIdealCoverSupport (G := G) B rowSets
      let _siteRadius := allocatedProductIdealSiteRadius (G := G) B rowSets
      let pModel := allocatedEarlyModelLog Pearly pSlice (Fintype.card (LayerSamplerVariables G I n B))
      let pDetect := allocatedModelTestLog u pModel
      let aDetect := 2 * u + 4 * pModel + 7
      let D := allocatedComparisonDimension m pnum
      let gainLog := slicedDetectionGainLog s Cdetect (Fintype.card (LayerSamplerVariables G I n B)) pDetect pDetect aDetect
      let Pk := scalarKernelLogarithmicBudget (Fin (s + 1)) G (gainLog + pDetect + 4)
      let Qearly := (Palloc + Aearly) ^ Aearly
      let Pphysical := Qearly + Pk + Qstride + nX + (m + 1 : ℕ) + 8
      let coarseTarget := gainLog + 32
      let Eextra := coefficientErrorSpatialLog Pphysical + 8
      let target := gainLog + 32 + Eextra
      let τ := Real.exp (-Pphysical)
      let Rspatial := spatialPrimitiveEnvelope Pphysical coarseTarget 0
      let ξLog := 2 * (Rspatial + spatialTupleToleranceLog Rspatial) + 4
      let F := pDetect + 2
      let _Tmod := ((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride
      let _δ := Real.exp (-(pDetect + 1))
      let E := target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5
      let _η := Real.exp (-E)
      let Prho := 2 * affineProfileInputEnvelope D (canonicalSublevelCutoffLip : ℝ)
        (canonicalTransitionLip : ℝ) E F + 2
      let Ptail := affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) E F
      let _K := Classical.choose (exists_allocatedAffineScaleLog_bound m)
      let geometryBudget := (Palloc + Eextra + Cgeom) ^ Cgeom
      let sourceBudget := (Palloc + Cphysical) ^ Cphysical
      let totalBudget := (P + C) ^ C
      P ≤ Palloc ∧ pnum ≤ Palloc ∧ geometryBudget ≤ sourceBudget ∧ sourceBudget ≤ totalBudget ∧
      Pphysical ∈ Set.Icc 0 sourceBudget ∧ coarseTarget ∈ Set.Icc 0 sourceBudget ∧
      ξLog ∈ Set.Icc 0 sourceBudget ∧ 0 ≤ Eextra ∧
      coarseTarget + coefficientErrorSpatialLog Pphysical + 8 = target ∧
      0 < τ ∧ τ ≤ 1 / 2 ∧ (nX : ℝ) * τ ≤ 1 / 2 ∧ 1 / τ = Real.exp Pphysical ∧
      (s + 1) * (s + 3) ≤ Fintype.card G ∧
      (∀ h : ℕ, h ≤ m → h * Jalloc ≤ Fintype.card G) ∧
      (∀ a : LayerSamplerAxis I n, Jalloc ≤ Fintype.card (B a)) ∧
      (∀ a : LayerSamplerAxis I n, (rowSets a.1).card ≤ Fintype.card (B a)) ∧
      (∀ i, (selection i).val = i.val) ∧
      (∀ inactive : LayerSamplerAxis I n → Prop,
        (∑ j : Fin m, Fintype.card (AllocatedCongruenceRankOutput (Fin nX) I inactive j)) ≤
          nX + m * M) ∧
      ⌈2 * ((modularInitialRankStrength m (nX + m * M) : ℝ) + (nX + m * M : ℕ) + 10) /
        modularRankSmallBallExponent m⌉₊ ≤ Jalloc ∧
      ∃ (pRadius : ℝ) (R : Fin m → ℝ),
      pRadius ∈ Set.Icc 0 Pearly ∧ pRadius ≤ geometryBudget ∧
      (∀ j, 0 < R j ∧ R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
      pModel ∈ Set.Icc 0 geometryBudget ∧ pDetect ∈ Set.Icc 0 geometryBudget ∧
      aDetect ∈ Set.Icc 0 geometryBudget ∧ target ∈ Set.Icc 0 geometryBudget ∧
      D ∈ Set.Icc 0 geometryBudget ∧ gainLog ∈ Set.Icc 0 geometryBudget ∧
      Pk ∈ Set.Icc 0 geometryBudget ∧ Prho ∈ Set.Icc 0 geometryBudget ∧
      Ptail ∈ Set.Icc 0 geometryBudget ∧
      (∀ Vtail : Fin m → ℝ≥0, (∀ j, (Vtail j : ℝ) ≤ Real.exp Palloc) →
        (probabilityProfileLipschitz : ℝ) ≤ Real.exp Palloc →
        let Ctail := 4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j)
        let α := allocatedModelUnitThreshold u pModel
          (Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))) Ctail
        Ctail ≤ Real.exp pModel ∧ Real.exp (-aDetect) ≤ α) ∧
      ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      ∀ (Lmin : ℕ) {W Qw Pmin : ℝ}, 1 ≤ W → 0 ≤ Qw → W ≤ Real.exp Qw →
      0 ≤ Pmin → (Lmin : ℝ) ≤ Real.exp Pmin →
      ∀ {J : Fin m → Type} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ),
        let Pscale := pRadius + Ptail
        ∃ S : LayerSamplerScale (G := G) B U basis R (fun _ => t),
          Pscale ∈ Set.Icc 0 geometryBudget ∧ Pk ≤ Pscale ∧ Lmin ≤ S.value ∧
          (S.value : ℝ) ≤ Real.exp (allocatedWitnessScaleLog geometryBudget Qw +
            (1 + geometryBudget ^ 2) * Pmin) ∧
          (S.value : ℝ) ≤ Real.exp ((P + Qw + Pmin + Cscale) ^ Cscale) ∧
          (∀ j i, S.value ^ (j.val + 1) < basisAxisScale (basis j) i →
            8 * (probabilityProfileLipschitz : ℝ) * W ≤
              (layerSamplerGapWidth (G := G) B R ⟨j, i⟩ / 2) *
                ((basisAxisScale (basis j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) ∧
          Nonempty (AllocatedEarlyNativeSourceGeometryGeneral (B := B) (U := U)
            (basis := basis) (S := S) (s := s) (nX := nX)
            Palloc Pscale D target Pk Prho Qstride pDetect (Real.toNNReal (Real.exp pRadius))) ∧
          (∀ lateTarget : ℝ, coarseTarget ≤ lateTarget →
            let Plate := preparedModularGeneralDetectorLateMaster sourceBudget geometryBudget Qw Pphysical lateTarget +
              (1 + geometryBudget ^ 2) * Pmin
            let resources := preparedModularGeneralDetectorResources
              (preparedModularGeneralDetectorConstants m s) (s + 1) sourceBudget Plate
            resources.nativeBudget ∈ Set.Icc 0 ((2 * sourceBudget + Cresource) ^ Cresource) ∧
            resources.required ∈ Set.Icc 0 ((sourceBudget + Plate + Cresource) ^ Cresource) ∧
            resources.nativeBudget = (preparedModularGeneralDetectorResources
              (preparedModularGeneralDetectorConstants m s) (s + 1) sourceBudget sourceBudget).nativeBudget ∧
            (∀ (hRpos : ∀ j, 0 < R j) (hσpos : ∀ _j : Fin m, 0 < t)
              (stride N : Fin nX → ℕ)
              (Q : Fin m → Type) [∀ j, Fintype (Q j)]
              (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
              (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
              (_bW : ∀ j, Module.Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
              [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
              (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
                (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
              [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
              [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
              [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
              [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
              (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
              [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
              [CompactSpace (CoefficientTorus (K := Fin (s + 1)) U)]
              [MeasurableSpace (CoefficientTorus (K := Fin (s + 1)) U)]
              [BorelSpace (CoefficientTorus (K := Fin (s + 1)) U)]
              (μrows : Measure (CoefficientTorus (K := Fin (s + 1)) U))
              [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]
              [MeasurableSpace (SiteTorus (Finset (Fin (s + 1))) U)]
              [BorelSpace (SiteTorus (Finset (Fin (s + 1))) U)]
              (Vtail : Fin m → ℝ≥0) (α τfree : ℝ),
              Real.exp (-aDetect) ≤ α → α ≤ 1 →
              PreparedModularGeneralDirectDetectionFreeTrimPreparedSharedWidthInterface
                (B := B) (U := U) (basis := basis) (S := S) (hR := hRpos) (hσ := hσpos)
                (selection := selection) (stride := stride) (N := N)
                (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail) (α := α) (τ := τfree)
                (hb := hb) (o := o) Palloc Qstride sourceBudget Plate gainLog Pphysical lateTarget)) ∧
          ∀ α : ℝ, Real.exp (-aDetect) ≤ α →
            Real.exp (-gainLog) ≤
              (Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (s + 1)) ∧
            (scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
              (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (s + 1))) / 2) : ℝ) ≤ Real.exp Pk ∧
            scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
              (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (s + 1))) / 2) ≤ S.value := by
  intro Cdetect Cresource Aalloc Cgeom Aearly Cphysical
  obtain ⟨C, hC, hsource⟩ := exists_preparedModularGeneralCanonicalLateFloorPhysicalSource m s Cdetect
  obtain ⟨Cscale, hCscale, hScaleBudget⟩ := exists_preparedModularGeneralLateFloorScale_budget C
  refine ⟨C, Cscale, hC, hCscale, ?_⟩
  intro X J₀ L M nX hCoord P pSlice u Qstride hm hs hP hM hpSlice hu hQstride hnX
    Jalloc pnum Palloc G I n B selection A Pearly rowSets T siteRadius pModel pDetect aDetect D
    gainLog Pk Qearly Pphysical coarseTarget Eextra target τ Rspatial ξLog F Tmod δ E η Prho Ptail K
    geometryBudget sourceBudget totalBudget
  obtain ⟨hPalloc, hnum, hGeometryBudget, hTotalBudget, hPhysicalMaster, hCoarseMaster,
      hXiMaster, hExtra, hprecision, hτ, hτhalf, hτdim, hτinv,
      hcapacity, hkernelAllocation, hblockAllocation, hblockRows, hselection, houtputCount,
      hthreshold, pRadius, R, hpRadius, hpRadiusGeometry, hR,
      hModelGeometry, hDetectGeometry, haGeometry, hTargetGeometry, hDGeometry, hGainGeometry,
      hPkGeometry, hPrhoGeometry, hPtailGeometry, hTailCap, t, ht, htone, hsampler⟩ :=
    hsource L hCoord hm hs hP hM hpSlice hu hQstride hnX
  refine ⟨hPalloc, hnum, hGeometryBudget, hTotalBudget, hPhysicalMaster, hCoarseMaster,
    hXiMaster, hExtra, hprecision, hτ, hτhalf, hτdim, hτinv,
    hcapacity, hkernelAllocation, hblockAllocation, hblockRows, hselection, houtputCount,
    hthreshold, pRadius, R, hpRadius, hpRadiusGeometry, hR,
    hModelGeometry, hDetectGeometry, haGeometry, hTargetGeometry, hDGeometry, hGainGeometry,
    hPkGeometry, hPrhoGeometry, hPtailGeometry, hTailCap, t, ht, htone, ?_⟩
  intro Lmin Wscale Qw Pmin hWscale hQw hWQw hPmin hLmin J _ U basis Pscale
  obtain ⟨S, hScaleGeometry, hPkScale, hFloor, hSWitness, hgap, ⟨geometry⟩, hgainKernel⟩ :=
    hsampler Lmin hWscale hQw hWQw hPmin hLmin U basis
  have hGeometry0 : 0 ≤ geometryBudget := hModelGeometry.1.trans hModelGeometry.2
  have hScalePolynomial := hSWitness.trans (Real.exp_le_exp.mpr
    (hScaleBudget hP hQw hPmin hGeometry0 (hGeometryBudget.trans hTotalBudget)))
  refine ⟨S, hScaleGeometry, hPkScale, hFloor, hSWitness, hScalePolynomial,
    hgap, ⟨geometry⟩, ?_, hgainKernel⟩
  intro lateTarget hCoarseLower Plate resources
  have hAlloc0 : 0 ≤ Palloc := hP.trans hPalloc
  have hMaster : 0 ≤ sourceBudget := hPhysicalMaster.1.trans hPhysicalMaster.2
  have hLateTarget0 : 0 ≤ lateTarget := hCoarseMaster.1.trans hCoarseLower
  obtain ⟨_, hLateBase, hWitnessBase, hCoarseBase, hXiBase⟩ :=
    preparedModularGeneralDetectorLateMaster_bounds hMaster hGeometry0 hQw hPhysicalMaster.1 hLateTarget0
  have hFloorCost : 0 ≤ (1 + geometryBudget ^ 2) * Pmin := by positivity
  have hBaseLate : preparedModularGeneralDetectorLateMaster sourceBudget geometryBudget Qw Pphysical lateTarget ≤ Plate :=
    le_add_of_nonneg_right hFloorCost
  have hLate := hLateBase.trans hBaseLate
  have hWitnessLate : allocatedWitnessScaleLog geometryBudget Qw + (1 + geometryBudget ^ 2) * Pmin ≤ Plate :=
    add_le_add hWitnessBase (le_refl ((1 + geometryBudget ^ 2) * Pmin))
  have hCoarseLate := hCoarseBase.trans hBaseLate
  have hXiLate := hXiBase.trans hBaseLate
  obtain ⟨hNativeResource, hRequiredResource⟩ :=
    (Classical.choose_spec (exists_preparedModularGeneral_uniform_resource_budget m)).2
      hMaster hLate ⟨s, Nat.lt_succ_of_le hs⟩
  refine ⟨hNativeResource, hRequiredResource, rfl, ?_⟩
  intro hRpos hσpos stride N Q _ hb o bW _ ν _ _ _ _ _ μ _ _ _ _ _ μrows _ _ _ _ Vtail α τfree hαlower hαone
    hstride hstrideBound Cchart hCchart hCchartBound hchart Cforward hforward
    hForward hVtail hVactual hprofile hcutoff hτfree hτfreeInv hτfreeHalf hτfreeDim
  have hCphysical : 2 ≤ Cphysical :=
    (Classical.choose_spec (exists_detectedCanonicalPhysicalBudget m Aearly Cgeom)).1
  have hAllocMaster : Palloc ≤ sourceBudget := by
    have hbase : 1 ≤ Palloc + Cphysical := by
      have hcast : (2 : ℝ) ≤ Cphysical := Nat.cast_le.mpr hCphysical
      linarith only [hAlloc0, hcast]
    exact (le_add_of_nonneg_right (Nat.cast_nonneg Cphysical)).trans
      (le_self_pow₀ hbase (by omega))
  have liftMaster {x : ℝ} (hx : x ∈ Set.Icc 0 geometryBudget) : x ∈ Set.Icc 0 sourceBudget :=
    ⟨hx.1, hx.2.trans hGeometryBudget⟩
  have hModelMaster := liftMaster hModelGeometry
  have hDetectMaster := liftMaster hDetectGeometry
  have hTargetMaster := liftMaster hTargetGeometry
  have hDMaster := liftMaster hDGeometry
  have hGainMaster := liftMaster hGainGeometry
  have hPkMaster := liftMaster hPkGeometry
  have hPrhoMaster := liftMaster hPrhoGeometry
  have hScaleMaster := liftMaster hScaleGeometry
  have hpRadiusMaster := hpRadiusGeometry.trans hGeometryBudget
  have hSLate := hSWitness.trans (Real.exp_le_exp.mpr hWitnessLate)
  have hPMaster : P ≤ sourceBudget := hPalloc.trans hAllocMaster
  have hExpMaster : Real.exp Palloc ≤ Real.exp sourceBudget := Real.exp_le_exp.mpr hAllocMaster
  obtain ⟨_, hSliceModel, _, _, _, _, _, hcountModel, _, _, _, _, _, _, _, _⟩ :=
    preparedModularCanonicalDetector_early_cap L Jalloc A hCoord hAlloc0 hnum hpSlice.1 hu.1
      R Vtail hRpos (fun j => (hR j).2.2) hpRadius.2 hVtail hprofile
  have hMk := (hgainKernel α hαlower).2
  have hMkPk : (allocatedDetectedKernelCutoff s G
      (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect pDetect
      α : ℝ)
      ≤ Real.exp Pk := hMk.1
  have hMkP := hMkPk.trans (Real.exp_le_exp.mpr hPkScale)
  have hKMaster : (Real.toNNReal (Real.exp pRadius) : ℝ) ≤ Real.exp sourceBudget := by
    rw [Real.coe_toNNReal (Real.exp pRadius) (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr hpRadiusMaster
  have hAearly : 2 ≤ Aearly :=
    (Classical.choose_spec (exists_preparedModularGeneralCanonicalEarlyParameters m s Cdetect)).1
  have hQearly0 : 0 ≤ Qearly := by dsimp only [Qearly]; positivity
  have hAllocQ : Palloc ≤ Qearly := by
    have hbase : 1 ≤ Palloc + Aearly := by
      have hcast : (2 : ℝ) ≤ Aearly := Nat.cast_le.mpr hAearly
      linarith only [hAlloc0, hcast]
    exact (le_add_of_nonneg_right (Nat.cast_nonneg Aearly)).trans
      (le_self_pow₀ hbase (by omega))
  have hQPhysical : Qearly ≤ Pphysical := by
    dsimp only [Pphysical]
    linarith only [hPkMaster.1, hQstride.1, Nat.cast_nonneg (α := ℝ) nX,
      Nat.cast_nonneg (α := ℝ) (m + 1)]
  have hmPhysical : ((m + 1 : ℕ) : ℝ) ≤ Pphysical := by
    dsimp only [Pphysical]
    linarith only [hQearly0, hPkMaster.1, hQstride.1, Nat.cast_nonneg (α := ℝ) nX]
  have hDimPhysical : ((s + 2 : ℕ) : ℝ) ≤ Pphysical := by
    have hsm : (s : ℝ) ≤ m := Nat.cast_le.mpr hs
    dsimp only [Pphysical]
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    linarith only [hQearly0, hPkMaster.1, hQstride.1, Nat.cast_nonneg (α := ℝ) nX, hsm]
  have hXPhysical : (nX : ℝ) ≤ Pphysical := by
    dsimp only [Pphysical]
    linarith only [hQearly0, hPkMaster.1, hQstride.1, Nat.cast_nonneg (α := ℝ) (m + 1)]
  have hPkPhysical : Pk ≤ Pphysical := by
    dsimp only [Pphysical]
    linarith only [hQearly0, hQstride.1, Nat.cast_nonneg (α := ℝ) nX,
      Nat.cast_nonneg (α := ℝ) (m + 1)]
  have hQstridePhysical : Qstride ≤ Pphysical := by
    dsimp only [Pphysical]
    linarith only [hQearly0, hPkMaster.1, Nat.cast_nonneg (α := ℝ) nX,
      Nat.cast_nonneg (α := ℝ) (m + 1)]
  have hvarsPhysical : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pphysical :=
    (Nat.cast_le.mpr (enlargedPreparedCommonSampler_dimensions L Jalloc hCoord).1).trans
      (hnum.trans (hAllocQ.trans hQPhysical))
  intro r W ξn hξn hξle hξInvLate hW cells poly hp hmem Rrank hNlarge hrank hRankLarge V
    hcells bases Z
  have hτInvMaster : τfree⁻¹ ≤ Real.exp sourceBudget :=
    hτfreeInv.trans (Real.exp_le_exp.mpr hPhysicalMaster.2)
  have hξone := hξle.trans (preparedModularCanonicalDetector_narrow_width_le_one (Fin nX)
    (PrincipalTupleIndex B (layerSamplerDegree I n)) selection
    (allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B))
      Pdetect pDetect pDetect α)
    Pphysical lateTarget)
  obtain ⟨hNpos, hbases, hbox, hmass, hnormalizer, hmargin⟩ :=
    preparedModularGeneralDetector_late_positive_bounds B U basis S hb o μ ν hRpos hσpos
      (fun _ => htone) Cforward Vtail hforward hVactual Cchart hCchart hchart
      (geometry.hbudgets Cchart hCchart hCchartBound).1 hMaster hLate geometry.hdimensions
      hDMaster.2 (hnX.trans hPMaster)
      (fun j => (hR j).2.2.trans (Real.exp_le_exp.mpr hpRadiusMaster))
      (fun j => (geometry.hσi j).trans (Real.exp_le_exp.mpr (hScaleMaster.2.trans hLate))) hSLate
      (fun j => (hForward j).trans hExpMaster) (fun j => (hVtail j).trans hExpMaster)
      poly hp hmem stride hstride
      (fun i => (hstrideBound i).trans (Real.exp_le_exp.mpr (hQstride.2.trans hPMaster)))
      hτfree hτInvMaster hτfreeHalf hτfreeDim hξn hξone hξInvLate
      N hrank cells hcells hNlarge hRankLarge
  let : ∀ i, NeZero (N i) := fun i => ⟨(hNpos i).ne'⟩
  have consumer := preparedModularGeneralDirectDetectionFreeTrimSharedWidthInterface_of_geometry
    (B := B) (U := U) (basis := basis) (hR := hRpos) (hσ := hσpos) (S := S) (P := Pscale)
    (selection := selection) (stride := stride) (N := N)
    (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail) (α := α) (τ := τfree)
    (Q := Q) (hb := hb) (o := o) (bW := bW) (μ := μ) (ν := ν) (μrows := μrows)
    hs Palloc D target Pk Prho Qstride sourceBudget Plate gainLog Pphysical lateTarget
    (Real.toNNReal (Real.exp pRadius)) geometry
  have completed := consumer hLate hMaster hDMaster.2 hPkMaster
    ⟨hQstride.1, hQstride.2.trans hPMaster⟩ hDetectMaster (hnX.trans hPMaster)
    (fun j => (hR j).2.1)
    (fun j => (hR j).2.2.trans (Real.exp_le_exp.mpr hpRadiusMaster))
    (fun j => (geometry.hσi j).trans (Real.exp_le_exp.mpr (hScaleMaster.2.trans hLate)))
    hSLate hKMaster (hcutoff.trans hExpMaster) hMkP hMkPk hstride hstrideBound
    Cchart hCchart hCchartBound hchart Cforward hforward
    (fun j => (hForward j).trans hExpMaster) (fun j => (hVtail j).trans hExpMaster) hVactual
    (fun j i => enlargedPreparedCommonSamplerBlock_positiveModerate L Jalloc s hs ⟨j, Sum.inr i⟩)
    (fun j i => enlargedPreparedCommonSamplerBlock_uniform L Jalloc s hs ⟨j, Sum.inr i⟩)
    ⟨hu.1, hu.2.trans hPMaster⟩ hModelMaster hSliceModel hcountModel hαlower hαone
    hPrhoMaster hTargetMaster hGainMaster hCoarseMaster.2 hCoarseLower hCoarseLate hPhysicalMaster
    hmPhysical hDimPhysical hvarsPhysical hXPhysical hPkPhysical hQstridePhysical
    (le_refl _) hprecision.le hXiLate hτfree hτfreeInv hξn hξle hξInvLate
  refine ⟨hNpos, hbases, hbox, hmass, hnormalizer, hmargin, ?_⟩
  intro Path pathLaw sides Sites e Tests _ Ldetect _ _ dims _ _ _ _
    Ddetect Vdetect slices cdetect stepdetect Hdetect hstep hboxDetect hdense hcount hcomplexity hnorm
    budget'
  exact completed cells poly hp hmem hNlarge hrank hRankLarge hcells hbases hmass
    hnormalizer.2.2.1 Ddetect Vdetect slices cdetect stepdetect Hdetect hstep hboxDetect hdense hcount
    hcomplexity hnorm hcapacity hMk.2

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

section Consumer

variable {m s : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
local notation "selectedRows" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin (s + 1))))
variable (selection : Fin (s + 1) ↪ G) (stride N : Fin nX → ℕ)
variable (Pdetect : Polynomial ℕ) (u pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
local notation "pDetect" => allocatedModelTestLog u pModel
local notation "qDetect" => allocatedModelTestLog u pModel
local notation "Ctail" => (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j))
local notation "Kslice" => Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))
variable (α τ : ℝ)
variable {P : ℝ}

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "jetRows" => selectedRows
local notation "activeB" => (fun a : {a // ¬grid a} => B (Subtype.val a))
local notation "activeDegree" => (fun a : {a // ¬grid a} => degree (Subtype.val a))
local notation "L" => principalAxisLength (fun a => ¬grid a) (allocatedPrincipalSides B U basis S)
local notation "positiveLengths" => (fun j : Tuple => allocatedPrincipalSides_pos B U basis S
  (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j)))

variable (Q : Fin m → Type) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "source" => allocatedCoefficientSource B U basis hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U basis hR hσ S
local notation "reference" => allocatedLongJetReference B U basis S jetRows
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [IsProbabilityMeasure μ]
local notation "jetHaar" => Measure.pi (fun j =>
  @Measure.pi (selectedRows j) _ (fullBooleanRowSetFintype (s + 1) (Fin.val j + 1)) _
    (fun _ : selectedRows j => ν j))
local notation "density" => allocatedCoefficientDensity B U basis hb o hR hσ S

def PreparedModularGeneralCenteredDetectionFreeTrimSharedWidthInterface
    (Pchart Qstride Pmaster Plate _pGain Pphysical coarseTarget : ℝ) : Prop :=
    ∀ (_hstride : ∀ i, 0 < stride i) (_hstrideBound : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    (C : Fin m → ℝ) (_hC : ∀ j, 0 ≤ C j) (_hCbound : ∀ j, C j ≤ Real.exp Pchart)
    (_hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (Cforward : Fin m → ℝ≥0)
    (_hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) v‖ ≤ Cforward j * ‖v‖)
    (_hForward : ∀ j, (Cforward j : ℝ) ≤ Real.exp Pchart)
    (_hVtail : ∀ j, (Vtail j : ℝ) ≤ Real.exp Pchart)
    (_hVactual : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ Vtail j)
    (_hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Pchart)
    (_hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Pchart),
    ∀ (hτSpatial : 0 < τ), τ⁻¹ ≤ Real.exp Pphysical →
    τ ≤ 1 / 2 → (nX : ℝ) * τ ≤ 1 / 2 →
    let r := preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m s) (s + 1) Pmaster Plate
    let W := allocatedPhysicalRootBudget B U basis S (fun _ => 0)
    ∀ {ξn : ℝ} (hξn : 0 < ξn),
    ξn ≤ normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection
      (allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect (α / 2))
      Pphysical coarseTarget → ξn⁻¹ ≤ Real.exp Plate →
    let hW := allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0)
    ∀ (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
      (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
      (_hp : ∀ j, DegreeLE (1 : (Fin nX) → ℕ) (j.val + 1) (poly j))
      (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
      {Rrank : ℝ},
    (∀ i, Real.exp r.required ≤ (N i : ℝ)) →
    (∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
    Real.exp r.required ≤ Rrank →
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξn N
    cells.Nonempty →
    let bases := trimmedIntegerBox N (spatialTrimMargin τ N)
    let Z := selectedJointDensityMass bases stride cells V
      (allocatedJointBaseDensity B U basis hb o hR hσ S (Fin nX) poly hmem)
    ∃ (hN : ∀ i, 0 < N i) (hbases : bases.Nonempty) (hbox : (integerBox N).Nonempty)
      (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z)
      (_hnormalizer : |Z - 1| ≤ Real.exp (-r.E) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z ∧ Z⁻¹ ≤ 2)
      (_hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i),
    let Path := bases × rectangularWeightIndices 0 V 1
    ∃ hcenter : ∀ center : CoefficientTorus (K := LayerSamplerVariables G I n B) U,
      0 < selectedJointDensityMass bases stride cells V
        (allocatedCenteredJointDensity B U basis hb o hR hσ S poly hmem center),
    let centeredLaw := fun center => selectedJointFiniteLaw bases hbases stride cells V
      (narrowTrimmedSpatialWidths_pos hW hτSpatial hξn N hN) hmass
      (allocatedCenteredJointDensity B U basis hb o hR hσ S poly hmem center)
      (allocatedCenteredJointDensity_nonneg B U basis hb o hR hσ S poly hmem center) (hcenter center)
    ∃ hweight : ∀ z, Measurable (fun center => (centeredLaw center).weight z),
    let pathLaw := centeredFiniteMarginal μ centeredLaw hweight
    let sides := Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S)
    let Sites := integerBox sides
    let e : Sites → LayerSamplerVariables G I n B → ℤ := Subtype.val
    ∀ {Tests : Path → Type} [∀ z, Nonempty (Tests z)]
      {Ldetect : ∀ z, Tests z → Type} [∀ z j, LieRing (Ldetect z j)] [∀ z j, LieAlgebra ℚ (Ldetect z j)]
      {dims : ∀ z, Tests z → ℕ}
      [∀ z j, TopologicalSpace (ℝ ⊗[ℚ] Ldetect z j)]
      [∀ z j, IsTopologicalAddGroup (ℝ ⊗[ℚ] Ldetect z j)]
      [∀ z j, ContinuousSMul ℝ (ℝ ⊗[ℚ] Ldetect z j)] [∀ z j, T2Space (ℝ ⊗[ℚ] Ldetect z j)]
      (Ddetect : ∀ z j, RationalFilteredNilmanifold (Ldetect z j) s (dims z j))
      (Vdetect : ∀ z j, (Ddetect z j).Niltest (fun _ : LayerSamplerVariables G I n B => 1))
      (slices : ∀ z, Tests z → Finset Sites)
      (cdetect : ∀ z, Tests z → LayerSamplerVariables G I n B → ℤ)
      (stepdetect : ∀ z, Tests z → ℕ)
      (Hdetect : ∀ z, Tests z → LayerSamplerVariables G I n B → ℕ),
    (∀ z j, 0 < stepdetect z j) →
    (∀ z j, (slices z j).image e = commonStrideBox (cdetect z j) (stepdetect z j) (Hdetect z j)) →
    (∀ z j, IsDenseCommonStrideBox
      (Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S)) pSlice ((slices z j).image e)) →
    (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pdetect.eval₂ (Nat.castRingHom ℝ) qDetect →
    (∀ z j, (Vdetect z j).ComplexityLE (Pdetect.eval₂ (Nat.castRingHom ℝ) qDetect)) →
    (∀ z j, ((Vdetect z j).normBound : ℝ) ≤ 1) →
    let budget := r.nativeBudget
    ∀ (signal : (Fin nX → ℤ) → ℂ),
    0 < α →
    (∀ t, ‖signal t‖ ≤ 1) → (∀ t, t ∉ integerBox N → signal t = 0) →
    α ≤ sampledSliceSeminorm pathLaw
      (fun z t => jointIntegerPhysicalSite (e t) (z.1.val, z.2.val)) slices
      (fun z j t => star ((Vdetect z j).eval
        (commonStrideIndex (cdetect z j) (stepdetect z j) (e t)))) signal →
    ∃ twistData : NormalizedPolynomialTwist (Fin nX) (Σ j, J j)
      (Real.exp budget) (Real.exp budget) ⟨Real.exp budget, Real.exp_nonneg _⟩,
      ∃ Fnative : integerBox N → ℂ,
        Nonempty (NativeSampleModel (fun _ : Fin nX => 1) s budget
          (fun t : integerBox N => t.val) Fnative) ∧
        Real.exp (-budget) ≤
          ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) hbox).correlation
            (fun t => signal t.val) (fun t => star (twistData.eval N poly t.val) * Fnative t)‖

include μ hR hσ hb o in

theorem preparedModularGeneralCenteredDetectionFreeTrimSharedWidth_of_direct
    (Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget : ℝ)
    (hDirect : PreparedModularGeneralDirectDetectionFreeTrimPreparedSharedWidthInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (α := α / 2) (τ := τ) (hb := hb) (o := o)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget) :
    PreparedModularGeneralCenteredDetectionFreeTrimSharedWidthInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (α := α) (τ := τ) (hb := hb) (o := o) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget := by
  intro hstride hstrideBound C hC hCbound hchart Cforward hforward hForward
    hVtail hVactual hprofile hcutoff hτSpatial hτInv hτHalf hτDim
    r W ξn hξn hξn_le hξLate hW cells poly hp hmem Rrank hsize hrank hRank V hCells bases Z
  have hprimitive := hDirect hstride hstrideBound C hC hCbound hchart Cforward hforward
    hForward hVtail hVactual hprofile hcutoff hτSpatial hτInv hτHalf hτDim
      hξn hξn_le hξLate
  obtain ⟨hN, hbases, hbox, hmass, hnormalizer, hmargin, _⟩ :=
    hprimitive cells poly hp hmem hsize hrank hRank hCells
  refine ⟨hN, hbases, hbox, hmass, hnormalizer, hmargin, ?_⟩
  intro Path
  have hcenter (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U) :
      0 < selectedJointDensityMass bases stride cells V
        (allocatedCenteredJointDensity B U basis hb o hR hσ S poly hmem center) := by
    obtain ⟨c, hc⟩ := exists_subtractive_constant_center U center
    let pc := fun j => subtractConstant (c j).val (poly j)
    let hmc := fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hmem j)
    obtain ⟨_, _, _, _, hnormc, _, _⟩ := hprimitive cells pc
      (preparedModularGeneralCentered_degree U poly hp c) hmc hsize
      (preparedModularGeneralCentered_rank U poly (fun i => (N i : ℝ)) Rrank hrank c)
      hRank hCells
    have hdensity := allocatedJointBaseDensity_subtractConstant_centered
      B U basis hb o hR hσ S poly hmem center c hc
    have hpos := hnormc.2.2.1
    change 0 < selectedJointDensityMass bases stride cells V
      (allocatedJointBaseDensity B U basis hb o hR hσ S (Fin nX) pc hmc) at hpos
    rw [hdensity] at hpos
    exact hpos
  refine ⟨hcenter, ?_⟩
  intro centeredLaw
  have hweight (z : Path) : Measurable (fun center => (centeredLaw center).weight z) :=
    selectedJointFiniteLaw_weight_measurable bases hbases stride cells V
      (narrowTrimmedSpatialWidths_pos hW hτSpatial hξn N hN) hmass
      (allocatedCenteredJointDensity B U basis hb o hR hσ S poly hmem)
      (allocatedCenteredJointDensity_measurable_center B U basis hb o hR hσ S poly hmem)
      (allocatedCenteredJointDensity_nonneg B U basis hb o hR hσ S poly hmem) hcenter z
  refine ⟨hweight, ?_⟩
  intro pathLaw sides Sites e Tests _ Ldetect _ _ dims _ _ _ _ Ddetect Vdetect slices
    cdetect stepdetect Hdetect hstep hboxDetect hdense hdimension hcomplexity hcap budget
    signal hα hsignal hzero hlarge
  obtain ⟨center, hlargeCenter⟩ := exists_center_of_sampledSliceSeminorm μ centeredLaw hweight
    (fun z t => jointIntegerPhysicalSite (e t) (z.1.val, z.2.val)) slices
    (fun z j t => star ((Vdetect z j).eval
      (commonStrideIndex (cdetect z j) (stepdetect z j) (e t)))) signal hα hlarge
  obtain ⟨c, hc⟩ := exists_subtractive_constant_center U center
  let pc := fun j => subtractConstant (c j).val (poly j)
  let hmc := fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hmem j)
  obtain ⟨hNc, hbasesc, hboxc, hmassc, hnormc, hmargin, hdetector⟩ :=
    hprimitive cells pc (preparedModularGeneralCentered_degree U poly hp c) hmc hsize
      (preparedModularGeneralCentered_rank U poly (fun i => (N i : ℝ)) Rrank hrank c)
      hRank hCells
  have hlaw := allocatedOriginalPathLaw_subtractConstant_eq_centered
    B U basis hb o hR hσ S poly hmem N hN hW hτSpatial hξn stride cells hmass bases hbases
    center c hc hnormc.2.2.1 (hcenter center)
  change α / 2 ≤ sampledSliceSeminorm
    (selectedJointFiniteLaw bases hbases stride cells V
      (narrowTrimmedSpatialWidths_pos hW hτSpatial hξn N hN) hmass
      (allocatedCenteredJointDensity B U basis hb o hR hσ S poly hmem center)
      (allocatedCenteredJointDensity_nonneg B U basis hb o hR hσ S poly hmem center)
      (hcenter center))
    (fun z t => jointIntegerPhysicalSite (e t) (z.1.val, z.2.val)) slices
    (fun z j t => star ((Vdetect z j).eval
      (commonStrideIndex (cdetect z j) (stepdetect z j) (e t)))) signal at hlargeCenter
  rw [← hlaw] at hlargeCenter
  obtain ⟨twistData, Fnative, hNative, hcorrelation⟩ :=
    hdetector Ddetect Vdetect slices cdetect stepdetect Hdetect hstep hboxDetect hdense
      hdimension hcomplexity hcap signal hsignal hzero hlargeCenter
  refine ⟨twistData.shiftConstant (fun j => (c j).val), Fnative, hNative, ?_⟩
  have heval (t : integerBox N) :
      (twistData.shiftConstant (fun j => (c j).val)).eval N poly t.val =
        twistData.eval N pc t.val :=
    NormalizedPolynomialTwist.eval_shiftConstant twistData (fun j => (c j).val) N poly t.val
  simp_rw [heval]
  exact hcorrelation

end Consumer
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

def SharedWidthDetectedCanonicalLateToleranceFreeTrimPreparedStatement (m s : ℕ)
    (Pdetect : Polynomial ℕ) : Prop :=
    let Cdetect := sampledSupportedSlicedDetectionConstant s Pdetect
    let Aearly := Classical.choose (exists_preparedModularGeneralCanonicalEarlyParameters m s Cdetect)
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {G : Type} [Fintype G] [DecidableEq G]
      {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
      (B : LayerSamplerAxis I n → Type) [∀ b, Fintype (B b)] [∀ b, DecidableEq (B b)]
      {Bstruct pnum pSlice Qstride : ℝ} {nX : ℕ},
      0 < m → s ≤ m → 0 ≤ Bstruct → pnum ∈ Set.Icc 0 Bstruct →
      (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pnum →
      (∀ j, (Fintype.card (I j) : ℝ) ≤ pnum) → (∀ j, (n j : ℝ) ≤ pnum) →
      (∀ b : LayerSamplerAxis I n,
        (boundedBooleanJetRows (Fin (s + 1)) (b.1.val + 1)).card ≤ Fintype.card (B b)) →
      pSlice ∈ Set.Icc 0 Bstruct → Qstride ∈ Set.Icc 0 Bstruct → (nX : ℝ) ≤ Bstruct →
      (∀ j i, positiveModerateSpectrumBlockCount j.val (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
        ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩)) →
      (∀ j i, uniformSpectrumBlockCount j.val (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
        ((j.val + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩)) →
      (s + 1) * (s + 3) ≤ Fintype.card G →
      let A := Classical.choose (exists_allocatedCanonicalSlice_early_radius.{0,0,0,0} m)
      let radiusBudget := Bstruct + (2 * Bstruct + A) ^ A + 2
      let rowSets := fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)
      let T := allocatedIdealCoverSupport (G := G) B rowSets
      let siteRadius := allocatedProductIdealSiteRadius (G := G) B rowSets
      let D := allocatedComparisonDimension m pnum
      ∃ (pRadius : ℝ) (R : Fin m → ℝ),
      pRadius ∈ Set.Icc 0 radiusBudget ∧
      (∀ j, 0 < R j ∧ R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
      1 ≤ siteRadius ∧ (∀ j, 0 ≤ T j) ∧
      (∀ j, partitionedIdealRadius (Fin (s + 1)) m + 1 ≤ T j) ∧
      (∀ j, (Fintype.card (BoundedCoefficientExponent
        (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
          ((2 : ℝ) ^ Fintype.card (Fin (s + 1)) *
            ((Fintype.card (Fin (s + 1)) : ℝ) + 1) ^ (j.val + 1)) ≤ T j) ∧
      (∀ j, (rowSets j).card * T j ≤ (siteRadius : ℝ)) ∧
      (∀ j, T j ≤ Real.exp pRadius) ∧ 2 * (siteRadius : ℝ) ≤ Real.exp pRadius ∧
      (∀ Cchart : Fin m → ℝ, (∀ j, 0 ≤ Cchart j) → (∀ j, Cchart j ≤ Real.exp Bstruct) →
        (∀ j, Cchart j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4) ∧
        (∀ j, Cchart j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4) ∧
        (∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin (s + 1))) *
          (Cchart j * (((Fintype.card (I j) : ℝ) + 1) *
            (2 * (siteRadius : ℝ) * R j)))) ≤ 1 / 4)) ∧
      AllocatedComparisonDimensions (G := G) B (Fin (s + 1)) (fun j => (rowSets j : Type)) D ∧
      ∀ {u P : ℝ}, 0 ≤ u → Bstruct + u ≤ P →
      let Pearly := P + (2 * P + A) ^ A + 2
      let pModel := allocatedEarlyModelLog Pearly pSlice (Fintype.card (LayerSamplerVariables G I n B))
      let pDetect := allocatedModelTestLog u pModel
      let aDetect := 2 * u + 4 * pModel + 7
      let gainLog := slicedDetectionGainLog s Cdetect (Fintype.card (LayerSamplerVariables G I n B)) pDetect pDetect aDetect
      let Pk := scalarKernelLogarithmicBudget (Fin (s + 1)) G (gainLog + pDetect + 4)
      let Qearly := (P + Aearly) ^ Aearly
      let Pphysical := Qearly + Pk + Qstride + nX + (m + 1 : ℕ) + 8
      let Eextra := coefficientErrorSpatialLog Pphysical + 8
      let target := gainLog + 32 + Eextra
      let F := pDetect + 2
      let Tmod := ((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride
      let _δ := Real.exp (-(pDetect + 1))
      let E := target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5
      let _η := Real.exp (-E)
      let Prho := 2 * affineProfileInputEnvelope D (canonicalSublevelCutoffLip : ℝ)
        (canonicalTransitionLip : ℝ) E F + 2
      let Ptail := affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) E F
      let _K := Classical.choose (exists_allocatedAffineScaleLog_bound m)
      let budget := (P + Eextra + C) ^ C
      let master := budget + Pphysical + Pearly + gainLog + 32
      pRadius ≤ budget ∧ (∀ j, T j ≤ Real.exp budget) ∧
      2 * (siteRadius : ℝ) ≤ Real.exp budget ∧ radiusBudget ≤ Pearly ∧
      P ≤ Pearly ∧ Pearly ≤ budget ∧ pModel ∈ Set.Icc 0 budget ∧ pDetect ∈ Set.Icc 0 budget ∧
      aDetect ∈ Set.Icc 0 budget ∧ target ∈ Set.Icc 0 budget ∧ D ∈ Set.Icc 0 budget ∧ gainLog ∈ Set.Icc 0 budget ∧ Pk ∈ Set.Icc 0 budget ∧
      Prho ∈ Set.Icc 0 budget ∧ Ptail ∈ Set.Icc 0 budget ∧ Tmod ∈ Set.Icc 0 budget ∧
      ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      t⁻¹ ≤ Real.exp Ptail ∧ t⁻¹ ≤ Real.exp budget ∧
      ∀ {Qσ : ℝ}, 0 ≤ Qσ →
      let σ := min t (Real.exp (-Qσ))
      let Pscale := pRadius + Ptail + Qσ
      let lengthLog := allocatedAffineLengthLog m D Pscale Prho Pk target F Tmod
      let Pseed := allocatedScaleLog (D + Pscale + lengthLog + 1)
      0 < σ ∧ σ ≤ t ∧ σ ≤ Real.exp (-Qσ) ∧
      σ⁻¹ ≤ Real.exp Pscale ∧ Pscale ∈ Set.Icc 0 (2 * budget + Qσ) ∧
      ∀ (Lmin : ℕ) {W Qw Pmin : ℝ},
        1 ≤ W → 0 ≤ Qw → W ≤ Real.exp Qw →
        0 ≤ Pmin → (Lmin : ℝ) ≤ Real.exp Pmin →
      ∀ {J : Fin m → Type} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ),
        ∃ S : LayerSamplerScale (G := G) B U basis R (fun _ => σ),
          Pk ≤ Pscale ∧ Lmin ≤ S.value ∧
          (S.value : ℝ) ≤ Real.exp
            (allocatedWitnessScaleLog Pseed Qw + (1 + Pseed ^ 2) * Pmin) ∧
          (∀ j i, S.value ^ (j.val + 1) < basisAxisScale (basis j) i →
            8 * (probabilityProfileLipschitz : ℝ) * W ≤
              (layerSamplerGapWidth (G := G) B R ⟨j, i⟩ / 2) *
                ((basisAxisScale (basis j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) ∧
          (∀ lateTarget : ℝ, gainLog + 32 ≤ lateTarget →
            let Plate := preparedModularGeneralDetectorLateMaster master Pseed Qw Pphysical lateTarget +
              (1 + Pseed ^ 2) * Pmin + Pscale
            let resources := preparedModularGeneralDetectorResources
              (preparedModularGeneralDetectorConstants m s) (s + 1) master Plate
            resources.nativeBudget = (preparedModularGeneralDetectorResources
              (preparedModularGeneralDetectorConstants m s) (s + 1) master master).nativeBudget ∧
            (∀ (selection : Fin (s + 1) ↪ G) (hRpos : ∀ j, 0 < R j) (hσpos : ∀ _j : Fin m, 0 < σ)
              (stride N : Fin nX → ℕ)
              (Q : Fin m → Type) [∀ j, Fintype (Q j)]
              (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
              (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
              (_bW : ∀ j, Module.Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
              [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
              (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
                (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
              [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
              [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
              [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
              [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
              (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
              [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
              [CompactSpace (CoefficientTorus (K := Fin (s + 1)) U)]
              [MeasurableSpace (CoefficientTorus (K := Fin (s + 1)) U)]
              [BorelSpace (CoefficientTorus (K := Fin (s + 1)) U)]
              (μrows : Measure (CoefficientTorus (K := Fin (s + 1)) U))
              [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]
              [MeasurableSpace (SiteTorus (Finset (Fin (s + 1))) U)]
              [BorelSpace (SiteTorus (Finset (Fin (s + 1))) U)]
              (Vtail : Fin m → ℝ≥0) (α τfree : ℝ),
              Real.exp (-aDetect) ≤ α → α ≤ 1 →
              PreparedModularGeneralDirectDetectionFreeTrimPreparedSharedWidthInterface
                (B := B) (U := U) (basis := basis) (S := S) (hR := hRpos) (hσ := hσpos)
                (selection := selection) (stride := stride) (N := N)
                (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail) (α := α) (τ := τfree)
                (hb := hb) (o := o) Bstruct Qstride master Plate gainLog Pphysical lateTarget)) ∧
          ∀ α : ℝ, Real.exp (-aDetect) ≤ α →
            Real.exp (-gainLog) ≤
              (Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (s + 1)) ∧
            (scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
              (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (s + 1))) / 2) : ℝ) ≤ Real.exp Pk ∧
            scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
              (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (s + 1))) / 2) ≤ S.value

theorem exists_sharedWidth_detected_canonical_late_tolerance_free_trim_prepared (m s : ℕ)
    (Pdetect : Polynomial ℕ) :
    SharedWidthDetectedCanonicalLateToleranceFreeTrimPreparedStatement m s Pdetect := by
  unfold SharedWidthDetectedCanonicalLateToleranceFreeTrimPreparedStatement
  intro Cdetect Aearly
  obtain ⟨C, hC, hearly⟩ := exists_detected_canonical_early_radius_late_tolerance_source m s Cdetect
  refine ⟨C, hC, ?_⟩
  intro G _ _ I _ n B _ _ Bstruct pnum pSlice Qstride nX hm hs hB hnum
    hvars hI hn hblocks hpSlice hQstride hnX hBa hBi hcapacity
    A radiusBudget rowSets T siteRadius D
  obtain ⟨pRadius, R, hpRadius, hR, hrone, hT0, hTideal, hTsource,
      hTradius, hTbound, hrbound, hsmall, hdimensions, hsource⟩ :=
    hearly (G := G) B hm hs hB hnum hvars hI hn hblocks hpSlice hQstride hnX
  refine ⟨pRadius, R, hpRadius, hR, hrone, hT0, hTideal, hTsource,
    hTradius, hTbound, hrbound, hsmall, hdimensions, ?_⟩
  intro u P hu hmaster Pearly pModel pDetect aDetect gainLog Pk Qearly Pphysical Eextra target
    F Tmod δ E η Prho Ptail K budget master
  have hBP : Bstruct ≤ P := (le_add_of_nonneg_right hu).trans hmaster
  have hP : 0 ≤ P := hB.trans hBP
  have huP : u ≤ P := (le_add_of_nonneg_left hB).trans hmaster
  obtain ⟨hPQ, hEarlyQ, _, _, _, _, hGainQ, hPkQ⟩ :=
    (Classical.choose_spec (exists_preparedModularGeneralCanonicalEarlyParameters m s Cdetect)).2
      (G := G) B hm hs hP ⟨hnum.1, hnum.2.trans hBP⟩ hvars hI hn hblocks
      ⟨hpSlice.1, hpSlice.2.trans hBP⟩ ⟨hu, huP⟩
      ⟨hQstride.1, hQstride.2.trans hBP⟩ (hnX.trans hBP)
  have hQearly0 : 0 ≤ Qearly := hP.trans hPQ
  have hPhysical0 : 0 ≤ Pphysical := by
    dsimp only [Pphysical]
    linarith only [hQearly0, hPkQ.1, hQstride.1,
      Nat.cast_nonneg (α := ℝ) nX, Nat.cast_nonneg (α := ℝ) (m + 1)]
  have hExtra : 0 ≤ Eextra := by
    have herror := coefficientErrorSpatialLog_nonneg hPhysical0
    dsimp only [Eextra]
    linarith only [herror]
  obtain ⟨hpRadiusBudget, hTbudget, hrbudget, hRadiusEarly, hPEarly, hEarlyBudget,
      hModel, hDetect, hAlog, htarget, hD, hgain, hPk, hPrho, hPtail, hTmod,
      t, ht, htone, htPtail, htbudget, htolerances⟩ := hsource hu hmaster hExtra
  refine ⟨hpRadiusBudget, hTbudget, hrbudget, hRadiusEarly, hPEarly, hEarlyBudget,
    hModel, hDetect, hAlog, htarget, hD, hgain, hPk, hPrho, hPtail, hTmod,
    t, ht, htone, htPtail, htbudget, ?_⟩
  intro Qσ hQσ σ Pscale lengthLog Pseed
  obtain ⟨hσ, hσt, hσexp, hσinv, hScaleBound, hsamplers⟩ := htolerances hQσ
  refine ⟨hσ, hσt, hσexp, hσinv, hScaleBound, ?_⟩
  intro Lmin Wscale Qw Pmin hWscale hQw hWexp hPmin hLmin J _ U basis
  obtain ⟨S, hPkScale, hFloor, hSWitness, hgap, ⟨geometry⟩, hgainKernel⟩ :=
    hsamplers Lmin hWscale hQw hWexp hPmin hLmin U basis
  refine ⟨S, hPkScale, hFloor, hSWitness, hgap, ?_, hgainKernel⟩
  intro lateTarget hCoarseLower Plate resources
  refine ⟨rfl, ?_⟩
  intro selection hRpos hσpos stride N Q _ hb o bW _ ν _ _ _ _ _ μ
    _ _ _ _ _ μrows _ _ _ _ Vtail α τfree hαlower hαone
    hstride hstrideBound Cchart hCchart hCchartBound hchart Cforward hforward
    hForward hVtail hVactual hprofile hcutoff hτfree hτfreeInv hτfreeHalf hτfreeDim
  have hGeometry0 : 0 ≤ budget := hModel.1.trans hModel.2
  have hEarly0 : 0 ≤ Pearly := hP.trans hPEarly
  have hGeometryMaster : budget ≤ master := by
    dsimp only [master]
    linarith only [hPhysical0, hEarly0, hgain.1]
  have hPhysicalMaster : Pphysical ∈ Set.Icc 0 master := by
    refine ⟨hPhysical0, ?_⟩
    dsimp only [master]
    linarith only [hGeometry0, hEarly0, hgain.1]
  have hMaster : 0 ≤ master := hGeometry0.trans hGeometryMaster
  have hCoarseMaster : gainLog + 32 ≤ master := by
    dsimp only [master]
    linarith only [hGeometry0, hPhysical0, hEarly0]
  have hLateTarget0 : 0 ≤ lateTarget := by
    linarith only [hgain.1, hCoarseLower]
  have hF : 0 ≤ F := by
    change 0 ≤ pDetect + 2
    linarith only [hDetect.1]
  have hLength0 : 0 ≤ lengthLog :=
    (allocatedAffineLengthLog_bounds m hD.1 hScaleBound.1 hPrho.1 hPk.1
      htarget.1 hF hTmod.1).2.2.1
  have hSeedInput : 0 ≤ D + Pscale + lengthLog + 1 := by
    linarith only [hD.1, hScaleBound.1, hLength0]
  have hSeed0 : 0 ≤ Pseed := allocatedScaleLog_nonneg hSeedInput
  obtain ⟨hBase0, hLateBase, hWitnessBase, hCoarseBase, hXiBase⟩ :=
    preparedModularGeneralDetectorLateMaster_bounds hMaster hSeed0 hQw hPhysical0 hLateTarget0
  have hFloorCost : 0 ≤ (1 + Pseed ^ 2) * Pmin := by positivity
  have hBaseLate : preparedModularGeneralDetectorLateMaster master Pseed Qw Pphysical lateTarget ≤ Plate := by
    dsimp only [Plate]
    linarith only [hFloorCost, hScaleBound.1]
  have hLate := hLateBase.trans hBaseLate
  have hWitnessLate : allocatedWitnessScaleLog Pseed Qw + (1 + Pseed ^ 2) * Pmin ≤ Plate := by
    dsimp only [Plate]
    linarith only [hWitnessBase, hScaleBound.1]
  have hCoarseLate := hCoarseBase.trans hBaseLate
  have hXiLate := hXiBase.trans hBaseLate
  have hScaleLate : Pscale ≤ Plate := by
    dsimp only [Plate]
    linarith only [hBase0, hFloorCost]
  have liftMaster {x : ℝ} (hx : x ∈ Set.Icc 0 budget) : x ∈ Set.Icc 0 master :=
    ⟨hx.1, hx.2.trans hGeometryMaster⟩
  have hModelMaster := liftMaster hModel
  have hDetectMaster := liftMaster hDetect
  have hTargetMaster := liftMaster htarget
  have hDMaster := liftMaster hD
  have hGainMaster := liftMaster hgain
  have hPkMaster := liftMaster hPk
  have hPrhoMaster := liftMaster hPrho
  have hpRadiusMaster := hpRadiusBudget.trans hGeometryMaster
  have hSLate := hSWitness.trans (Real.exp_le_exp.mpr hWitnessLate)
  have hPMaster : P ≤ master := hPEarly.trans (hEarlyBudget.trans hGeometryMaster)
  have hBMaster := hBP.trans hPMaster
  have hExpMaster : Real.exp Bstruct ≤ Real.exp master := Real.exp_le_exp.mpr hBMaster
  obtain ⟨_, hSliceModel, _, hcountModel⟩ := detectedCanonicalEarlyRadiusModel_bounds
    (Fintype.card (LayerSamplerVariables G I n B)) hEarly0 hpSlice.1
    (hvars.trans (hnum.2.trans (hBP.trans hPEarly)))
  have hMk := (hgainKernel α hαlower).2
  have hMkPk : (allocatedDetectedKernelCutoff s G
      (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect pDetect α : ℝ) ≤ Real.exp Pk := hMk.1
  have hMkP := hMkPk.trans (Real.exp_le_exp.mpr hPkScale)
  have hKMaster : (Real.toNNReal (Real.exp pRadius) : ℝ) ≤ Real.exp master := by
    rw [Real.coe_toNNReal (Real.exp pRadius) (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr hpRadiusMaster
  have hQPhysical : Qearly ≤ Pphysical := by
    dsimp only [Pphysical]
    linarith only [hPk.1, hQstride.1, Nat.cast_nonneg (α := ℝ) nX,
      Nat.cast_nonneg (α := ℝ) (m + 1)]
  have hmPhysical : ((m + 1 : ℕ) : ℝ) ≤ Pphysical := by
    dsimp only [Pphysical]
    linarith only [hQearly0, hPk.1, hQstride.1, Nat.cast_nonneg (α := ℝ) nX]
  have hDimPhysical : ((s + 2 : ℕ) : ℝ) ≤ Pphysical := by
    have hsm : (s : ℝ) ≤ m := Nat.cast_le.mpr hs
    dsimp only [Pphysical]
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    linarith only [hQearly0, hPk.1, hQstride.1, Nat.cast_nonneg (α := ℝ) nX, hsm]
  have hXPhysical : (nX : ℝ) ≤ Pphysical := by
    dsimp only [Pphysical]
    linarith only [hQearly0, hPk.1, hQstride.1, Nat.cast_nonneg (α := ℝ) (m + 1)]
  have hPkPhysical : Pk ≤ Pphysical := by
    dsimp only [Pphysical]
    linarith only [hQearly0, hQstride.1, Nat.cast_nonneg (α := ℝ) nX,
      Nat.cast_nonneg (α := ℝ) (m + 1)]
  have hQstridePhysical : Qstride ≤ Pphysical := by
    dsimp only [Pphysical]
    linarith only [hQearly0, hPk.1, Nat.cast_nonneg (α := ℝ) nX,
      Nat.cast_nonneg (α := ℝ) (m + 1)]
  have hvarsPhysical : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pphysical :=
    hvars.trans (hnum.2.trans (hBP.trans (hPQ.trans hQPhysical)))
  have hprecision : gainLog + 32 + coefficientErrorSpatialLog Pphysical + 8 ≤ target := by
    dsimp only [target, Eextra]
    linarith only
  intro r W ξn hξn hξle hξInvLate hW cells poly hp hmem Rrank hNlarge hrank hRankLarge V
    hcells bases Z
  have hτInvMaster : τfree⁻¹ ≤ Real.exp master :=
    hτfreeInv.trans (Real.exp_le_exp.mpr hPhysicalMaster.2)
  have hξone : ξn ≤ 1 := hξle.trans (min_le_left _ _)
  obtain ⟨hNpos, hbases, hbox, hmass, hnormalizer, hmargin⟩ :=
    preparedModularGeneralDetector_late_positive_bounds B U basis S hb o μ ν hRpos hσpos
      (fun _ => hσt.trans htone) Cforward Vtail hforward hVactual Cchart hCchart hchart
      (geometry.hbudgets Cchart hCchart hCchartBound).1 hMaster hLate geometry.hdimensions
      hDMaster.2 (hnX.trans hBMaster)
      (fun j => (hR j).2.2.trans (Real.exp_le_exp.mpr hpRadiusMaster))
      (fun j => (geometry.hσi j).trans (Real.exp_le_exp.mpr hScaleLate)) hSLate
      (fun j => (hForward j).trans hExpMaster) (fun j => (hVtail j).trans hExpMaster)
      poly hp hmem stride hstride
      (fun i => (hstrideBound i).trans (Real.exp_le_exp.mpr (hQstride.2.trans hBMaster)))
      hτfree hτInvMaster hτfreeHalf hτfreeDim hξn hξone hξInvLate
      N hrank cells hcells hNlarge hRankLarge
  let : ∀ i, NeZero (N i) := fun i => ⟨(hNpos i).ne'⟩
  have consumer := preparedModularGeneralDirectDetectionFreeTrimSharedWidthInterface_of_geometry
    (B := B) (U := U) (basis := basis) (hR := hRpos) (hσ := hσpos) (S := S) (P := Pscale)
    (selection := selection) (stride := stride) (N := N)
    (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail) (α := α) (τ := τfree)
    (Q := Q) (hb := hb) (o := o) (bW := bW) (μ := μ) (ν := ν) (μrows := μrows)
    hs Bstruct D target Pk Prho Qstride master Plate gainLog Pphysical lateTarget
    (Real.toNNReal (Real.exp pRadius)) geometry
  have completed := consumer hLate hMaster hDMaster.2 hPkMaster
    ⟨hQstride.1, hQstride.2.trans hBMaster⟩ hDetectMaster (hnX.trans hBMaster)
    (fun j => (hR j).2.1)
    (fun j => (hR j).2.2.trans (Real.exp_le_exp.mpr hpRadiusMaster))
    (fun j => (geometry.hσi j).trans (Real.exp_le_exp.mpr hScaleLate))
    hSLate hKMaster (hcutoff.trans hExpMaster) hMkP hMkPk hstride hstrideBound
    Cchart hCchart hCchartBound hchart Cforward hforward
    (fun j => (hForward j).trans hExpMaster) (fun j => (hVtail j).trans hExpMaster) hVactual hBa hBi
    ⟨hu, huP.trans hPMaster⟩ hModelMaster hSliceModel hcountModel hαlower hαone
    hPrhoMaster hTargetMaster hGainMaster hCoarseMaster hCoarseLower hCoarseLate hPhysicalMaster
    hmPhysical hDimPhysical hvarsPhysical hXPhysical hPkPhysical hQstridePhysical
    (le_refl _) hprecision hXiLate hτfree hτfreeInv hξn hξle hξInvLate
  refine ⟨hNpos, hbases, hbox, hmass, hnormalizer, hmargin, ?_⟩
  intro Path pathLaw sides Sites e Tests _ Ldetect _ _ dims _ _ _ _
    Ddetect Vdetect slices cdetect stepdetect Hdetect hstep hboxDetect hdense hcount hcomplexity hnorm budget'
  exact completed cells poly hp hmem hNlarge hrank hRankLarge hcells hbases hmass
    hnormalizer.2.2.1 Ddetect Vdetect slices cdetect stepdetect Hdetect hstep hboxDetect hdense hcount
    hcomplexity hnorm hcapacity hMk.2

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

def SharedWidthPreparedLateToleranceFreeTrimSourceStatement (m : ℕ) (Pdetect : Polynomial ℕ) : Prop :=
    let Cdetect := sampledSupportedSlicedDetectionConstant 0 Pdetect
    let Aearly := Classical.choose (exists_preparedModularGeneralCanonicalEarlyParameters m 0 Cdetect)
    let Aalloc := Classical.choose (exists_preparedModularCanonicalDetectorAllocationBudget m)
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {X J₀ : Type} (L : RankPreparationFamily X J₀ m) {M nX : ℕ},
      (∀ j, Fintype.card (L j).Coord ≤ M) →
      ∀ {Pstruct pSlice Qstride : ℝ},
      0 < m → 0 ≤ Pstruct → (M : ℝ) ≤ Pstruct →
      pSlice ∈ Set.Icc 0 Pstruct → Qstride ∈ Set.Icc 0 Pstruct → (nX : ℝ) ≤ Pstruct →
      let Jalloc := modularInitialBlockCount m (nX + m * M)
      let pnum : ℝ := enlargedPreparedCommonSamplerDimension m M Jalloc
      let Bstruct := (Pstruct + Aalloc) ^ Aalloc
      let G := EnlargedPreparedCommonKernel m Jalloc
      let I := PreparedSamplerContinuous L
      let n := preparedSamplerTransverse L
      let B := EnlargedPreparedCommonSamplerBlock L Jalloc
      let selection := enlargedPreparedCommonCanonicalSelection m Jalloc 0 (Nat.zero_le m)
    let A := Classical.choose (exists_allocatedCanonicalSlice_early_radius.{0,0,0,0} m)
      let radiusBudget := Bstruct + (2 * Bstruct + A) ^ A + 2
      let rowSets := fun j : Fin m => boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1)
      let T := allocatedIdealCoverSupport (G := G) B rowSets
      let siteRadius := allocatedProductIdealSiteRadius (G := G) B rowSets
      let D := allocatedComparisonDimension m pnum
      ∃ (pRadius : ℝ) (R : Fin m → ℝ),
      pRadius ∈ Set.Icc 0 radiusBudget ∧
      (∀ j, 0 < R j ∧ R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
      1 ≤ siteRadius ∧ (∀ j, 0 ≤ T j) ∧
      (∀ j, partitionedIdealRadius (Fin (0 + 1)) m + 1 ≤ T j) ∧
      (∀ j, (Fintype.card (BoundedCoefficientExponent
        (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
          ((2 : ℝ) ^ Fintype.card (Fin (0 + 1)) *
            ((Fintype.card (Fin (0 + 1)) : ℝ) + 1) ^ (j.val + 1)) ≤ T j) ∧
      (∀ j, (rowSets j).card * T j ≤ (siteRadius : ℝ)) ∧
      (∀ j, T j ≤ Real.exp pRadius) ∧ 2 * (siteRadius : ℝ) ≤ Real.exp pRadius ∧
      (∀ Cchart : Fin m → ℝ, (∀ j, 0 ≤ Cchart j) → (∀ j, Cchart j ≤ Real.exp Bstruct) →
        (∀ j, Cchart j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4) ∧
        (∀ j, Cchart j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4) ∧
        (∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin (0 + 1))) *
          (Cchart j * (((Fintype.card (I j) : ℝ) + 1) *
            (2 * (siteRadius : ℝ) * R j)))) ≤ 1 / 4)) ∧
      AllocatedComparisonDimensions (G := G) B (Fin (0 + 1)) (fun j => (rowSets j : Type)) D ∧
      ∀ {u P : ℝ}, 0 ≤ u → Bstruct + u ≤ P →
      let Pearly := P + (2 * P + A) ^ A + 2
      let pModel := allocatedEarlyModelLog Pearly pSlice (Fintype.card (LayerSamplerVariables G I n B))
      let pDetect := allocatedModelTestLog u pModel
      let aDetect := 2 * u + 4 * pModel + 7
      let gainLog := slicedDetectionGainLog 0 Cdetect (Fintype.card (LayerSamplerVariables G I n B)) pDetect pDetect aDetect
      let Pk := scalarKernelLogarithmicBudget (Fin (0 + 1)) G (gainLog + pDetect + 4)
      let Qearly := (P + Aearly) ^ Aearly
      let Pphysical := Qearly + Pk + Qstride + nX + (m + 1 : ℕ) + 8
      let Eextra := coefficientErrorSpatialLog Pphysical + 8
      let target := gainLog + 32 + Eextra
      let F := pDetect + 2
      let Tmod := ((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride
      let _δ := Real.exp (-(pDetect + 1))
      let E := target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5
      let _η := Real.exp (-E)
      let Prho := 2 * affineProfileInputEnvelope D (canonicalSublevelCutoffLip : ℝ)
        (canonicalTransitionLip : ℝ) E F + 2
      let Ptail := affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) E F
      let _K := Classical.choose (exists_allocatedAffineScaleLog_bound m)
      let budget := (P + Eextra + C) ^ C
      let master := budget + Pphysical + Pearly + gainLog + 32
      pRadius ≤ budget ∧ (∀ j, T j ≤ Real.exp budget) ∧
      2 * (siteRadius : ℝ) ≤ Real.exp budget ∧ radiusBudget ≤ Pearly ∧
      P ≤ Pearly ∧ Pearly ≤ budget ∧ pModel ∈ Set.Icc 0 budget ∧ pDetect ∈ Set.Icc 0 budget ∧
      aDetect ∈ Set.Icc 0 budget ∧ target ∈ Set.Icc 0 budget ∧ D ∈ Set.Icc 0 budget ∧ gainLog ∈ Set.Icc 0 budget ∧ Pk ∈ Set.Icc 0 budget ∧
      Prho ∈ Set.Icc 0 budget ∧ Ptail ∈ Set.Icc 0 budget ∧ Tmod ∈ Set.Icc 0 budget ∧
      ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      t⁻¹ ≤ Real.exp Ptail ∧ t⁻¹ ≤ Real.exp budget ∧
      ∀ {Qσ : ℝ}, 0 ≤ Qσ →
      let σ := min t (Real.exp (-Qσ))
      let Pscale := pRadius + Ptail + Qσ
      let lengthLog := allocatedAffineLengthLog m D Pscale Prho Pk target F Tmod
      let Pseed := allocatedScaleLog (D + Pscale + lengthLog + 1)
      0 < σ ∧ σ ≤ t ∧ σ ≤ Real.exp (-Qσ) ∧
      σ⁻¹ ≤ Real.exp Pscale ∧ Pscale ∈ Set.Icc 0 (2 * budget + Qσ) ∧
      ∀ (Lmin : ℕ) {W Qw Pmin : ℝ},
        1 ≤ W → 0 ≤ Qw → W ≤ Real.exp Qw →
        0 ≤ Pmin → (Lmin : ℝ) ≤ Real.exp Pmin →
      ∀ {J : Fin m → Type} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ),
        ∃ S : LayerSamplerScale (G := G) B U basis R (fun _ => σ),
          Pk ≤ Pscale ∧ Lmin ≤ S.value ∧
          (S.value : ℝ) ≤ Real.exp
            (allocatedWitnessScaleLog Pseed Qw + (1 + Pseed ^ 2) * Pmin) ∧
          (∀ j i, S.value ^ (j.val + 1) < basisAxisScale (basis j) i →
            8 * (probabilityProfileLipschitz : ℝ) * W ≤
              (layerSamplerGapWidth (G := G) B R ⟨j, i⟩ / 2) *
                ((basisAxisScale (basis j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) ∧
          (∀ lateTarget : ℝ, gainLog + 32 ≤ lateTarget →
            let Plate := preparedModularGeneralDetectorLateMaster master Pseed Qw Pphysical lateTarget +
              (1 + Pseed ^ 2) * Pmin + Pscale
            let resources := preparedModularGeneralDetectorResources
              (preparedModularGeneralDetectorConstants m 0) (0 + 1) master Plate
            resources.nativeBudget = (preparedModularGeneralDetectorResources
              (preparedModularGeneralDetectorConstants m 0) (0 + 1) master master).nativeBudget ∧
            (∀ (hRpos : ∀ j, 0 < R j) (hσpos : ∀ _j : Fin m, 0 < σ)
              (stride N : Fin nX → ℕ)
              (Q : Fin m → Type) [∀ j, Fintype (Q j)]
              (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
              (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
              (_bW : ∀ j, Module.Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
              [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
              (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
                (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
              [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
              [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
              [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
              [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
              (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
              [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
              [CompactSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
              [MeasurableSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
              [BorelSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
              (μrows : Measure (CoefficientTorus (K := Fin (0 + 1)) U))
              [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]
              [MeasurableSpace (SiteTorus (Finset (Fin (0 + 1))) U)]
              [BorelSpace (SiteTorus (Finset (Fin (0 + 1))) U)]
              (Vtail : Fin m → ℝ≥0) (α τfree : ℝ),
              Real.exp (-aDetect) ≤ α → α ≤ 1 →
              PreparedModularGeneralDirectDetectionFreeTrimPreparedSharedWidthInterface
                (B := B) (U := U) (basis := basis) (S := S) (hR := hRpos) (hσ := hσpos)
                (selection := selection) (stride := stride) (N := N)
                (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail) (α := α) (τ := τfree)
                (hb := hb) (o := o) Bstruct Qstride master Plate gainLog Pphysical lateTarget)) ∧
          ∀ α : ℝ, Real.exp (-aDetect) ≤ α →
            Real.exp (-gainLog) ≤
              (Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (0 + 1)) ∧
            (scalarKernelCutoff (Fin (0 + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
              (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (0 + 1))) / 2) : ℝ) ≤ Real.exp Pk ∧
            scalarKernelCutoff (Fin (0 + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
              (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (0 + 1))) / 2) ≤ S.value

theorem exists_sharedWidth_prepared_late_tolerance_free_trim_source (m : ℕ) (Pdetect : Polynomial ℕ) :
    SharedWidthPreparedLateToleranceFreeTrimSourceStatement m Pdetect := by
  unfold SharedWidthPreparedLateToleranceFreeTrimSourceStatement
  intro Cdetect Aearly Aalloc
  have hactual := exists_sharedWidth_detected_canonical_late_tolerance_free_trim_prepared m 0 Pdetect
  unfold SharedWidthDetectedCanonicalLateToleranceFreeTrimPreparedStatement at hactual
  obtain ⟨C, hC, hsource⟩ := hactual
  refine ⟨C, hC, ?_⟩
  intro X J₀ L M nX hCoord Pstruct pSlice Qstride hm hPstruct hM hpSlice hQstride hnX
    Jalloc pnum Bstruct G I n B selection A radiusBudget rowSets T siteRadius D
  obtain ⟨hStruct, _, hnum, _⟩ :=
    (Classical.choose_spec (exists_preparedModularCanonicalDetectorAllocationBudget m)).2
      hPstruct hM hnX
  obtain ⟨hvars, hI, hn⟩ := enlargedPreparedCommonSampler_dimensions L Jalloc hCoord
  have hblocks (a : LayerSamplerAxis I n) :
      (boundedBooleanJetRows (Fin (0 + 1)) (a.1.val + 1)).card ≤ Fintype.card (B a) := by
    calc
      _ = Fintype.card (BoundedBooleanJet (Fin (0 + 1)) (a.1.val + 1)) :=
        (Fintype.card_coe _).symm.trans (Fintype.card_congr (boundedBooleanJetRowsEquiv _ _))
      _ ≤ _ := enlargedPreparedCommonSamplerBlock_jets L Jalloc 0 (Nat.zero_le m) a
  obtain ⟨pRadius, R, hpRadius, hR, hrone, hT0, hTideal, hTsource,
      hTradius, hTbound, hrbound, hsmall, hdimensions, hlate⟩ :=
    hsource (G := G) B hm (Nat.zero_le m) (hPstruct.trans hStruct) hnum
      (Nat.cast_le.mpr hvars) (fun j => Nat.cast_le.mpr (hI j))
      (fun j => Nat.cast_le.mpr (hn j)) hblocks
      ⟨hpSlice.1, hpSlice.2.trans hStruct⟩ ⟨hQstride.1, hQstride.2.trans hStruct⟩
      (hnX.trans hStruct)
      (fun j i => enlargedPreparedCommonSamplerBlock_positiveModerate L Jalloc 0 (Nat.zero_le m) ⟨j, Sum.inr i⟩)
      (fun j i => enlargedPreparedCommonSamplerBlock_uniform L Jalloc 0 (Nat.zero_le m) ⟨j, Sum.inr i⟩)
      (enlargedPreparedCommonKernel_analytic_capacity m Jalloc 0 (Nat.zero_le m))
  refine ⟨pRadius, R, hpRadius, hR, hrone, hT0, hTideal, hTsource,
    hTradius, hTbound, hrbound, hsmall, hdimensions, ?_⟩
  intro u P hu hmaster Pearly pModel pDetect aDetect gainLog Pk Qearly Pphysical Eextra target
    F Tmod δ E η Prho Ptail K budget master
  obtain ⟨hpRadiusBudget, hTbudget, hrbudget, hRadiusEarly, hPEarly, hEarlyBudget,
      hModel, hDetect, hAlog, htarget, hD, hgain, hPk, hPrho, hPtail, hTmod,
      t, ht, htone, htPtail, htbudget, htolerances⟩ := hlate hu hmaster
  refine ⟨hpRadiusBudget, hTbudget, hrbudget, hRadiusEarly, hPEarly, hEarlyBudget,
    hModel, hDetect, hAlog, htarget, hD, hgain, hPk, hPrho, hPtail, hTmod,
    t, ht, htone, htPtail, htbudget, ?_⟩
  intro Qσ hQσ σ Pscale lengthLog Pseed
  obtain ⟨hσ, hσt, hσexp, hσinv, hScaleBound, hsamplers⟩ := htolerances hQσ
  refine ⟨hσ, hσt, hσexp, hσinv, hScaleBound, ?_⟩
  intro Lmin Wscale Qw Pmin hWscale hQw hWexp hPmin hLmin J _ U basis
  obtain ⟨S, hPkScale, hFloor, hSWitness, hgap, hdetector, hgainKernel⟩ :=
    hsamplers Lmin hWscale hQw hWexp hPmin hLmin U basis
  refine ⟨S, hPkScale, hFloor, hSWitness, hgap, ?_, hgainKernel⟩
  intro lateTarget hCoarseLower Plate resources
  obtain ⟨hnative, hprepared⟩ := hdetector lateTarget hCoarseLower
  exact ⟨hnative, hprepared selection⟩

end Erdos3.VectorPolynomial

end

end OAI
