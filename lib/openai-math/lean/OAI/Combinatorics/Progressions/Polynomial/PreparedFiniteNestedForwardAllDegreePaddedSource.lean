import OAI.Combinatorics.Progressions.Estimates.PreparedFiniteForwardSeededIndexedProductiveSource

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

abbrev PreparedFiniteNestedForwardAllDegreeSlot (outerDepth innerDepth cutoff : ℕ) :=
  Fin (outerDepth + 1) × Fin (innerDepth + 1) × Fin (cutoff + 1) × Bool

def preparedFiniteNestedForwardAllDegreeOuter {outerDepth innerDepth cutoff : ℕ}
    (k : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff) :
    Fin (outerDepth + 1) := k.1

def preparedFiniteNestedForwardAllDegreeStage {outerDepth innerDepth cutoff : ℕ}
    (k : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff) :
    Fin (innerDepth + 1) := k.2.1

def preparedFiniteNestedForwardAllDegreeIsDirect {outerDepth innerDepth cutoff : ℕ}
    (k : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff) : Bool :=
  k.2.2.2

def preparedFiniteNestedForwardAllDegreeDegree {outerDepth innerDepth cutoff : ℕ}
    (k : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff) : ℕ :=
  k.2.2.1.val

noncomputable def preparedFiniteNestedForwardAllDegreeSeed
    {outerDepth innerDepth cutoff : ℕ} (A : ℕ) (constants : ℕ → ℕ) (x : ℝ)
    (k : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff) : ℝ :=
  candidateNestedForwardSeed A constants innerDepth k.1.val x

def preparedFiniteNestedForwardAllDegreeAnchor (outerDepth innerDepth cutoff : ℕ) :
    PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff :=
  (⟨outerDepth, Nat.lt_succ_self outerDepth⟩,
    ⟨innerDepth, Nat.lt_succ_self innerDepth⟩, 0, false)

@[simp] theorem preparedFiniteNestedForwardAllDegreeOuter_slot {outerDepth innerDepth cutoff : ℕ}
    (outer : Fin (outerDepth + 1)) (inner : Fin (innerDepth + 1))
    (degree : Fin (cutoff + 1)) (direct : Bool) :
    preparedFiniteNestedForwardAllDegreeOuter (outer, inner, degree, direct) = outer := rfl

@[simp] theorem preparedFiniteNestedForwardAllDegreeStage_slot {outerDepth innerDepth cutoff : ℕ}
    (outer : Fin (outerDepth + 1)) (inner : Fin (innerDepth + 1))
    (degree : Fin (cutoff + 1)) (direct : Bool) :
    preparedFiniteNestedForwardAllDegreeStage (outer, inner, degree, direct) = inner := rfl

@[simp] theorem preparedFiniteNestedForwardAllDegreeIsDirect_slot {outerDepth innerDepth cutoff : ℕ}
    (outer : Fin (outerDepth + 1)) (inner : Fin (innerDepth + 1))
    (degree : Fin (cutoff + 1)) (direct : Bool) :
    preparedFiniteNestedForwardAllDegreeIsDirect (outer, inner, degree, direct) = direct := rfl

@[simp] theorem preparedFiniteNestedForwardAllDegreeDegree_slot {outerDepth innerDepth cutoff : ℕ}
    (outer : Fin (outerDepth + 1)) (inner : Fin (innerDepth + 1))
    (degree : Fin (cutoff + 1)) (direct : Bool) :
    preparedFiniteNestedForwardAllDegreeDegree (outer, inner, degree, direct) = degree.val := rfl

@[simp] theorem preparedFiniteNestedForwardAllDegreeSeed_slot {outerDepth innerDepth cutoff : ℕ}
    (A : ℕ) (constants : ℕ → ℕ) (x : ℝ)
    (outer : Fin (outerDepth + 1)) (inner : Fin (innerDepth + 1))
    (degree : Fin (cutoff + 1)) (direct : Bool) :
    preparedFiniteNestedForwardAllDegreeSeed A constants x (outer, inner, degree, direct) =
      candidateNestedForwardSeed A constants innerDepth outer.val x := rfl

theorem preparedFiniteNestedForwardAllDegreeDegree_le {outerDepth innerDepth cutoff m : ℕ}
    (hcutoff : cutoff ≤ m)
    (k : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff) :
    preparedFiniteNestedForwardAllDegreeDegree k ≤ m :=
  (Nat.le_of_lt_succ k.2.2.1.isLt).trans hcutoff

theorem le_preparedFiniteNestedForwardAllDegreeSeed {outerDepth innerDepth cutoff : ℕ}
    (A : ℕ) (constants : ℕ → ℕ) {x : ℝ} (hA : 2 ≤ A) (hx : 0 ≤ x)
    (k : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff) :
    x ≤ preparedFiniteNestedForwardAllDegreeSeed A constants x k :=
  le_candidateNestedForwardSeed A constants innerDepth k.1.val hA hx

@[simp] theorem preparedFiniteNestedForwardAllDegreeAnchor_outer
    (outerDepth innerDepth cutoff : ℕ) :
    preparedFiniteNestedForwardAllDegreeOuter
      (preparedFiniteNestedForwardAllDegreeAnchor outerDepth innerDepth cutoff) =
      ⟨outerDepth, Nat.lt_succ_self outerDepth⟩ := rfl

@[simp] theorem preparedFiniteNestedForwardAllDegreeAnchor_stage
    (outerDepth innerDepth cutoff : ℕ) :
    preparedFiniteNestedForwardAllDegreeStage
      (preparedFiniteNestedForwardAllDegreeAnchor outerDepth innerDepth cutoff) =
      ⟨innerDepth, Nat.lt_succ_self innerDepth⟩ := rfl

@[simp] theorem preparedFiniteNestedForwardAllDegreeAnchor_model
    (outerDepth innerDepth cutoff : ℕ) :
    preparedFiniteNestedForwardAllDegreeIsDirect
      (preparedFiniteNestedForwardAllDegreeAnchor outerDepth innerDepth cutoff) = false := rfl

@[simp] theorem preparedFiniteNestedForwardAllDegreeAnchor_degree
    (outerDepth innerDepth cutoff : ℕ) :
    preparedFiniteNestedForwardAllDegreeDegree
      (preparedFiniteNestedForwardAllDegreeAnchor outerDepth innerDepth cutoff) = 0 := rfl

@[simp] theorem preparedFiniteNestedForwardAllDegreeAnchor_seed
    (outerDepth innerDepth cutoff A : ℕ) (constants : ℕ → ℕ) (x : ℝ) :
    preparedFiniteNestedForwardAllDegreeSeed A constants x
      (preparedFiniteNestedForwardAllDegreeAnchor outerDepth innerDepth cutoff) =
      candidateNestedForwardSeed A constants innerDepth outerDepth x := rfl

theorem exists_preparedFiniteNestedForwardAllDegreePaddedProductiveSource
    {m nX M : ℕ} {X₀ J₀ : Type} (prep : RankPreparationFamily X₀ J₀ m) (outerDepth innerDepth cutoff : ℕ)
    [∀ j : Fin (max m cutoff), DecidableEq (RankPreparationLayer.Coord ((prep.pad (max m cutoff)) j))]
    (U : ∀ j, Submodule ℝ ((fun j : Fin (max m cutoff) => RankPreparationLayer.Coord ((prep.pad (max m cutoff)) j)) j → ℝ))
    (b : ∀ j, Basis (Fin ((preparedSamplerTransverse (prep.pad (max m cutoff))) j)) ℝ (euclideanSubspace (U j))ᗮ)
    (stride N : Fin nX → ℕ) (Pdetect : Polynomial ℕ)
    (Vtail : Fin (max m cutoff) → ℝ≥0)

    (Q : Fin (max m cutoff) → Type) [∀ j, Fintype (Q j)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis ((PreparedSamplerContinuous (prep.pad (max m cutoff))) j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin (max m cutoff) => RankPreparationLayer.Coord ((prep.pad (max m cutoff)) j)) j)) (euclideanSubspace (U j))))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice ((fun j : Fin (max m cutoff) => RankPreparationLayer.Coord ((prep.pad (max m cutoff)) j)) j)) (euclideanSubspace (U j)))]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice ((fun j : Fin (max m cutoff) => RankPreparationLayer.Coord ((prep.pad (max m cutoff)) j)) j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    [CompactSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
    [BorelSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
    (μrows : Measure (CoefficientTorus (K := Fin (0 + 1)) U))
    [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]
    [MeasurableSpace (SiteTorus (Finset (Fin (0 + 1))) U)]
    [BorelSpace (SiteTorus (Finset (Fin (0 + 1))) U)]

    (A Cslice Cdirect : ℕ) (stageCountConstant : ℕ → ℕ)
    (hA : 2 ≤ A) (hSliceExponent : Cslice + 1 ≤ A)
    (Bstruct Qstride forecastCap stageLog : ℝ)
    (Qσ Qw Pmin requestedCoarse gainLog gain Vlog : ℝ)
    (Lmin Qgood : ℕ)
    (hm : 0 < max m cutoff) (hnX : 0 < nX)
    (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hB : 0 ≤ Bstruct) (hstage : stageLog ∈ Set.Icc 0 Bstruct)
    (hQstride : 0 ≤ Qstride)
    (hQσ : 0 ≤ Qσ) (hQw : 0 ≤ Qw) (hPmin : 0 ≤ Pmin)
    (hLmin : (Lmin : ℝ) ≤ Real.exp Pmin)
    (hg : 0 ≤ gainLog) (hVlog : 0 ≤ Vlog)
    (hQgood : 1 ≤ Qgood) (hQexp : (Qgood : ℝ) ≤ Real.exp Vlog)
    (hgain : Real.exp (-gainLog) ≤ gain)
    (hnChart : (nX : ℝ) ≤ Bstruct) (hgChart : gainLog ≤ Bstruct) :
    let K := PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff
    let degree : K → ℕ := preparedFiniteNestedForwardAllDegreeDegree
    let Cdetect := fun k : K => sampledSupportedSlicedDetectionConstant (degree k) Pdetect
    let kModel : K := preparedFiniteNestedForwardAllDegreeAnchor outerDepth innerDepth cutoff
    let sourceU := fun k : K =>
      preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant
        (preparedFiniteNestedForwardAllDegreeStage k).val (preparedFiniteNestedForwardAllDegreeIsDirect k)
        (preparedFiniteNestedForwardAllDegreeSeed A stageCountConstant Bstruct k) gainLog stageLog
    let modelLog := fun k : K => preparedFiniteForwardWork A stageCountConstant
      (preparedFiniteNestedForwardAllDegreeStage k).val
      (preparedFiniteNestedForwardAllDegreeSeed A stageCountConstant Bstruct k)
    let sliceLog := fun k : K =>
      (preparedFiniteForwardParameter A stageCountConstant (preparedFiniteNestedForwardAllDegreeStage k).val
        (preparedFiniteNestedForwardAllDegreeSeed A stageCountConstant Bstruct k) + Cslice) ^ Cslice
    let u := preparedFiniteForwardModelPrecision A stageCountConstant innerDepth
      (candidateNestedForwardSeed A stageCountConstant innerDepth outerDepth Bstruct) gainLog stageLog
    let p := preparedFiniteForwardWork A stageCountConstant innerDepth
      (candidateNestedForwardSeed A stageCountConstant innerDepth outerDepth Bstruct)
    let pnum : ℝ := enlargedPreparedCommonSamplerDimension (max m cutoff) M (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))
    let R : Fin (max m cutoff) → ℝ := fun _ => allocatedCommonProductRadius (max m cutoff) Bstruct Bstruct
    let pRadius := allocatedCommonProductRadiusLog (max m cutoff) Bstruct Bstruct
    let D := allocatedComparisonDimension (max m cutoff) pnum
    let pDetect := fun k => allocatedModelTestLog (sourceU k) (modelLog k)
    let aDetect := fun k => 2 * sourceU k + 4 * modelLog k + 7
    let detectionGain := fun s : K => slicedDetectionGainLog (degree s) (Cdetect s)
      (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))))) (pDetect s) (pDetect s) (aDetect s)
    let Pk := fun s : K => scalarKernelLogarithmicBudget (Fin ((degree s) + 1)) (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))
      (detectionGain s + pDetect s + 4)
    let Pphysical := fun k : K => preparedFiniteScheduleLocalPhysical (max m cutoff) nX
      (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))))) Qstride (Pk k)
    let target := fun k => detectionGain k + 40 + coefficientErrorSpatialLog (Pphysical k)
    let E := fun s : K => target s + D * (((max m cutoff) * 2 ^ ((max m cutoff) + 1) : ℕ) * Pk s) + 5
    let Prho := fun s : K => 2 * affineProfileInputEnvelope D
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2) + 2
    let Ptail := fun s : K => affineProfileToleranceEnvelope (max m cutoff) D (D * (D + 1) + D * D + D + 1)
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2)
    let Pscale := preparedUniformDegreeScaleLog (D + pRadius) Ptail Qσ
    let Tmod := fun s : K => (((max m cutoff) + 1 : ℕ) : ℝ) * Pk s + nX * Qstride
    let lengthLogs := fun s : K => allocatedAffineLengthLog (max m cutoff) D Pscale (Prho s) (Pk s)
      (target s) (pDetect s + 2) (Tmod s)
    let Pseed := allocatedScaleLog (Pscale + ∑ s, lengthLogs s + Pmin + 1)
    let W := physicalBadProductGap ((modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)) * (nX + (max m cutoff) * M)) (gainLog + 8) Vlog Qgood
    let Pmaster := fun k : K => preparedFiniteScheduleLocalMaster Bstruct D pRadius Qstride
      (Pphysical k) (sourceU k) (modelLog k) (Prho k) (target k) (detectionGain k)
    let coarseTarget := preparedFiniteScheduleDirectCoarse detectionGain requestedCoarse
    let Plate := ∑ k : K, preparedUniformDegreeDirectLate (Pmaster k) Pscale
      (Pphysical k) coarseTarget (allocatedWitnessScaleLog Pseed Qw)
    let τ := Real.exp (-(gainLog + (nX : ℝ) + 8))
    pnum ≤ Bstruct →
    W ≤ Real.exp Qw →
    (4 * ∏ j, earlyConstantDensityCap (Fintype.card ((PreparedSamplerContinuous (prep.pad (max m cutoff))) j)) ((preparedSamplerTransverse (prep.pad (max m cutoff))) j) (R j) (Vtail j)) ≤ Real.exp p →
    0 ≤ forecastCap → forecastCap ≤ Real.exp p →
    ∃ (hR : ∀ j, 0 < R j) (σ : ℝ) (hσ : 0 < σ)
      (S : LayerSamplerScale («G» := (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) («I» := (PreparedSamplerContinuous (prep.pad (max m cutoff)))) («n» := (preparedSamplerTransverse (prep.pad (max m cutoff)))) («J» := (fun j : Fin (max m cutoff) => RankPreparationLayer.Coord ((prep.pad (max m cutoff)) j))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) U b R (fun _ => σ)),
      0 ≤ pRadius ∧ (∀ j, R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
      σ ≤ 1 ∧ σ ≤ Real.exp (-Qσ) ∧ σ⁻¹ ≤ Real.exp Pscale ∧
      Lmin ≤ S.value ∧ (S.value : ℝ) ≤ Real.exp (allocatedWitnessScaleLog Pseed Qw) ∧
      (∀ j i, S.value ^ (j.val + 1) < basisAxisScale (b j) i →
        8 * (probabilityProfileLipschitz : ℝ) * W ≤
          (layerSamplerGapWidth («G» := (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) R ⟨j, i⟩ / 2) *
            ((basisAxisScale (b j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) ∧
      (∀ s : K, PreparedUniformDegreeGeometryAt («G» := (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) U b S (degree s) (Cdetect s) nX
        Bstruct Pscale D (target s) (Pk s) (Prho s) Qstride (pDetect s) pRadius (aDetect s) (detectionGain s)) ∧
      (∀ k, PreparedUniformDegreeDirectScalarBounds (max m cutoff) (degree k) nX
        (Fintype.card (LayerSamplerVariables
          (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))
          (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff)))
          (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))))
        (Cdetect k) Bstruct Pscale D (target k) (Pk k) (Prho k) Qstride (Pmaster k) Plate
        (detectionGain k) (Pphysical k) coarseTarget pRadius (sourceU k) (modelLog k) (sliceLog k)) ∧
      (∀ k, PreparedScheduledDirectSourceAvailability
          (B := EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))
          (U := U) (basis := b) (S := S) (hR := hR) (hσ := fun _ => hσ)
          (selection := enlargedPreparedCommonCanonicalSelection (max m cutoff)
            (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)) (degree k) (preparedFiniteNestedForwardAllDegreeDegree_le (Nat.le_max_right m cutoff) k))
          (stride := stride) (N := N) (Pdetect := Pdetect)
          (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
          (Vtail := Vtail) (τ := τ) (hb := hb) (o := o)
          Bstruct Qstride (Pmaster k) Plate (detectionGain k) (Pphysical k) coarseTarget) ∧
      (∀ k, PreparedScheduledDegreeModelAvailability
          (B := EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))
          (U := U) (basis := b) (S := S) (hR := hR) (hσ := fun _ => hσ)
          (selection := enlargedPreparedCommonCanonicalSelection (max m cutoff)
            (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)) (degree k)
              (preparedFiniteNestedForwardAllDegreeDegree_le (Nat.le_max_right m cutoff) k))
          (stride := stride) (N := N) (Pdetect := Pdetect)
          (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
          (Vtail := Vtail) (τ := τ) (hb := hb) (o := o) (μ := μ)
          Bstruct Qstride (Pmaster k) Plate (detectionGain k) (Pphysical k) coarseTarget) ∧
      PreparedUniformDegreeProductiveSourceConclusion
        (m := (max m cutoff)) (nX := nX) (M := M) (prep := (prep.pad (max m cutoff))) (U := U) (b := b) (S := S)
        (hR := hR) (hσ := fun _ => hσ) (stride := stride) (N := N)
        (Pdetect := Pdetect) (pModel := modelLog kModel) (pSlice := sliceLog kModel)
        (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
        (hb := hb) (o := o) (bW := bW) (μ := μ)
        Bstruct Qstride (Pmaster kModel) Plate (detectionGain kModel) (Pphysical kModel) coarseTarget
        pRadius Pscale Pseed Qw gainLog gain Vlog Qgood := by
  exact exists_preparedFiniteForwardSeededIndexedProductiveSource
    (m := max m cutoff) (nX := nX) (M := M) (prep.pad (max m cutoff)) U b stride N Pdetect Vtail
    Q hb o bW ν μ μrows innerDepth A Cslice Cdirect stageCountConstant
    preparedFiniteNestedForwardAllDegreeStage preparedFiniteNestedForwardAllDegreeIsDirect
    (preparedFiniteNestedForwardAllDegreeSeed A stageCountConstant Bstruct)
    preparedFiniteNestedForwardAllDegreeDegree (preparedFiniteNestedForwardAllDegreeAnchor outerDepth innerDepth cutoff)
    (preparedFiniteNestedForwardAllDegreeDegree_le (Nat.le_max_right m cutoff))
    (preparedFiniteNestedForwardAllDegreeAnchor_degree outerDepth innerDepth cutoff)
    (preparedFiniteNestedForwardAllDegreeAnchor_model outerDepth innerDepth cutoff)
    hA hSliceExponent
    Bstruct Qstride forecastCap stageLog Qσ Qw Pmin requestedCoarse gainLog gain Vlog
    Lmin Qgood hm hnX
    (prep.pad_coordinate_card_le hCoord)
    hB (fun k => le_preparedFiniteNestedForwardAllDegreeSeed A stageCountConstant hA hB k)
    hstage hQstride hQσ hQw hPmin hLmin hg hVlog hQgood hQexp hgain hnChart hgChart

end Erdos3.VectorPolynomial

end

end OAI
