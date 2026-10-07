import OAI.Combinatorics.Progressions.Estimates.PreparedCanonicalInitializedRelativeSourceConclusion

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

noncomputable def preparedFiniteNestedSourceLiteralRequired
    (m cutoff A Cdirect outerDepth innerDepth : ℕ) (constants : ℕ → ℕ)
    (G : Type) [Fintype G] (M count nX : ℕ)
    (Bstruct pnum Qstride gainLog stageLog Vlog Qσ Pmin requestedCoarse endpoint : ℝ) : ℝ :=
  let K := PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff
  let degree : K → ℕ := preparedFiniteNestedForwardAllDegreeDegree
  let Pdetect := preparedFiniteForwardDetectorPolynomial cutoff
  let Cdetect := fun k : K => sampledSupportedSlicedDetectionConstant (degree k) Pdetect
  let kModel : K := preparedFiniteNestedForwardAllDegreeAnchor outerDepth innerDepth cutoff
  let sourceU := fun k : K => preparedFiniteForwardPairedSourcePrecision A Cdirect constants
    (preparedFiniteNestedForwardAllDegreeStage k).val (preparedFiniteNestedForwardAllDegreeIsDirect k)
    (preparedFiniteNestedForwardAllDegreeSeed A constants Bstruct k) gainLog stageLog
  let modelLog := fun k : K => preparedFiniteForwardWork A constants
    (preparedFiniteNestedForwardAllDegreeStage k).val
    (preparedFiniteNestedForwardAllDegreeSeed A constants Bstruct k)
  let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
  let D := allocatedComparisonDimension m pnum
  let pDetect := fun k => allocatedModelTestLog (sourceU k) (modelLog k)
  let aDetect := fun k => 2 * sourceU k + 4 * modelLog k + 7
  let detectionGain := fun k : K => slicedDetectionGainLog (degree k) (Cdetect k) count
    (pDetect k) (pDetect k) (aDetect k)
  let Pk := fun k : K => scalarKernelLogarithmicBudget (Fin (degree k + 1)) G
    (detectionGain k + pDetect k + 4)
  let Pphysical := fun k : K => preparedFiniteScheduleLocalPhysical m nX count Qstride (Pk k)
  let target := fun k => detectionGain k + 40 + coefficientErrorSpatialLog (Pphysical k)
  let Eprofile := fun k : K => target k + D * ((m * 2 ^ (m + 1) : ℕ) * Pk k) + 5
  let Prho := fun k : K => 2 * affineProfileInputEnvelope D
    (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (Eprofile k) (pDetect k + 2) + 2
  let Ptail := fun k : K => affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
    (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (Eprofile k) (pDetect k + 2)
  let Pscale := preparedUniformDegreeScaleLog (D + pRadius) Ptail Qσ
  let Tmod := fun k : K => ((m + 1 : ℕ) : ℝ) * Pk k + nX * Qstride
  let lengthLogs := fun k : K => allocatedAffineLengthLog m D Pscale (Prho k) (Pk k)
    (target k) (pDetect k + 2) (Tmod k)
  let Pseed := allocatedScaleLog (Pscale + ∑ k, lengthLogs k + Pmin + 1)
  let Qw := 2 * Bstruct + 2 * Vlog + 5 * (gainLog + 8) + 24
  let Pmaster := fun k : K => preparedFiniteScheduleLocalMaster Bstruct D pRadius Qstride
    (Pphysical k) (sourceU k) (modelLog k) (Prho k) (target k) (detectionGain k)
  let coarseTarget := preparedFiniteScheduleDirectCoarse detectionGain requestedCoarse
  let Plate := ∑ k : K, preparedUniformDegreeDirectLate (Pmaster k) Pscale
    (Pphysical k) coarseTarget (allocatedWitnessScaleLog Pseed Qw)
  let native : K → ℝ := fun k =>
    (preparedModularGeneralDetectorResources
      (preparedModularGeneralDetectorConstants m (degree k))
      (degree k + 1) (Pmaster k) Plate).nativeBudget
  let Econditional := preparedNestedFrontProjectionEnvelope A constants innerDepth
    (fun k : K => k.1.val) (fun k : K => k.2.1.val) native
    Bstruct gainLog stageLog endpoint
  let baseB0 := preparedUniformDegreeProductiveCertificateBudget
    M nX pRadius Pscale Pseed Qw (gainLog + 8) Vlog
  let Pwidth := 4 * (Plate + 8) ^ 2
  let Bcert := preparedForecastGoodCertificateBudget baseB0 Bstruct Pwidth gainLog Vlog
  let Pgood := preparedForecastGoodAnalyticBudget (preparedCenteredShortForecastSpatialExponent m)
    baseB0 Bstruct Pwidth gainLog Vlog
  let anchorRequired := preparedFiniteScheduleAnchorGoodRequired
    m (Pmaster kModel) Plate Econditional Bcert Pgood Pwidth
  let conditionalRequired := preparedConditionalExcessRequired m Plate Econditional
  let detectorRequired := fun k : K => (preparedModularGeneralDetectorResources
    (preparedModularGeneralDetectorConstants m (degree k)) (degree k + 1) (Pmaster k) Plate).required
  let Rreq := preparedFiniteNestedSourceRequired A constants innerDepth outerDepth cutoff Bstruct
    anchorRequired conditionalRequired detectorRequired
  Rreq

theorem preparedFiniteNestedSourceLiteralRequired_eq
    (m cutoff A Cdirect outerDepth innerDepth : ℕ) (constants : ℕ → ℕ)
    (G : Type) [Fintype G] (M count nX : ℕ)
    (Bstruct pnum Qstride gainLog stageLog Vlog Qσ Pmin requestedCoarse endpoint : ℝ) :
    preparedFiniteNestedSourceLiteralRequired m cutoff A Cdirect outerDepth innerDepth constants
      G M count nX Bstruct pnum Qstride gainLog stageLog Vlog Qσ Pmin requestedCoarse endpoint =
    preparedFiniteNestedSourceRequiredLog m cutoff A Cdirect outerDepth innerDepth constants
      G M count nX Bstruct pnum Qstride gainLog stageLog Vlog Qσ Pmin requestedCoarse endpoint := by
  rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct
attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection integerBox
  RankPreparationFamily.PreparedHeights.canonicalPaddedSamplerData

noncomputable def preparedCanonicalInitializedRelativeSourceDataConclusion
    {nX m s D Erest : ℕ} (prep : RankPreparationFamily (Fin nX) (Fin D) m)
    (oldPatch : PolynomialPatch (Fin nX) s (D + Erest)) (F : oldPatch.LowestLayerModel m)
    (outerDepth innerDepth e Cprimitive Cdirect extra : ℕ)
    {p pRelative Bstruct knob pPrep pLate precisionBudget : ℝ} {Rrank : ℕ}
    (hheight : prep.PreparedHeights pPrep Rrank) (_hsize : prep.Sized D (m * D))
    (_hms : m ≤ s) (_hs : 1 ≤ s) (_hnX : 0 < nX)
    (_hp : 2 ≤ p) (_hpPrep : 0 ≤ pPrep) (_hRank : 1 ≤ Rrank)
    (_hPrepLate : pPrep ≤ pLate) (_hRankLate : (Rrank : ℝ) ≤ Real.exp pLate)
    (_hCapLate : (preparationCoordinateCap (max m s) D (s * D) : ℝ) ≤ pLate)
    (_hprimitive : 1 ≤ Cprimitive) (_hknob : 0 ≤ knob)
    (_hstructure :
      let M := preparationCoordinateCap s D (s * D)
      let Jalloc := modularInitialBlockCount s (nX + s * M)
      let dim := enlargedPreparedCommonSamplerDimension s M Jalloc
      p ≤ pRelative ∧ (s : ℝ) + 3 ≤ pRelative ∧
        (M : ℝ) ≤ pRelative ∧ (Jalloc : ℝ) ≤ pRelative ∧
        (dim : ℝ) ≤ pRelative ∧ allocatedUniformChartLog (M : ℝ) + 1 ≤ pRelative)
    (_hBrelative : 6 * pRelative + 35 ≤ Bstruct)
    (_hprecision : 3 * pRelative + 130 ≤ precisionBudget)
    (_hnXp : (nX : ℝ) ≤ p)
    (_hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Bstruct)
    (_hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Bstruct)
    (N : Fin nX → ℕ)
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ))
      (Rrank : ℝ) (prep j).space (prep j).poly)
    (_hN : ∀ i, Real.exp (preparedCanonicalRelativeSourceRequired prep s outerDepth innerDepth
      e Cprimitive Cdirect extra Bstruct p knob) ≤ (N i : ℝ))
    (_hSourceRank : Real.exp (preparedCanonicalRelativeSourceRequired prep s outerDepth innerDepth
      e Cprimitive Cdirect extra Bstruct p knob) ≤ (Rrank : ℝ))
    (ip : Fin D → MvPolynomial (Fin nX) ℤ) (_hip : ∀ i, (ip i).totalDegree ≤ m)
    (c₀ : Fin D → ℝ) (err : VectorPolynomial (Fin nX) ℝ (Fin D → ℝ))
    (_hprepare : ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
      prep.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c₀) + err)
    (_herr : ∀ x ∈ integerBox N, ∀ i,
      |eval (fun z => (x z : ℝ)) err i| ≤ Real.exp (-precisionBudget))
    {n₀ stage d₀ : ℕ} {discount : ℝ} {childCutoff childCost : ℝ → ℝ}
    (_ih : RelativePatchInductionRule s n₀ stage discount childCutoff childCost)
    {a Λ initialCost : ℝ}
    (_ha : Real.exp (-p) ≤ a) (_haΛ : a ≤ Λ) (_hΛ : Λ ≤ 1)
    (_habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀)
    (_hOldComplexity : relativePatchComplexity oldPatch ≤ p)
    (_hDpos : 0 < D) (_hrest : ∀ i : Fin Erest, m < oldPatch.weight (i.natAdd D))
    (_hOldStage : relativePatchDistinctWeights oldPatch ≤ stage + 1)
    (f : (Fin nX → ℤ) → ℝ)
    (_hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (_hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2))
    (_hscore : Real.exp (-p) ≤ relativePatchBoxScore N f a oldPatch)
    (_hdiscount : discount ∈ Set.Icc (0 : ℝ) 1)
    (_hchildCost : 0 ≤ childCost (pRelative + 2))
    (_hCost : childCost (pRelative + 2) ≤ initialCost)
    (H Lmin Qgood : ℕ) (_hHLmin : H ≤ Lmin)
    (_hHcut : Real.exp (childCutoff (pRelative + 2)) ≤ (H : ℝ))
    (_hHcost : (H : ℝ) ≤ Real.exp initialCost)
    (_hLmin : (Lmin : ℝ) ≤ Real.exp knob)
    (_hQgood : 1 ≤ Qgood) (_hQexp : (Qgood : ℝ) ≤ Real.exp knob)
    (data :
      let q := max m s
      let M := preparationCoordinateCap q D (s * D)
      let Jalloc := modularInitialBlockCount q (nX + q * M)
      let G := EnlargedPreparedCommonKernel q Jalloc
      let Vars := LayerSamplerVariables G (PreparedSamplerContinuous (prep.pad q))
        (preparedSamplerTransverse (prep.pad q)) (EnlargedPreparedCommonSamplerBlock (prep.pad q) Jalloc)
      (prep.pad q).CanonicalSamplerData Vars M pLate) : Prop :=
    let q := max m s
    let M := preparationCoordinateCap q D (s * D)
    let Jalloc := modularInitialBlockCount q (nX + q * M)
    let G := EnlargedPreparedCommonKernel q Jalloc
    let Vars := LayerSamplerVariables G (PreparedSamplerContinuous (prep.pad q))
      (preparedSamplerTransverse (prep.pad q)) (EnlargedPreparedCommonSamplerBlock (prep.pad q) Jalloc)
    let U := fun j => (prep.pad q j).space
    letI : ∀ j, DecidableEq (prep.pad q j).Coord := fun _ => Classical.decEq _
    letI := data.measures.lattice
    letI := data.measures.coefficientCompact
    letI := data.measures.coefficientBorel
    letI := data.measures.rowCompact
    letI := data.measures.rowBorel
    letI := data.measures.siteBorel
    letI := data.measures.layerInvariant
    letI := data.measures.layerProbability
    letI := data.measures.coefficientInvariant
    letI := data.measures.coefficientProbability
    letI := data.measures.rowInvariant
    letI := data.measures.rowProbability
    let b := data.b
    let hb := data.span_eq
    let o := data.o
    let bW := data.bW
    let _ν := data.measures.layer
    let μ := data.measures.coefficient
    let _μrows := data.measures.row
    let cutoff := s
    let Q := PreparedSamplerContinuous (prep.pad q)
    let Qstride : ℝ := 0
    let stageLog : ℝ := 0
    let endpoint := knob
    let Qσ := knob
    let Pmin := knob
    let requestedCoarse := knob
    let gainLog := p
    let gain := Real.exp (-p)
    let Vlog := knob
    let pchild := pRelative + 2
    let chartLog := allocatedUniformChartLog (M : ℝ)
    let Vtail : Fin q → ℝ≥0 := fun _ => ⟨Real.exp chartLog, (Real.exp_pos _).le⟩
    let stride : Fin nX → ℕ := fun _ => 1
    let cells : Finset (ColumnResiduePattern (Option Vars) (Fin nX) stride) := {0}
    let hmem := prep.pad_coefficients_mem (q := q) (fun j => (hheight j).2.1)
    let stageCountConstant := AllocatedExternalCandidateSampler.degreeSourceCountConstants
    let A := preparedFiniteNestedSourceExponent (max m cutoff) cutoff e Cprimitive Cdirect extra
    let Cslice := preparedFiniteNestedSourceSliceExponent (max m cutoff) cutoff Cprimitive
    let forecastCap : ℝ := 1
    let Qw := 2 * Bstruct + 2 * Vlog + 5 * (gainLog + 8) + 24
    let Pdetect := preparedFiniteForwardDetectorPolynomial cutoff
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
    let native : K → ℝ := fun k =>
      (preparedModularGeneralDetectorResources
        (preparedModularGeneralDetectorConstants (max m cutoff) (degree k))
        (degree k + 1) (Pmaster k) Plate).nativeBudget
    let Econditional := preparedNestedFrontProjectionEnvelope A stageCountConstant innerDepth
      (fun k : K => k.1.val) (fun k : K => k.2.1.val) native
      Bstruct gainLog stageLog endpoint
    let τ := Real.exp (-(gainLog + (nX : ℝ) + 8))
    let α := fun k : K => Real.exp (-(2 * preparedFiniteForwardModelPrecision A stageCountConstant
      (preparedFiniteNestedForwardAllDegreeStage k).val
      (preparedFiniteNestedForwardAllDegreeSeed A stageCountConstant Bstruct k) gainLog stageLog +
      4 * modelLog k + 8))
    let baseB0 := preparedUniformDegreeProductiveCertificateBudget M nX pRadius Pscale Pseed Qw (gainLog + 8) Vlog
    let Pwidth := 4 * (Plate + 8) ^ 2
    let Bcert := preparedForecastGoodCertificateBudget baseB0 Bstruct Pwidth gainLog Vlog
    let Pgood := preparedForecastGoodAnalyticBudget (preparedCenteredShortForecastSpatialExponent (max m cutoff))
      baseB0 Bstruct Pwidth gainLog Vlog
    let anchorRequired := preparedFiniteScheduleAnchorGoodRequired (max m cutoff) (Pmaster kModel) Plate Econditional Bcert Pgood Pwidth
    let conditionalRequired := preparedConditionalExcessRequired (max m cutoff) Plate Econditional
    let detectorRequired := fun k : K => (preparedModularGeneralDetectorResources
      (preparedModularGeneralDetectorConstants (max m cutoff) (degree k)) (degree k + 1) (Pmaster k) Plate).required
    let _Rreq := preparedFiniteNestedSourceRequired A stageCountConstant innerDepth outerDepth cutoff Bstruct
      anchorRequired conditionalRequired detectorRequired
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
        pRadius Pscale Pseed Qw gainLog gain Vlog Qgood ∧
      ∃ (hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i)
        (Acandidate : AllocatedExternalCandidateSamplerFamily (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) U b S hb o hR (fun _ => hσ)
          N (fun j => (prep.pad (max m cutoff) j).poly) hmem τ (Real.exp (-Plate)) stride cells)
        (hξone : Real.exp (-Plate) ≤ 1),
      PreparedCenteredProductiveGoodCenterEnhancedConclusion (m := (max m cutoff)) (nX := nX) (M := M)
        (prep.pad (max m cutoff)) U b S bW hb o hR (fun _ => hσ) μ (fun j => (prep.pad (max m cutoff) j).poly) hmem stride
        (allocatedExternalCandidateWidths (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) U b S N τ (Real.exp (-Plate))) (Acandidate 0).bases
        gainLog gain Qgood (preparedSpatialKernelBlocks (max m cutoff) M nX) Acandidate.law N (relativePatchSourceTest N f a oldPatch)
        (fun center =>
          let _ : DecidableEq (Fin nX) := Classical.decEq _
          ((∀ k : K, (Acandidate center).NativeDetection (degree k) (sliceLog k)
            (Pdetect.eval₂ (Nat.castRingHom ℝ) (pDetect k))
            (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants (max m cutoff) (degree k))
              (degree k + 1) (Pmaster k) Plate).nativeBudget (α k)) ∧
          letI : Nonempty (Acandidate center).Site := (Acandidate center).site_nonempty
          (FiniteProbabilityWeights.uniformFinset (integerBox N) (Acandidate center).integerBox_nonempty).excessMass
            ((Acandidate center).law.siteLaw ((Acandidate center).physicalBox hξone hmargin))
            (4 * ∏ j, earlyConstantDensityCap (Fintype.card ((PreparedSamplerContinuous (prep.pad (max m cutoff))) j)) ((preparedSamplerTransverse (prep.pad (max m cutoff))) j) (R j) (Vtail j)) ≤
              6 * positiveProjectionAccuracy Econditional) ∧
          ∀ (outerFront outerInner : Fin (outerDepth + 1)) (d : ℕ),
            ∀ (hd : d ≤ cutoff), d ≤ innerDepth → ∀ (pInput : ℝ),
            pInput ∈ Set.Icc 0 (candidateNestedForwardSeed A stageCountConstant innerDepth outerFront.val Bstruct) →
            pInput ≤ candidateNestedForwardSeed A stageCountConstant innerDepth outerInner.val Bstruct →
            ∃ profile : (Acandidate center).DegreeSourceProfile d pInput e,
              profile.inner.x = candidateNestedForwardSeed A stageCountConstant innerDepth outerInner.val Bstruct ∧
              profile.inner.gainLog = candidateNestedForwardSeed A stageCountConstant innerDepth outerInner.val Bstruct ∧
              profile.front.u = preparedFiniteForwardModelPrecision A stageCountConstant 0
                (candidateNestedForwardSeed A stageCountConstant innerDepth outerFront.val Bstruct) gainLog stageLog ∧
              profile.front.pModel = preparedFiniteForwardWork A stageCountConstant 0
                (candidateNestedForwardSeed A stageCountConstant innerDepth outerFront.val Bstruct) ∧
              profile.front.nativeBudget = native (outerFront, 0, ⟨d, Nat.lt_succ_of_le hd⟩, false) ∧
              profile.inner.Cprimitive = Cprimitive ∧
              profile.inner.scheduleExponent = A ∧
              profile.inner.Csource = preparedFiniteNestedSourceNativeExponent (max m cutoff) cutoff Cdirect)
        (fun center centerLift productive =>
          AllocatedNormalizedCandidateConclusion (E := Q) (A := Acandidate center)
            s (fun k => H ≤ (Acandidate center).sides k) centerLift productive
            (childCost pchild) initialCost (d₀ + s * Erest) f
            ((1 - discount) ^ (stage + 1) * Λ))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

theorem preparedCanonicalRelative_initializerInputs
    {nX s D E m n₀ d₀ : ℕ}
    (oldPatch : PolynomialPatch (Fin nX) s (D + E))
    (prep : RankPreparationFamily (Fin nX) (Fin D) m)
    {p pRelative precisionBudget a Λ : ℝ}
    (hsize : prep.Sized D (m * D)) (hms : m ≤ s) (hp : 2 ≤ p)
    (hstructure :
      let M := preparationCoordinateCap s D (s * D)
      let Jalloc := modularInitialBlockCount s (nX + s * M)
      let dim := enlargedPreparedCommonSamplerDimension s M Jalloc
      p ≤ pRelative ∧ (s : ℝ) + 3 ≤ pRelative ∧
        (M : ℝ) ≤ pRelative ∧ (Jalloc : ℝ) ≤ pRelative ∧
        (dim : ℝ) ≤ pRelative ∧ allocatedUniformChartLog (M : ℝ) + 1 ≤ pRelative)
    (hprecision : 3 * pRelative + 130 ≤ precisionBudget)
    (hcomplexity : relativePatchComplexity oldPatch ≤ p)
    (ha : Real.exp (-p) ≤ a)
    (habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀) :
    let M := preparationCoordinateCap (max m s) D (s * D)
    PreparedRelativeInitializerScalarInputs oldPatch
      (fun j => Fintype.card (prep.pad (max m s) j).Coord)
      (preparedRelativeInitializerVariableCount prep s M)
      p pRelative precisionBudget (allocatedUniformChartLog (M : ℝ)) a Λ n₀ d₀ := by
  intro M
  have hcoord : ∀ j, Fintype.card (prep j).Coord ≤ preparationCoordinateCap m D (m * D) :=
    fun j => (preparationCoordinateCap_bounds hsize le_rfl j).1
  have hM : M = preparationCoordinateCap s D (s * D) := by
    dsimp only [M]
    rw [max_eq_right hms]
  rw [hM]
  exact preparedRelativeInitializer_scalarInputs oldPatch prep hp hms hcoord
    hstructure hprecision hcomplexity ha habsolute

noncomputable def preparedCanonicalRelativeLiteralRequired
    {nX D m : ℕ} (prep : RankPreparationFamily (Fin nX) (Fin D) m)
    (s outerDepth innerDepth e Cprimitive Cdirect extra : ℕ)
    (Bstruct p knob : ℝ) : ℝ :=
  let q := max m s
  let M := preparationCoordinateCap q D (s * D)
  let Jalloc := modularInitialBlockCount q (nX + q * M)
  let G := EnlargedPreparedCommonKernel q Jalloc
  let count := Fintype.card (LayerSamplerVariables G
    (PreparedSamplerContinuous (prep.pad q)) (preparedSamplerTransverse (prep.pad q))
    (EnlargedPreparedCommonSamplerBlock (prep.pad q) Jalloc))
  preparedFiniteNestedSourceLiteralRequired q s
    (preparedFiniteNestedSourceExponent q s e Cprimitive Cdirect extra) Cdirect outerDepth innerDepth
    AllocatedExternalCandidateSampler.degreeSourceCountConstants G M count nX Bstruct
    (enlargedPreparedCommonSamplerDimension q M Jalloc) 0 p 0 knob knob knob knob knob

theorem preparedCanonicalRelativeLiteralRequired_eq
    {nX D m : ℕ} (prep : RankPreparationFamily (Fin nX) (Fin D) m)
    (s outerDepth innerDepth e Cprimitive Cdirect extra : ℕ)
    (Bstruct p knob : ℝ) :
    preparedCanonicalRelativeLiteralRequired prep s outerDepth innerDepth e Cprimitive Cdirect extra
      Bstruct p knob =
    preparedCanonicalRelativeSourceRequired prep s outerDepth innerDepth e Cprimitive Cdirect extra
      Bstruct p knob := by
  exact preparedFiniteNestedSourceLiteralRequired_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem preparedCanonicalRelativeLiteralRequired_floors
    {nX D m : ℕ} (prep : RankPreparationFamily (Fin nX) (Fin D) m)
    (s outerDepth innerDepth e Cprimitive Cdirect extra : ℕ)
    (Bstruct p knob : ℝ) (N : Fin nX → ℕ) (rankThreshold : ℝ)
    (hN : ∀ i, Real.exp (preparedCanonicalRelativeSourceRequired prep s outerDepth innerDepth
      e Cprimitive Cdirect extra Bstruct p knob) ≤ (N i : ℝ))
    (hrank : Real.exp (preparedCanonicalRelativeSourceRequired prep s outerDepth innerDepth
      e Cprimitive Cdirect extra Bstruct p knob) ≤ rankThreshold) :
    (∀ i, Real.exp (preparedCanonicalRelativeLiteralRequired prep s outerDepth innerDepth
      e Cprimitive Cdirect extra Bstruct p knob) ≤ (N i : ℝ)) ∧
    Real.exp (preparedCanonicalRelativeLiteralRequired prep s outerDepth innerDepth
      e Cprimitive Cdirect extra Bstruct p knob) ≤ rankThreshold := by
  rw [preparedCanonicalRelativeLiteralRequired_eq]
  exact ⟨hN, hrank⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct
attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection integerBox
  RankPreparationFamily.PreparedHeights.canonicalPaddedSamplerData
  preparedFiniteNestedSourceRequiredLog

theorem preparedCanonicalInitializedRelativeSourceCore
    {nX m s D Erest : ℕ} (prep : RankPreparationFamily (Fin nX) (Fin D) m)
    (oldPatch : PolynomialPatch (Fin nX) s (D + Erest)) (F : oldPatch.LowestLayerModel m)
    (outerDepth innerDepth e Cprimitive Cdirect extra : ℕ)
    {p pRelative Bstruct knob pPrep pLate precisionBudget : ℝ} {Rrank : ℕ}
    (hheight : prep.PreparedHeights pPrep Rrank) (hsize : prep.Sized D (m * D))
    (hms : m ≤ s) (hs : 1 ≤ s) (hnX : 0 < nX)
    (hp : 2 ≤ p) (hpPrep : 0 ≤ pPrep) (hRank : 1 ≤ Rrank)
    (hPrepLate : pPrep ≤ pLate) (hRankLate : (Rrank : ℝ) ≤ Real.exp pLate)
    (hCapLate : (preparationCoordinateCap (max m s) D (s * D) : ℝ) ≤ pLate)
    (hprimitive : 1 ≤ Cprimitive) (hknob : 0 ≤ knob)
    (hstructure :
      let M := preparationCoordinateCap s D (s * D)
      let Jalloc := modularInitialBlockCount s (nX + s * M)
      let dim := enlargedPreparedCommonSamplerDimension s M Jalloc
      p ≤ pRelative ∧ (s : ℝ) + 3 ≤ pRelative ∧
        (M : ℝ) ≤ pRelative ∧ (Jalloc : ℝ) ≤ pRelative ∧
        (dim : ℝ) ≤ pRelative ∧ allocatedUniformChartLog (M : ℝ) + 1 ≤ pRelative)
    (hBrelative : 6 * pRelative + 35 ≤ Bstruct)
    (hprecision : 3 * pRelative + 130 ≤ precisionBudget)
    (hnXp : (nX : ℝ) ≤ p)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Bstruct)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Bstruct)
    (N : Fin nX → ℕ)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ))
      (Rrank : ℝ) (prep j).space (prep j).poly)
    (hN : ∀ i, Real.exp (preparedCanonicalRelativeSourceRequired prep s outerDepth innerDepth
      e Cprimitive Cdirect extra Bstruct p knob) ≤ (N i : ℝ))
    (hSourceRank : Real.exp (preparedCanonicalRelativeSourceRequired prep s outerDepth innerDepth
      e Cprimitive Cdirect extra Bstruct p knob) ≤ (Rrank : ℝ))
    (ip : Fin D → MvPolynomial (Fin nX) ℤ) (hip : ∀ i, (ip i).totalDegree ≤ m)
    (c₀ : Fin D → ℝ) (err : VectorPolynomial (Fin nX) ℝ (Fin D → ℝ))
    (hprepare : ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
      prep.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c₀) + err)
    (herr : ∀ x ∈ integerBox N, ∀ i,
      |eval (fun z => (x z : ℝ)) err i| ≤ Real.exp (-precisionBudget))
    {n₀ stage d₀ : ℕ} {discount : ℝ} {childCutoff childCost : ℝ → ℝ}
    (ih : RelativePatchInductionRule s n₀ stage discount childCutoff childCost)
    {a Λ initialCost : ℝ}
    (ha : Real.exp (-p) ≤ a) (haΛ : a ≤ Λ) (hΛ : Λ ≤ 1)
    (habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀)
    (hOldComplexity : relativePatchComplexity oldPatch ≤ p)
    (hDpos : 0 < D) (hrest : ∀ i : Fin Erest, m < oldPatch.weight (i.natAdd D))
    (hOldStage : relativePatchDistinctWeights oldPatch ≤ stage + 1)
    (f : (Fin nX → ℤ) → ℝ)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2))
    (hscore : Real.exp (-p) ≤ relativePatchBoxScore N f a oldPatch)
    (hdiscount : discount ∈ Set.Icc (0 : ℝ) 1)
    (hchildCost : 0 ≤ childCost (pRelative + 2))
    (hCost : childCost (pRelative + 2) ≤ initialCost)
    (H Lmin Qgood : ℕ) (hHLmin : H ≤ Lmin)
    (hHcut : Real.exp (childCutoff (pRelative + 2)) ≤ (H : ℝ))
    (hHcost : (H : ℝ) ≤ Real.exp initialCost)
    (hLmin : (Lmin : ℝ) ≤ Real.exp knob)
    (hQgood : 1 ≤ Qgood) (hQexp : (Qgood : ℝ) ≤ Real.exp knob)
    (data :
      let q := max m s
      let M := preparationCoordinateCap q D (s * D)
      let Jalloc := modularInitialBlockCount q (nX + q * M)
      let G := EnlargedPreparedCommonKernel q Jalloc
      let Vars := LayerSamplerVariables G (PreparedSamplerContinuous (prep.pad q))
        (preparedSamplerTransverse (prep.pad q)) (EnlargedPreparedCommonSamplerBlock (prep.pad q) Jalloc)
      (prep.pad q).CanonicalSamplerData Vars M pLate)
    (hScalar : PreparedCanonicalRelativeScalarInputs prep s p pRelative Bstruct)
    (hInputs :
      let q := max m s
      let M := preparationCoordinateCap q D (s * D)
      let Jalloc := modularInitialBlockCount q (nX + q * M)
      let G := EnlargedPreparedCommonKernel q Jalloc
      let Vars := LayerSamplerVariables G (PreparedSamplerContinuous (prep.pad q))
        (preparedSamplerTransverse (prep.pad q)) (EnlargedPreparedCommonSamplerBlock (prep.pad q) Jalloc)
      PreparedRelativeInitializerScalarInputs oldPatch
        (fun j => Fintype.card (prep.pad q j).Coord) (Fintype.card Vars)
        p pRelative precisionBudget (allocatedUniformChartLog (M : ℝ)) a Λ n₀ d₀)
    (hPhysicalSize : ∀ i, 4 ≤ Real.exp (-(p + nX + 8)) * (N i : ℝ))

    (hNliteral : ∀ i, Real.exp (preparedCanonicalRelativeLiteralRequired prep s outerDepth innerDepth
      e Cprimitive Cdirect extra Bstruct p knob) ≤ (N i : ℝ))
    (hRankLiteral : Real.exp (preparedCanonicalRelativeLiteralRequired prep s outerDepth innerDepth
      e Cprimitive Cdirect extra Bstruct p knob) ≤ (Rrank : ℝ)) :
    preparedCanonicalInitializedRelativeSourceDataConclusion
      (nX := nX) (m := m) (s := s) (D := D)
      (Erest := Erest) (prep := prep) (oldPatch := oldPatch) (F := F)
      (outerDepth := outerDepth) (innerDepth := innerDepth) (e := e) (Cprimitive := Cprimitive)
      (Cdirect := Cdirect) (extra := extra) (p := p) (pRelative := pRelative)
      (Bstruct := Bstruct) (knob := knob) (pPrep := pPrep) (pLate := pLate)
      (precisionBudget := precisionBudget) (Rrank := Rrank) (hheight := hheight) (_hsize := hsize)
      (_hms := hms) (_hs := hs) (_hnX := hnX) (_hp := hp)
      (_hpPrep := hpPrep) (_hRank := hRank) (_hPrepLate := hPrepLate) (_hRankLate := hRankLate)
      (_hCapLate := hCapLate) (_hprimitive := hprimitive) (_hknob := hknob) (_hstructure := hstructure)
      (_hBrelative := hBrelative) (_hprecision := hprecision) (_hnXp := hnXp) (_hprofile := hprofile)
      (_hcutoff := hcutoff) (N := N) (_hrank := hrank) (_hN := hN)
      (_hSourceRank := hSourceRank) (ip := ip) (_hip := hip) (c₀ := c₀)
      (err := err) (_hprepare := hprepare) (_herr := herr) (n₀ := n₀)
      (stage := stage) (d₀ := d₀) (discount := discount) (childCutoff := childCutoff)
      (childCost := childCost) (_ih := ih) (a := a) (Λ := Λ)
      (initialCost := initialCost) (_ha := ha) (_haΛ := haΛ) (_hΛ := hΛ)
      (_habsolute := habsolute) (_hOldComplexity := hOldComplexity) (_hDpos := hDpos) (_hrest := hrest)
      (_hOldStage := hOldStage) (f := f) (_hf := hf) (_hfree := hfree)
      (_hscore := hscore) (_hdiscount := hdiscount) (_hchildCost := hchildCost) (_hCost := hCost)
      (H := H) (Lmin := Lmin) (Qgood := Qgood) (_hHLmin := hHLmin)
      (_hHcut := hHcut) (_hHcost := hHcost) (_hLmin := hLmin) (_hQgood := hQgood)
      (_hQexp := hQexp)
      (data := data) := by
  let q := max m s
  let M := preparationCoordinateCap q D (s * D)
  let Jalloc := modularInitialBlockCount q (nX + q * M)
  let G := EnlargedPreparedCommonKernel q Jalloc
  let Vars := LayerSamplerVariables G (PreparedSamplerContinuous (prep.pad q))
    (preparedSamplerTransverse (prep.pad q)) (EnlargedPreparedCommonSamplerBlock (prep.pad q) Jalloc)
  let chartLog := allocatedUniformChartLog (M : ℝ)
  let C : Fin q → ℝ := fun _ => Real.exp chartLog
  let Vtail : Fin q → ℝ≥0 := fun _ => ⟨Real.exp chartLog, (Real.exp_pos _).le⟩
  let stride : Fin nX → ℕ := fun _ => 1
  let cells : Finset (ColumnResiduePattern (Option Vars) (Fin nX) stride) := {0}
  let U := fun j => (prep.pad q j).space
  let : ∀ j, DecidableEq (prep.pad q j).Coord := fun _ => Classical.decEq _
  let := data.measures.lattice
  let := data.measures.coefficientCompact
  let := data.measures.coefficientBorel
  let := data.measures.rowCompact
  let := data.measures.rowBorel
  let := data.measures.siteBorel
  let := data.measures.layerInvariant
  let := data.measures.layerProbability
  let := data.measures.coefficientInvariant
  let := data.measures.coefficientProbability
  let := data.measures.rowInvariant
  let := data.measures.rowProbability
  exact exists_preparedFiniteNestedInitializedRelativeSource_fullScalars
    (M := M) (δ := Real.exp (-precisionBudget)) (pInit := pRelative)
    (Pearly := 6 * pRelative + 35) (pchild := pRelative + 2)
    prep outerDepth innerDepth s oldPatch F U data.b stride N Vtail
    (PreparedSamplerContinuous (prep.pad q)) data.span_eq data.o data.bW
    data.measures.layer data.measures.coefficient data.measures.row
    e Cprimitive Cdirect extra hprimitive Bstruct 0 0 knob chartLog
    hknob hScalar.hchartBudget knob knob knob p (Real.exp (-p)) knob Lmin Qgood
    (Nat.lt_of_lt_of_le Nat.zero_lt_one (hs.trans (Nat.le_max_right m s))) hnX hScalar.hCoord hScalar.hB ⟨le_rfl, hScalar.hB⟩ ⟨le_rfl, hScalar.hB⟩
    hknob hknob hLmin hScalar.hp0 hknob hQgood hQexp le_rfl (hnXp.trans hScalar.hpSource) hScalar.hpSource
    (fun _ => Nat.zero_lt_one) (fun _ => by simp only [stride, Nat.cast_one, Real.exp_zero]; exact le_rfl)
    C (fun _ => (Real.exp_pos _).le) (fun _ => le_rfl) data.inverse_chart_bound
    Vtail data.chart_bound (fun _ => hScalar.hChartExp) (fun _ => hScalar.hChartExp) data.covolume_bound
    hprofile hcutoff cells (Finset.singleton_nonempty _) (prep.pad_degreeLE (fun j => (hheight j).1))
    (prep.pad_coefficients_mem (fun j => (hheight j).2.1))
    (Rrank : ℝ) (prep.pad_samplingRank _ _ hrank) ip hip c₀ err hprepare
    hInputs.hδ hInputs.hgain1 herr hInputs.hpInit hInputs.hDlog hInputs.hqlog hInputs.hLlog
    hInputs.hNlog hInputs.hClog hInputs.hgainlog hInputs.hδearly le_rfl hScalar.hEarlyRadius hPhysicalSize
    ih hInputs.hpchild hInputs.ha haΛ hΛ hInputs.habsolute hInputs.hDim H hHLmin hHcut
    hDpos hrest hInputs.hOldComplexity hOldStage f hf hfree hscore hdiscount hchildCost
    initialCost hCost hHcost hScalar.hnum hNliteral hRankLiteral

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct
attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection integerBox
  RankPreparationFamily.PreparedHeights.canonicalPaddedSamplerData
  preparedFiniteNestedSourceRequiredLog

theorem preparedCanonicalInitializedRelativeSourceDataProof
    {nX m s D Erest : ℕ} (prep : RankPreparationFamily (Fin nX) (Fin D) m)
    (oldPatch : PolynomialPatch (Fin nX) s (D + Erest)) (F : oldPatch.LowestLayerModel m)
    (outerDepth innerDepth e Cprimitive Cdirect extra : ℕ)
    {p pRelative Bstruct knob pPrep pLate precisionBudget : ℝ} {Rrank : ℕ}
    (hheight : prep.PreparedHeights pPrep Rrank) (hsize : prep.Sized D (m * D))
    (hms : m ≤ s) (hs : 1 ≤ s) (hnX : 0 < nX)
    (hp : 2 ≤ p) (hpPrep : 0 ≤ pPrep) (hRank : 1 ≤ Rrank)
    (hPrepLate : pPrep ≤ pLate) (hRankLate : (Rrank : ℝ) ≤ Real.exp pLate)
    (hCapLate : (preparationCoordinateCap (max m s) D (s * D) : ℝ) ≤ pLate)
    (hprimitive : 1 ≤ Cprimitive) (hknob : 0 ≤ knob)
    (hstructure :
      let M := preparationCoordinateCap s D (s * D)
      let Jalloc := modularInitialBlockCount s (nX + s * M)
      let dim := enlargedPreparedCommonSamplerDimension s M Jalloc
      p ≤ pRelative ∧ (s : ℝ) + 3 ≤ pRelative ∧
        (M : ℝ) ≤ pRelative ∧ (Jalloc : ℝ) ≤ pRelative ∧
        (dim : ℝ) ≤ pRelative ∧ allocatedUniformChartLog (M : ℝ) + 1 ≤ pRelative)
    (hBrelative : 6 * pRelative + 35 ≤ Bstruct)
    (hprecision : 3 * pRelative + 130 ≤ precisionBudget)
    (hnXp : (nX : ℝ) ≤ p)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Bstruct)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Bstruct)
    (N : Fin nX → ℕ)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ))
      (Rrank : ℝ) (prep j).space (prep j).poly)
    (hN : ∀ i, Real.exp (preparedCanonicalRelativeSourceRequired prep s outerDepth innerDepth
      e Cprimitive Cdirect extra Bstruct p knob) ≤ (N i : ℝ))
    (hSourceRank : Real.exp (preparedCanonicalRelativeSourceRequired prep s outerDepth innerDepth
      e Cprimitive Cdirect extra Bstruct p knob) ≤ (Rrank : ℝ))
    (ip : Fin D → MvPolynomial (Fin nX) ℤ) (hip : ∀ i, (ip i).totalDegree ≤ m)
    (c₀ : Fin D → ℝ) (err : VectorPolynomial (Fin nX) ℝ (Fin D → ℝ))
    (hprepare : ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
      prep.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c₀) + err)
    (herr : ∀ x ∈ integerBox N, ∀ i,
      |eval (fun z => (x z : ℝ)) err i| ≤ Real.exp (-precisionBudget))
    {n₀ stage d₀ : ℕ} {discount : ℝ} {childCutoff childCost : ℝ → ℝ}
    (ih : RelativePatchInductionRule s n₀ stage discount childCutoff childCost)
    {a Λ initialCost : ℝ}
    (ha : Real.exp (-p) ≤ a) (haΛ : a ≤ Λ) (hΛ : Λ ≤ 1)
    (habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀)
    (hOldComplexity : relativePatchComplexity oldPatch ≤ p)
    (hDpos : 0 < D) (hrest : ∀ i : Fin Erest, m < oldPatch.weight (i.natAdd D))
    (hOldStage : relativePatchDistinctWeights oldPatch ≤ stage + 1)
    (f : (Fin nX → ℤ) → ℝ)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2))
    (hscore : Real.exp (-p) ≤ relativePatchBoxScore N f a oldPatch)
    (hdiscount : discount ∈ Set.Icc (0 : ℝ) 1)
    (hchildCost : 0 ≤ childCost (pRelative + 2))
    (hCost : childCost (pRelative + 2) ≤ initialCost)
    (H Lmin Qgood : ℕ) (hHLmin : H ≤ Lmin)
    (hHcut : Real.exp (childCutoff (pRelative + 2)) ≤ (H : ℝ))
    (hHcost : (H : ℝ) ≤ Real.exp initialCost)
    (hLmin : (Lmin : ℝ) ≤ Real.exp knob)
    (hQgood : 1 ≤ Qgood) (hQexp : (Qgood : ℝ) ≤ Real.exp knob)
    (data :
      let q := max m s
      let M := preparationCoordinateCap q D (s * D)
      let Jalloc := modularInitialBlockCount q (nX + q * M)
      let G := EnlargedPreparedCommonKernel q Jalloc
      let Vars := LayerSamplerVariables G (PreparedSamplerContinuous (prep.pad q))
        (preparedSamplerTransverse (prep.pad q)) (EnlargedPreparedCommonSamplerBlock (prep.pad q) Jalloc)
      (prep.pad q).CanonicalSamplerData Vars M pLate) :
    preparedCanonicalInitializedRelativeSourceDataConclusion
      (nX := nX) (m := m) (s := s) (D := D)
      (Erest := Erest) (prep := prep) (oldPatch := oldPatch) (F := F)
      (outerDepth := outerDepth) (innerDepth := innerDepth) (e := e) (Cprimitive := Cprimitive)
      (Cdirect := Cdirect) (extra := extra) (p := p) (pRelative := pRelative)
      (Bstruct := Bstruct) (knob := knob) (pPrep := pPrep) (pLate := pLate)
      (precisionBudget := precisionBudget) (Rrank := Rrank) (hheight := hheight) (_hsize := hsize)
      (_hms := hms) (_hs := hs) (_hnX := hnX) (_hp := hp)
      (_hpPrep := hpPrep) (_hRank := hRank) (_hPrepLate := hPrepLate) (_hRankLate := hRankLate)
      (_hCapLate := hCapLate) (_hprimitive := hprimitive) (_hknob := hknob) (_hstructure := hstructure)
      (_hBrelative := hBrelative) (_hprecision := hprecision) (_hnXp := hnXp) (_hprofile := hprofile)
      (_hcutoff := hcutoff) (N := N) (_hrank := hrank) (_hN := hN)
      (_hSourceRank := hSourceRank) (ip := ip) (_hip := hip) (c₀ := c₀)
      (err := err) (_hprepare := hprepare) (_herr := herr) (n₀ := n₀)
      (stage := stage) (d₀ := d₀) (discount := discount) (childCutoff := childCutoff)
      (childCost := childCost) (_ih := ih) (a := a) (Λ := Λ)
      (initialCost := initialCost) (_ha := ha) (_haΛ := haΛ) (_hΛ := hΛ)
      (_habsolute := habsolute) (_hOldComplexity := hOldComplexity) (_hDpos := hDpos) (_hrest := hrest)
      (_hOldStage := hOldStage) (f := f) (_hf := hf) (_hfree := hfree)
      (_hscore := hscore) (_hdiscount := hdiscount) (_hchildCost := hchildCost) (_hCost := hCost)
      (H := H) (Lmin := Lmin) (Qgood := Qgood) (_hHLmin := hHLmin)
      (_hHcut := hHcut) (_hHcost := hHcost) (_hLmin := hLmin) (_hQgood := hQgood)
      (_hQexp := hQexp)
      (data := data) :=
  have hScalar := preparedCanonicalRelative_scalarInputs prep hsize hms hp hstructure hBrelative
  have hInputs := preparedCanonicalRelative_initializerInputs oldPatch prep hsize hms hp
    hstructure hprecision hOldComplexity ha habsolute
  have hPhysicalSize := preparedCanonicalRelativeSourceRequired_physicalSize
    prep s outerDepth innerDepth e Cprimitive Cdirect extra N hs hScalar.hB hScalar.hp0
    hScalar.hpSource hnXp hN
  have hFloors := preparedCanonicalRelativeLiteralRequired_floors prep s outerDepth innerDepth
    e Cprimitive Cdirect extra Bstruct p knob N (Rrank : ℝ) hN hSourceRank
  preparedCanonicalInitializedRelativeSourceCore
      (nX := nX) (m := m) (s := s) (D := D)
      (Erest := Erest) (prep := prep) (oldPatch := oldPatch) (F := F)
      (outerDepth := outerDepth) (innerDepth := innerDepth) (e := e) (Cprimitive := Cprimitive)
      (Cdirect := Cdirect) (extra := extra) (p := p) (pRelative := pRelative)
      (Bstruct := Bstruct) (knob := knob) (pPrep := pPrep) (pLate := pLate)
      (precisionBudget := precisionBudget) (Rrank := Rrank) (hheight := hheight) (hsize := hsize)
      (hms := hms) (hs := hs) (hnX := hnX) (hp := hp)
      (hpPrep := hpPrep) (hRank := hRank) (hPrepLate := hPrepLate) (hRankLate := hRankLate)
      (hCapLate := hCapLate) (hprimitive := hprimitive) (hknob := hknob) (hstructure := hstructure)
      (hBrelative := hBrelative) (hprecision := hprecision) (hnXp := hnXp) (hprofile := hprofile)
      (hcutoff := hcutoff) (N := N) (hrank := hrank) (hN := hN)
      (hSourceRank := hSourceRank) (ip := ip) (hip := hip) (c₀ := c₀)
      (err := err) (hprepare := hprepare) (herr := herr) (n₀ := n₀)
      (stage := stage) (d₀ := d₀) (discount := discount) (childCutoff := childCutoff)
      (childCost := childCost) (ih := ih) (a := a) (Λ := Λ)
      (initialCost := initialCost) (ha := ha) (haΛ := haΛ) (hΛ := hΛ)
      (habsolute := habsolute) (hOldComplexity := hOldComplexity) (hDpos := hDpos) (hrest := hrest)
      (hOldStage := hOldStage) (f := f) (hf := hf) (hfree := hfree)
      (hscore := hscore) (hdiscount := hdiscount) (hchildCost := hchildCost) (hCost := hCost)
      (H := H) (Lmin := Lmin) (Qgood := Qgood) (hHLmin := hHLmin)
      (hHcut := hHcut) (hHcost := hHcost) (hLmin := hLmin) (hQgood := hQgood)
      (hQexp := hQexp)
      (data := data)
      (hScalar := hScalar) (hInputs := hInputs) (hPhysicalSize := hPhysicalSize)
      (hNliteral := hFloors.1) (hRankLiteral := hFloors.2)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct
attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection integerBox
  RankPreparationFamily.PreparedHeights.canonicalPaddedSamplerData
  preparedFiniteNestedSourceRequiredLog

theorem exists_preparedCanonicalInitializedRelativeSource_of_data
    {nX m s D Erest : ℕ} (prep : RankPreparationFamily (Fin nX) (Fin D) m)
    (oldPatch : PolynomialPatch (Fin nX) s (D + Erest)) (F : oldPatch.LowestLayerModel m)
    (outerDepth innerDepth e Cprimitive Cdirect extra : ℕ)
    {p pRelative Bstruct knob pPrep pLate precisionBudget : ℝ} {Rrank : ℕ}
    (hheight : prep.PreparedHeights pPrep Rrank) (hsize : prep.Sized D (m * D))
    (hms : m ≤ s) (hs : 1 ≤ s) (hnX : 0 < nX)
    (hp : 2 ≤ p) (hpPrep : 0 ≤ pPrep) (hRank : 1 ≤ Rrank)
    (hPrepLate : pPrep ≤ pLate) (hRankLate : (Rrank : ℝ) ≤ Real.exp pLate)
    (hCapLate : (preparationCoordinateCap (max m s) D (s * D) : ℝ) ≤ pLate)
    (hprimitive : 1 ≤ Cprimitive) (hknob : 0 ≤ knob)
    (hstructure :
      let M := preparationCoordinateCap s D (s * D)
      let Jalloc := modularInitialBlockCount s (nX + s * M)
      let dim := enlargedPreparedCommonSamplerDimension s M Jalloc
      p ≤ pRelative ∧ (s : ℝ) + 3 ≤ pRelative ∧
        (M : ℝ) ≤ pRelative ∧ (Jalloc : ℝ) ≤ pRelative ∧
        (dim : ℝ) ≤ pRelative ∧ allocatedUniformChartLog (M : ℝ) + 1 ≤ pRelative)
    (hBrelative : 6 * pRelative + 35 ≤ Bstruct)
    (hprecision : 3 * pRelative + 130 ≤ precisionBudget)
    (hnXp : (nX : ℝ) ≤ p)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Bstruct)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Bstruct)
    (N : Fin nX → ℕ)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ))
      (Rrank : ℝ) (prep j).space (prep j).poly)
    (hN : ∀ i, Real.exp (preparedCanonicalRelativeSourceRequired prep s outerDepth innerDepth
      e Cprimitive Cdirect extra Bstruct p knob) ≤ (N i : ℝ))
    (hSourceRank : Real.exp (preparedCanonicalRelativeSourceRequired prep s outerDepth innerDepth
      e Cprimitive Cdirect extra Bstruct p knob) ≤ (Rrank : ℝ))
    (ip : Fin D → MvPolynomial (Fin nX) ℤ) (hip : ∀ i, (ip i).totalDegree ≤ m)
    (c₀ : Fin D → ℝ) (err : VectorPolynomial (Fin nX) ℝ (Fin D → ℝ))
    (hprepare : ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
      prep.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c₀) + err)
    (herr : ∀ x ∈ integerBox N, ∀ i,
      |eval (fun z => (x z : ℝ)) err i| ≤ Real.exp (-precisionBudget))
    {n₀ stage d₀ : ℕ} {discount : ℝ} {childCutoff childCost : ℝ → ℝ}
    (ih : RelativePatchInductionRule s n₀ stage discount childCutoff childCost)
    {a Λ initialCost : ℝ}
    (ha : Real.exp (-p) ≤ a) (haΛ : a ≤ Λ) (hΛ : Λ ≤ 1)
    (habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀)
    (hOldComplexity : relativePatchComplexity oldPatch ≤ p)
    (hDpos : 0 < D) (hrest : ∀ i : Fin Erest, m < oldPatch.weight (i.natAdd D))
    (hOldStage : relativePatchDistinctWeights oldPatch ≤ stage + 1)
    (f : (Fin nX → ℤ) → ℝ)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2))
    (hscore : Real.exp (-p) ≤ relativePatchBoxScore N f a oldPatch)
    (hdiscount : discount ∈ Set.Icc (0 : ℝ) 1)
    (hchildCost : 0 ≤ childCost (pRelative + 2))
    (hCost : childCost (pRelative + 2) ≤ initialCost)
    (H Lmin Qgood : ℕ) (hHLmin : H ≤ Lmin)
    (hHcut : Real.exp (childCutoff (pRelative + 2)) ≤ (H : ℝ))
    (hHcost : (H : ℝ) ≤ Real.exp initialCost)
    (hLmin : (Lmin : ℝ) ≤ Real.exp knob)
    (hQgood : 1 ≤ Qgood) (hQexp : (Qgood : ℝ) ≤ Real.exp knob)
    (data :
      let q := max m s
      let M := preparationCoordinateCap q D (s * D)
      let Jalloc := modularInitialBlockCount q (nX + q * M)
      let G := EnlargedPreparedCommonKernel q Jalloc
      let Vars := LayerSamplerVariables G (PreparedSamplerContinuous (prep.pad q))
        (preparedSamplerTransverse (prep.pad q)) (EnlargedPreparedCommonSamplerBlock (prep.pad q) Jalloc)
      (prep.pad q).CanonicalSamplerData Vars M pLate) :
    preparedCanonicalInitializedRelativeSourceDataConclusion
      (nX := nX) (m := m) (s := s) (D := D)
      (Erest := Erest) (prep := prep) (oldPatch := oldPatch) (F := F)
      (outerDepth := outerDepth) (innerDepth := innerDepth) (e := e) (Cprimitive := Cprimitive)
      (Cdirect := Cdirect) (extra := extra) (p := p) (pRelative := pRelative)
      (Bstruct := Bstruct) (knob := knob) (pPrep := pPrep) (pLate := pLate)
      (precisionBudget := precisionBudget) (Rrank := Rrank) (hheight := hheight) (_hsize := hsize)
      (_hms := hms) (_hs := hs) (_hnX := hnX) (_hp := hp)
      (_hpPrep := hpPrep) (_hRank := hRank) (_hPrepLate := hPrepLate) (_hRankLate := hRankLate)
      (_hCapLate := hCapLate) (_hprimitive := hprimitive) (_hknob := hknob) (_hstructure := hstructure)
      (_hBrelative := hBrelative) (_hprecision := hprecision) (_hnXp := hnXp) (_hprofile := hprofile)
      (_hcutoff := hcutoff) (N := N) (_hrank := hrank) (_hN := hN)
      (_hSourceRank := hSourceRank) (ip := ip) (_hip := hip) (c₀ := c₀)
      (err := err) (_hprepare := hprepare) (_herr := herr) (n₀ := n₀)
      (stage := stage) (d₀ := d₀) (discount := discount) (childCutoff := childCutoff)
      (childCost := childCost) (_ih := ih) (a := a) (Λ := Λ)
      (initialCost := initialCost) (_ha := ha) (_haΛ := haΛ) (_hΛ := hΛ)
      (_habsolute := habsolute) (_hOldComplexity := hOldComplexity) (_hDpos := hDpos) (_hrest := hrest)
      (_hOldStage := hOldStage) (f := f) (_hf := hf) (_hfree := hfree)
      (_hscore := hscore) (_hdiscount := hdiscount) (_hchildCost := hchildCost) (_hCost := hCost)
      (H := H) (Lmin := Lmin) (Qgood := Qgood) (_hHLmin := hHLmin)
      (_hHcut := hHcut) (_hHcost := hHcost) (_hLmin := hLmin) (_hQgood := hQgood)
      (_hQexp := hQexp)
      (data := data) :=
  preparedCanonicalInitializedRelativeSourceDataProof
      (nX := nX) (m := m) (s := s) (D := D)
      (Erest := Erest) (prep := prep) (oldPatch := oldPatch) (F := F)
      (outerDepth := outerDepth) (innerDepth := innerDepth) (e := e) (Cprimitive := Cprimitive)
      (Cdirect := Cdirect) (extra := extra) (p := p) (pRelative := pRelative)
      (Bstruct := Bstruct) (knob := knob) (pPrep := pPrep) (pLate := pLate)
      (precisionBudget := precisionBudget) (Rrank := Rrank) (hheight := hheight) (hsize := hsize)
      (hms := hms) (hs := hs) (hnX := hnX) (hp := hp)
      (hpPrep := hpPrep) (hRank := hRank) (hPrepLate := hPrepLate) (hRankLate := hRankLate)
      (hCapLate := hCapLate) (hprimitive := hprimitive) (hknob := hknob) (hstructure := hstructure)
      (hBrelative := hBrelative) (hprecision := hprecision) (hnXp := hnXp) (hprofile := hprofile)
      (hcutoff := hcutoff) (N := N) (hrank := hrank) (hN := hN)
      (hSourceRank := hSourceRank) (ip := ip) (hip := hip) (c₀ := c₀)
      (err := err) (hprepare := hprepare) (herr := herr) (n₀ := n₀)
      (stage := stage) (d₀ := d₀) (discount := discount) (childCutoff := childCutoff)
      (childCost := childCost) (ih := ih) (a := a) (Λ := Λ)
      (initialCost := initialCost) (ha := ha) (haΛ := haΛ) (hΛ := hΛ)
      (habsolute := habsolute) (hOldComplexity := hOldComplexity) (hDpos := hDpos) (hrest := hrest)
      (hOldStage := hOldStage) (f := f) (hf := hf) (hfree := hfree)
      (hscore := hscore) (hdiscount := hdiscount) (hchildCost := hchildCost) (hCost := hCost)
      (H := H) (Lmin := Lmin) (Qgood := Qgood) (hHLmin := hHLmin)
      (hHcut := hHcut) (hHcost := hHcost) (hLmin := hLmin) (hQgood := hQgood)
      (hQexp := hQexp)
      (data := data)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct
attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection integerBox
  RankPreparationFamily.PreparedHeights.canonicalPaddedSamplerData

theorem exists_preparedCanonicalInitializedRelativeSource
    {nX m s D Erest : ℕ} (prep : RankPreparationFamily (Fin nX) (Fin D) m)
    (oldPatch : PolynomialPatch (Fin nX) s (D + Erest)) (F : oldPatch.LowestLayerModel m)
    (outerDepth innerDepth e Cprimitive Cdirect extra : ℕ)
    {p pRelative Bstruct knob pPrep pLate precisionBudget : ℝ} {Rrank : ℕ}
    (hheight : prep.PreparedHeights pPrep Rrank) (hsize : prep.Sized D (m * D))
    (hms : m ≤ s) (hs : 1 ≤ s) (hnX : 0 < nX)
    (hp : 2 ≤ p) (hpPrep : 0 ≤ pPrep) (hRank : 1 ≤ Rrank)
    (hPrepLate : pPrep ≤ pLate) (hRankLate : (Rrank : ℝ) ≤ Real.exp pLate)
    (hCapLate : (preparationCoordinateCap (max m s) D (s * D) : ℝ) ≤ pLate)
    (hprimitive : 1 ≤ Cprimitive) (hknob : 0 ≤ knob)
    (hstructure :
      let M := preparationCoordinateCap s D (s * D)
      let Jalloc := modularInitialBlockCount s (nX + s * M)
      let dim := enlargedPreparedCommonSamplerDimension s M Jalloc
      p ≤ pRelative ∧ (s : ℝ) + 3 ≤ pRelative ∧
        (M : ℝ) ≤ pRelative ∧ (Jalloc : ℝ) ≤ pRelative ∧
        (dim : ℝ) ≤ pRelative ∧ allocatedUniformChartLog (M : ℝ) + 1 ≤ pRelative)
    (hBrelative : 6 * pRelative + 35 ≤ Bstruct)
    (hprecision : 3 * pRelative + 130 ≤ precisionBudget)
    (hnXp : (nX : ℝ) ≤ p)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Bstruct)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Bstruct)
    (N : Fin nX → ℕ)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ))
      (Rrank : ℝ) (prep j).space (prep j).poly)
    (hN : ∀ i, Real.exp (preparedCanonicalRelativeSourceRequired prep s outerDepth innerDepth
      e Cprimitive Cdirect extra Bstruct p knob) ≤ (N i : ℝ))
    (hSourceRank : Real.exp (preparedCanonicalRelativeSourceRequired prep s outerDepth innerDepth
      e Cprimitive Cdirect extra Bstruct p knob) ≤ (Rrank : ℝ))
    (ip : Fin D → MvPolynomial (Fin nX) ℤ) (hip : ∀ i, (ip i).totalDegree ≤ m)
    (c₀ : Fin D → ℝ) (err : VectorPolynomial (Fin nX) ℝ (Fin D → ℝ))
    (hprepare : ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
      prep.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c₀) + err)
    (herr : ∀ x ∈ integerBox N, ∀ i,
      |eval (fun z => (x z : ℝ)) err i| ≤ Real.exp (-precisionBudget))
    {n₀ stage d₀ : ℕ} {discount : ℝ} {childCutoff childCost : ℝ → ℝ}
    (ih : RelativePatchInductionRule s n₀ stage discount childCutoff childCost)
    {a Λ initialCost : ℝ}
    (ha : Real.exp (-p) ≤ a) (haΛ : a ≤ Λ) (hΛ : Λ ≤ 1)
    (habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀)
    (hOldComplexity : relativePatchComplexity oldPatch ≤ p)
    (hDpos : 0 < D) (hrest : ∀ i : Fin Erest, m < oldPatch.weight (i.natAdd D))
    (hOldStage : relativePatchDistinctWeights oldPatch ≤ stage + 1)
    (f : (Fin nX → ℤ) → ℝ)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2))
    (hscore : Real.exp (-p) ≤ relativePatchBoxScore N f a oldPatch)
    (hdiscount : discount ∈ Set.Icc (0 : ℝ) 1)
    (hchildCost : 0 ≤ childCost (pRelative + 2))
    (hCost : childCost (pRelative + 2) ≤ initialCost)
    (H Lmin Qgood : ℕ) (hHLmin : H ≤ Lmin)
    (hHcut : Real.exp (childCutoff (pRelative + 2)) ≤ (H : ℝ))
    (hHcost : (H : ℝ) ≤ Real.exp initialCost)
    (hLmin : (Lmin : ℝ) ≤ Real.exp knob)
    (hQgood : 1 ≤ Qgood) (hQexp : (Qgood : ℝ) ≤ Real.exp knob) :
    preparedCanonicalInitializedRelativeSourceConclusion
      (nX := nX) (m := m) (s := s) (D := D)
      (Erest := Erest) (prep := prep) (oldPatch := oldPatch) (F := F)
      (outerDepth := outerDepth) (innerDepth := innerDepth) (e := e) (Cprimitive := Cprimitive)
      (Cdirect := Cdirect) (extra := extra) (p := p) (pRelative := pRelative)
      (Bstruct := Bstruct) (knob := knob) (pPrep := pPrep) (pLate := pLate)
      (precisionBudget := precisionBudget) (Rrank := Rrank) (hheight := hheight) (hsize := hsize)
      (hms := hms) (_hs := hs) (_hnX := hnX) (_hp := hp)
      (hpPrep := hpPrep) (hRank := hRank) (hPrepLate := hPrepLate) (hRankLate := hRankLate)
      (hCapLate := hCapLate) (_hprimitive := hprimitive) (_hknob := hknob) (_hstructure := hstructure)
      (_hBrelative := hBrelative) (_hprecision := hprecision) (_hnXp := hnXp) (_hprofile := hprofile)
      (_hcutoff := hcutoff) (N := N) (_hrank := hrank) (_hN := hN)
      (_hSourceRank := hSourceRank) (ip := ip) (_hip := hip) (c₀ := c₀)
      (err := err) (_hprepare := hprepare) (_herr := herr) (n₀ := n₀)
      (stage := stage) (d₀ := d₀) (discount := discount) (childCutoff := childCutoff)
      (childCost := childCost) (_ih := ih) (a := a) (Λ := Λ)
      (initialCost := initialCost) (_ha := ha) (_haΛ := haΛ) (_hΛ := hΛ)
      (_habsolute := habsolute) (_hOldComplexity := hOldComplexity) (_hDpos := hDpos) (_hrest := hrest)
      (_hOldStage := hOldStage) (f := f) (_hf := hf) (_hfree := hfree)
      (_hscore := hscore) (_hdiscount := hdiscount) (_hchildCost := hchildCost) (_hCost := hCost)
      (H := H) (Lmin := Lmin) (Qgood := Qgood) (_hHLmin := hHLmin)
      (_hHcut := hHcut) (_hHcost := hHcost) (_hLmin := hLmin) (_hQgood := hQgood)
      (_hQexp := hQexp) := by
  let q := max m s
  let M := preparationCoordinateCap q D (s * D)
  let Jalloc := modularInitialBlockCount q (nX + q * M)
  let G := EnlargedPreparedCommonKernel q Jalloc
  let Vars := LayerSamplerVariables G (PreparedSamplerContinuous (prep.pad q))
    (preparedSamplerTransverse (prep.pad q)) (EnlargedPreparedCommonSamplerBlock (prep.pad q) Jalloc)
  let data := hheight.canonicalPaddedSamplerData prep Vars (Nat.le_max_left m s)
    hpPrep hRank hPrepLate hRankLate hsize (Nat.mul_le_mul_right D hms) hCapLate
  exact exists_preparedCanonicalInitializedRelativeSource_of_data
      (nX := nX) (m := m) (s := s) (D := D)
      (Erest := Erest) (prep := prep) (oldPatch := oldPatch) (F := F)
      (outerDepth := outerDepth) (innerDepth := innerDepth) (e := e) (Cprimitive := Cprimitive)
      (Cdirect := Cdirect) (extra := extra) (p := p) (pRelative := pRelative)
      (Bstruct := Bstruct) (knob := knob) (pPrep := pPrep) (pLate := pLate)
      (precisionBudget := precisionBudget) (Rrank := Rrank) (hheight := hheight) (hsize := hsize)
      (hms := hms) (hs := hs) (hnX := hnX) (hp := hp)
      (hpPrep := hpPrep) (hRank := hRank) (hPrepLate := hPrepLate) (hRankLate := hRankLate)
      (hCapLate := hCapLate) (hprimitive := hprimitive) (hknob := hknob) (hstructure := hstructure)
      (hBrelative := hBrelative) (hprecision := hprecision) (hnXp := hnXp) (hprofile := hprofile)
      (hcutoff := hcutoff) (N := N) (hrank := hrank) (hN := hN)
      (hSourceRank := hSourceRank) (ip := ip) (hip := hip) (c₀ := c₀)
      (err := err) (hprepare := hprepare) (herr := herr) (n₀ := n₀)
      (stage := stage) (d₀ := d₀) (discount := discount) (childCutoff := childCutoff)
      (childCost := childCost) (ih := ih) (a := a) (Λ := Λ)
      (initialCost := initialCost) (ha := ha) (haΛ := haΛ) (hΛ := hΛ)
      (habsolute := habsolute) (hOldComplexity := hOldComplexity) (hDpos := hDpos) (hrest := hrest)
      (hOldStage := hOldStage) (f := f) (hf := hf) (hfree := hfree)
      (hscore := hscore) (hdiscount := hdiscount) (hchildCost := hchildCost) (hCost := hCost)
      (H := H) (Lmin := Lmin) (Qgood := Qgood) (hHLmin := hHLmin)
      (hHcut := hHcut) (hHcost := hHcost) (hLmin := hLmin) (hQgood := hQgood)
      (hQexp := hQexp)
      (data := data)

end Erdos3.VectorPolynomial

end

end OAI
