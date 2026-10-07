import OAI.Combinatorics.Progressions.Estimates.PreparedCanonicalInitializedRelativeSource
import OAI.Combinatorics.Progressions.Estimates.PreparedRelativePositiveNativeRuleCanonical
import OAI.Combinatorics.Progressions.Estimates.PreparedSourceGeometryNormalizedPatchConclusion
import OAI.Combinatorics.Progressions.Sampling.PreparedRelativePositiveForecastSource

namespace OAI

section

namespace Erdos3.RankPreparationFamily

open Module Submodule VectorPolynomial

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

theorem PreparedHeights.euclideanJetLayers_compact
    {p : ℝ} {R : ℕ} (hL : L.PreparedHeights p R)
    (hp : 0 ≤ p) (hR : 1 ≤ R) (O : Fin m → Type*) :
    CompactSpace (EuclideanJetLayers (fun j => (L j).space) O) := by
  let : ∀ j, CompactSpace (euclideanSubspace (L j).space ⧸
      (latticeSection (standardEuclideanLattice (L j).Coord)
        (euclideanSubspace (L j).space)).toAddSubgroup) :=
    hL.euclideanLayerTorus_compact L hp hR
  dsimp only [EuclideanJetLayers]
  infer_instance

end Erdos3.RankPreparationFamily

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

noncomputable def preparedFiniteNestedSourceLiteralNative
    (m cutoff A Cdirect outerDepth innerDepth : ℕ) (constants : ℕ → ℕ)
    (G : Type) [Fintype G] (count nX : ℕ)
    (Bstruct pnum Qstride gainLog stageLog Plate : ℝ)
    (k : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff) : ℝ :=
  let K := PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff
  let degree : K → ℕ := preparedFiniteNestedForwardAllDegreeDegree
  let Pdetect := preparedFiniteForwardDetectorPolynomial cutoff
  let Cdetect := fun k : K => sampledSupportedSlicedDetectionConstant (degree k) Pdetect
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
  let Pmaster := fun k : K => preparedFiniteScheduleLocalMaster Bstruct D pRadius Qstride
    (Pphysical k) (sourceU k) (modelLog k) (Prho k) (target k) (detectionGain k)
  (preparedModularGeneralDetectorResources
    (preparedModularGeneralDetectorConstants m (degree k))
    (degree k + 1) (Pmaster k) Plate).nativeBudget

theorem preparedFiniteNestedSourceLiteralNative_eq
    (m cutoff A Cdirect outerDepth innerDepth : ℕ) (constants : ℕ → ℕ)
    (G : Type) [Fintype G] (count nX : ℕ)
    (Bstruct pnum Qstride gainLog stageLog Plate : ℝ)
    (k : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff) :
    preparedFiniteNestedSourceLiteralNative m cutoff A Cdirect outerDepth innerDepth constants
      G count nX Bstruct pnum Qstride gainLog stageLog Plate k =
    preparedFiniteNestedSourceNative m G count nX (preparedFiniteForwardDetectorPolynomial cutoff)
      A Cdirect constants Bstruct pnum Qstride gainLog stageLog Plate k := by
  rfl

theorem preparedFiniteNestedSourceNative_literal_eq
    (m cutoff A Cdirect outerDepth innerDepth : ℕ) (constants : ℕ → ℕ)
    (G : Type) [Fintype G] (count nX : ℕ)
    (Bstruct pnum Qstride gainLog stageLog Plate : ℝ)
    (k : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff) :
  let K := PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff
  let degree : K → ℕ := preparedFiniteNestedForwardAllDegreeDegree
  let Pdetect := preparedFiniteForwardDetectorPolynomial cutoff
  let Cdetect := fun k : K => sampledSupportedSlicedDetectionConstant (degree k) Pdetect
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
  let Pmaster := fun k : K => preparedFiniteScheduleLocalMaster Bstruct D pRadius Qstride
    (Pphysical k) (sourceU k) (modelLog k) (Prho k) (target k) (detectionGain k)
  (preparedModularGeneralDetectorResources
    (preparedModularGeneralDetectorConstants m (degree k))
    (degree k + 1) (Pmaster k) Plate).nativeBudget =
    preparedFiniteNestedSourceNative m G count nX (preparedFiniteForwardDetectorPolynomial cutoff)
      A Cdirect constants Bstruct pnum Qstride gainLog stageLog Plate k := by
  rfl

theorem preparedFiniteNestedSourceNative_late_eq
    (m cutoff A Cdirect outerDepth innerDepth : ℕ) (constants : ℕ → ℕ)
    (G : Type) [Fintype G] (count nX : ℕ)
    (Bstruct pnum Qstride gainLog stageLog Plate Plate' : ℝ)
    (k : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff) :
    preparedFiniteNestedSourceNative m G count nX (preparedFiniteForwardDetectorPolynomial cutoff)
      A Cdirect constants Bstruct pnum Qstride gainLog stageLog Plate k =
    preparedFiniteNestedSourceNative m G count nX (preparedFiniteForwardDetectorPolynomial cutoff)
      A Cdirect constants Bstruct pnum Qstride gainLog stageLog Plate' k := by
  exact preparedModularGeneralDetectorResources_nativeBudget_eq _ _ _ Plate Plate'

theorem preparedFiniteNestedSourceNative_literal_eq_late
    (m cutoff A Cdirect outerDepth innerDepth : ℕ) (constants : ℕ → ℕ)
    (G : Type) [Fintype G] (count nX : ℕ)
    (Bstruct pnum Qstride gainLog stageLog Plate Plate' : ℝ)
    (k : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff) :
  let K := PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff
  let degree : K → ℕ := preparedFiniteNestedForwardAllDegreeDegree
  let Pdetect := preparedFiniteForwardDetectorPolynomial cutoff
  let Cdetect := fun k : K => sampledSupportedSlicedDetectionConstant (degree k) Pdetect
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
  let Pmaster := fun k : K => preparedFiniteScheduleLocalMaster Bstruct D pRadius Qstride
    (Pphysical k) (sourceU k) (modelLog k) (Prho k) (target k) (detectionGain k)
  (preparedModularGeneralDetectorResources
    (preparedModularGeneralDetectorConstants m (degree k))
    (degree k + 1) (Pmaster k) Plate).nativeBudget =
    preparedFiniteNestedSourceNative m G count nX (preparedFiniteForwardDetectorPolynomial cutoff)
      A Cdirect constants Bstruct pnum Qstride gainLog stageLog Plate' k := by
  exact preparedModularGeneralDetectorResources_nativeBudget_eq _ _ _ Plate Plate'

theorem preparedFiniteNestedSourceNative_literal_eq_zero
    (m cutoff A Cdirect outerDepth innerDepth : ℕ) (constants : ℕ → ℕ)
    (G : Type) [Fintype G] (count nX : ℕ)
    (Bstruct pnum Qstride gainLog stageLog Plate : ℝ)
    (k : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff) :
  let K := PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff
  let degree : K → ℕ := preparedFiniteNestedForwardAllDegreeDegree
  let Pdetect := preparedFiniteForwardDetectorPolynomial cutoff
  let Cdetect := fun k : K => sampledSupportedSlicedDetectionConstant (degree k) Pdetect
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
  let Pmaster := fun k : K => preparedFiniteScheduleLocalMaster Bstruct D pRadius Qstride
    (Pphysical k) (sourceU k) (modelLog k) (Prho k) (target k) (detectionGain k)
  (preparedModularGeneralDetectorResources
    (preparedModularGeneralDetectorConstants m (degree k))
    (degree k + 1) (Pmaster k) Plate).nativeBudget =
    preparedFiniteNestedSourceNative m G count nX (preparedFiniteForwardDetectorPolynomial cutoff)
      A Cdirect constants Bstruct pnum Qstride gainLog stageLog 0 k := by
  exact preparedModularGeneralDetectorResources_nativeBudget_eq _ _ _ Plate 0

end Erdos3.VectorPolynomial

end

section

namespace Erdos3
open VectorPolynomial Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal TensorProduct
attribute [local irreducible] preparedFiniteNestedSourceRequiredLog
  AllocatedExternalCandidateSampler.NativeDetection integerBox
  AllocatedExternalCandidateSampler.DegreeGlobalizationAt
  RankPreparationFamily.PreparedHeights.canonicalPaddedSamplerData

theorem exists_preparedRelativePatchPowerPassage
    (s n₀ stage childExponent : ℕ) (discount : ℝ)
    (hs : 1 ≤ s) (_hchildExponent : 2 ≤ childExponent)
    (hdiscount : 0 < discount) (hdiscountOne : discount ≤ 1)
    (ih : RelativePatchPowerInductionRule s n₀ stage discount childExponent) :
    ∃ requiredPower precisionPower : ℕ,
      ∀ preparationPower : ℕ, 2 ≤ preparationPower →
        ∃ passagePower : ℕ, 2 ≤ passagePower ∧
          PreparedRelativePatchPowerPassage s n₀ stage discount
            requiredPower precisionPower preparationPower passagePower := by
  classical
  obtain ⟨relativePower, hRelativePower, hStructure⟩ :=
    exists_preparedRelative_structural_input_power s
  obtain ⟨candidateBasePower, precisionPower, hCandidateBasePower, hPrecisionPower, hCandidate⟩ :=
    exists_preparedRelative_candidate_input_powers s relativePower childExponent
      (exists_relative_finite_returned_fiber_normalization.{0,0} s).choose
      (allocatedNormalizedShearObservableExponent s)
  obtain ⟨baseMin, hBaseMin, hUniversalConstants⟩ :=
    exists_preparedScalarStructuralBasePower s
  let basePower := max candidateBasePower baseMin
  have hBasePower : 2 ≤ basePower := hCandidateBasePower.trans (le_max_left _ _)
  let inputPower := preparedRelativePositiveInputExponent s
  let earlyPower := preparedRelativePositiveEarlyExponent s
  let extra := preparedRelativePositiveExtra s
  let primitive := preparedCommonRadiusPrimitiveExponent s
  let entropy := candidateNestedDegreeNetBound s 0
  let constants := AllocatedExternalCandidateSampler.degreeSourceCountConstants
  let outerDepth := 2 * s + 2
  let innerDepth := s + 1
  obtain ⟨requiredPower, hRequiredPower, hRequired⟩ :=
    exists_preparedFiniteNestedCanonicalRequired_power_budget_of_inputPower
      s outerDepth innerDepth s entropy primitive 2 extra basePower inputPower
      constants (by dsimp only [innerDepth]; omega) (by omega)
  refine ⟨requiredPower, precisionPower, ?_⟩
  intro preparationPower hPreparationPower
  obtain ⟨extractionPower, hExtractionPower, hExtraction⟩ :=
    exists_preparedRelativeFinalExtraction_power s s basePower inputPower
      preparationPower requiredPower discount
  let passagePower := max requiredPower extractionPower
  refine ⟨passagePower, hRequiredPower.trans (le_max_left _ _), ?_⟩
  intro p a Λ d₀ hp ha haΛ hΛ habsolute nX hnX hX N hN f hf hfree
    D E m hD hm hms oldPatch F hrest hcomplexity hStage hscore
    L hsize hheight hRankSum hCoord hrank ip c err hip herrDegree hprepare herr
  have hp0 : 0 ≤ p := by linarith only [hp]
  have hDreal : (D : ℝ) ≤ p := by
    have hd := (relativePatchComplexity_rank_le oldPatch).trans hcomplexity
    simp only [Nat.cast_add] at hd
    linarith only [hd, Nat.cast_nonneg (α := ℝ) E]
  have hq : max m s = s := max_eq_right hms
  let M := preparationCoordinateCap (max m s) D (s * D)
  let Jalloc := modularInitialBlockCount (max m s) (nX + max m s * M)
  let dim := enlargedPreparedCommonSamplerDimension (max m s) M Jalloc
  let G := EnlargedPreparedCommonKernel (max m s) Jalloc
  let pRelative := (p + 2) ^ relativePower
  let childCost := (pRelative + 4) ^ childExponent
  let Bstruct := (p + 2) ^ basePower
  let Vars := LayerSamplerVariables G (PreparedSamplerContinuous (L.pad (max m s)))
    (preparedSamplerTransverse (L.pad (max m s)))
    (EnlargedPreparedCommonSamplerBlock (L.pad (max m s)) Jalloc)
  let vars := Fintype.card Vars
  have hStructOriginal := hStructure hp D nX hDreal hX
  have hStruct : p ≤ pRelative ∧ (s : ℝ) + 3 ≤ pRelative ∧
    (M : ℝ) ≤ pRelative ∧ (Jalloc : ℝ) ≤ pRelative ∧
    (dim : ℝ) ≤ pRelative ∧ allocatedUniformChartLog (M : ℝ) + 1 ≤ pRelative := by
    simpa only [M, Jalloc, dim, hq] using hStructOriginal
  have hOriginalCoord : ∀ j, Fintype.card (L j).Coord ≤ M := by
    intro j
    simpa only [M, hq] using
      (hCoord j).trans (preparationCoordinateCap_mono hms (Nat.mul_le_mul_right D hms))
  have hvars : (vars : ℝ) ≤ pRelative :=
    (preparedFiniteNestedSource_counts L nX M s hOriginalCoord hStruct.2.2.2.2.1).2.2.1
  have hCandidateBase : (p + 2) ^ candidateBasePower ≤ Bstruct :=
    pow_le_pow_right₀ (by linarith only [hp]) (le_max_left _ _)
  obtain ⟨hNorm₀, hRegularity₀, hMass₀, hChartCost₀, hEarly₀, hPrecision⟩ :=
    hCandidate hp0 (Nat.cast_nonneg (α := ℝ) vars) hvars
  have hNorm := hNorm₀.trans hCandidateBase
  have hRegularity := hRegularity₀.trans hCandidateBase
  have hMass := hMass₀.trans hCandidateBase
  have hChartCost := hChartCost₀.trans hCandidateBase
  have hEarly := hEarly₀.trans hCandidateBase
  obtain ⟨_, hProfile, hCutoff, _⟩ :=
    hUniversalConstants basePower (le_max_right _ _) p hp
  have hInput := preparedRelativeInitializer_scalarInputs oldPatch L hp hms hCoord hStructOriginal
    hPrecision hcomplexity ha habsolute
  have hB : 0 ≤ Bstruct := by dsimp only [Bstruct]; positivity
  have hBtwo : 2 ≤ Bstruct := by
    change 6 * pRelative + 35 ≤ Bstruct at hEarly
    linarith only [hEarly, hStruct.1, hp]
  have hpB : p ≤ Bstruct := by
    linarith only [hEarly, hStruct.1, hp]
  have hM : (M : ℝ) ≤ Bstruct := by
    linarith only [hEarly, hStruct.2.2.1, hStruct.1, hp]
  have hnum : (dim : ℝ) ≤ Bstruct := by
    linarith only [hEarly, hStruct.2.2.2.2.1, hStruct.1, hp]
  have hVars : (vars : ℝ) ≤ Bstruct := hvars.trans (by
    linarith only [hEarly, hStruct.1, hp])
  have hPadCoord := preparedRelativeInitializer_padded_coordinate_card_le L hms hCoord
  let Aexp := preparedFiniteNestedSourceExponent (max m s) s entropy primitive 2 extra
  have hAeq : Aexp = preparedRelativePositiveSourceExponent s := by
    dsimp only [Aexp]
    rw [hq]
    rfl
  have hA := preparedRelativePositiveSourceExponent_bounds s
  rw [← hAeq] at hA
  let t := preparedRelativeEndpointInputScale s earlyPower Bstruct
  let T := preparedRelativeEndpointGeometryScale s t
  let K := preparedRelativeEndpointUniformKnob s t
  have hKPower : K ≤ (Bstruct + 2) ^ inputPower :=
    (preparedRelativePositiveInputExponent_spec s).2 hB
  have hFinal := preparedRelativeFinalEnvelope_bounds s basePower inputPower preparationPower
    requiredPower discount hp0 hKPower
  have hExtractionBound := hExtraction p hp0
  have hExtractionFinal := preparedRelativeFinalExtraction_side_floor N hp0
    (Nat.le_max_right requiredPower extractionPower) hExtractionBound hN

  obtain ⟨hG, _, hVariables, hLayers⟩ := preparedFiniteNestedSource_counts L nX M s
    hOriginalCoord hnum
  have hEarlyData :=
    (exists_preparedFiniteNestedCanonicalEarlyPrimitive_budget s outerDepth innerDepth s
      entropy primitive 2 extra constants).choose_spec.2 m hms G vars nX M
      hB ⟨Nat.cast_nonneg dim, hnum⟩ ⟨le_rfl, hB⟩ ⟨hp0, hpB⟩ ⟨le_rfl, hB⟩
      hVars (hX.trans hpB) hG hM
  have hAcanonical : preparedFiniteNestedSourceExponent (max m s) s entropy primitive 2 extra = Aexp := rfl
  let seed := candidateNestedForwardSeed Aexp constants innerDepth outerDepth Bstruct
  let endpointParameter := preparedFiniteForwardParameter Aexp constants innerDepth seed
  let cost := endpointParameter + 1
  let u := preparedFiniteForwardModelPrecision Aexp constants innerDepth seed p 0
  let modelLog := preparedFiniteForwardWork Aexp constants innerDepth seed
  let anchor := preparedFiniteNestedForwardAllDegreeAnchor outerDepth innerDepth s
  let native := preparedFiniteNestedSourceNative (max m s) G vars nX
    (preparedFiniteForwardDetectorPolynomial s) Aexp 2 constants Bstruct dim 0 p 0 0 anchor
  let pRadius := allocatedCommonProductRadiusLog (max m s) Bstruct Bstruct
  let chartLog := allocatedUniformChartLog (M : ℝ)
  have hData : pRadius ∈ Set.Icc 0 ((Bstruct + 2) ^ earlyPower) ∧
      allocatedComparisonDimension s (dim : ℝ) ∈ Set.Icc 0 ((Bstruct + 2) ^ earlyPower) ∧
      ((nX + s * M : ℕ) : ℝ) ∈ Set.Icc 0 ((Bstruct + 2) ^ earlyPower) ∧
      endpointParameter ∈ Set.Icc 0 ((Bstruct + 2) ^ earlyPower) ∧
      u ∈ Set.Icc 0 ((Bstruct + 2) ^ earlyPower) ∧
      modelLog ∈ Set.Icc 0 ((Bstruct + 2) ^ earlyPower) ∧
      native ∈ Set.Icc 0 ((Bstruct + 2) ^ earlyPower) := by
    obtain ⟨hr, hd, hmod, hend, hslots⟩ := hEarlyData
    obtain ⟨_, _, hu, hw, hn, _⟩ := hslots anchor
    have hEarlyExponent :
        (exists_preparedFiniteNestedCanonicalEarlyPrimitive_budget s outerDepth innerDepth s
          entropy primitive 2 extra constants).choose = earlyPower := rfl
    rw [hEarlyExponent] at hr hd hmod hend hu hw hn
    exact ⟨hr,
      by simpa only [hq] using hd, by simpa only [hq] using hmod,
      by simpa only [hAcanonical] using hend,
      by simpa only [hAcanonical, anchor, preparedFiniteNestedForwardAllDegreeAnchor_stage,
        preparedFiniteNestedForwardAllDegreeAnchor_seed] using hu,
      by simpa only [hAcanonical, anchor, preparedFiniteNestedForwardAllDegreeAnchor_stage,
        preparedFiniteNestedForwardAllDegreeAnchor_seed] using hw,
      by simpa only [hAcanonical] using hn⟩
  have hBase := preparedRelativeEndpointInputBase_bounds earlyPower hB
  have hPowBase : (Bstruct + 2) ^ earlyPower ≤ preparedRelativeEndpointInputBase earlyPower Bstruct := by
    linarith only [hBase.2.2]
  have liftEarly {z : ℝ} (hz : z ∈ Set.Icc 0 ((Bstruct + 2) ^ earlyPower)) :
      z ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower Bstruct) :=
    ⟨hz.1, hz.2.trans hPowBase⟩
  have liftBase {z : ℝ} (hz : z ∈ Set.Icc 0 Bstruct) :
      z ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower Bstruct) :=
    ⟨hz.1, hz.2.trans hBase.2.1⟩
  have hChild0 : 0 ≤ childCost := by dsimp only [childCost, pRelative]; positivity
  have hChildB : childCost ≤ Bstruct := by linarith only [hChartCost]
  have hChartLog0 : 0 ≤ chartLog := by dsimp only [chartLog, allocatedUniformChartLog]; positivity
  have hChartLogB : chartLog ≤ Bstruct := by
    have hchart : chartLog + 1 ≤ pRelative := hStruct.2.2.2.2.2
    linarith only [hchart, hEarly, hStruct.1, hp]
  have hCostBase : cost ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower Bstruct) :=
    ⟨by dsimp only [cost]; linarith only [hData.2.2.2.1.1],
      (add_le_add hData.2.2.2.1.2 le_rfl).trans hBase.2.2⟩
  have hSeed0 : 0 ≤ seed := candidateNestedForwardSeed_nonneg Aexp constants innerDepth outerDepth hB
  have hSeedBase : seed ≤ preparedRelativeEndpointInputBase earlyPower Bstruct :=
    (le_preparedFiniteForwardParameter Aexp constants innerDepth hSeed0).trans
      (hData.2.2.2.1.2.trans hPowBase)
  have hNumData := preparedRelativeEndpoint_numerical_bounds s earlyPower M nX Jalloc hB
    (by simpa only [dim, hq] using hData.2.1.2.trans hPowBase)
    (hData.2.2.1.2.trans hPowBase)
    (liftBase ⟨hB, le_rfl⟩) hCostBase (liftEarly hData.1) (liftBase ⟨hp0, hpB⟩)
    (liftBase ⟨le_rfl, hB⟩) (liftBase ⟨hChartLog0, hChartLogB⟩)
    (liftBase ⟨hChartLog0, hChartLogB⟩) (liftBase ⟨hChild0, hChildB⟩)
    (liftEarly hData.2.2.2.2.1) (liftEarly hData.2.2.2.2.2.1)
    (liftEarly hData.2.2.2.2.2.2) hSeedBase
  let Eearly := 2 * u + 4 * modelLog + 12
  let nativeEarly := preparedConcreteSlicedForecastNativeLog s M nX Jalloc
    Bstruct cost pRadius p 0 chartLog chartLog childCost Eearly
  let massEarly := preparedConcreteSlicedForecastMassLog s M nX Jalloc
    Bstruct cost pRadius p 0 chartLog childCost Eearly
  let Ptest := preparedRelativeEndpointTestLog native nativeEarly
  let Ecompare := preparedRelativeEndpointComparisonLog native nativeEarly massEarly u modelLog cost
  let floorLog := (T + 10) ^ (2 * s + 20)
  let Lmin := preparedRelativeEndpointMinimumScale seed 0 childCost cost floorLog
  let Qgood := preparedRelativeEndpointGoodCutoff Ptest
  obtain ⟨hT, htT, hTK, hK, hTest, hCompare, hnEarly, hmEarly, hnLate, hmLate,
    hModelRequired, hNativeAmbient, hMin, hGood, hSigma, hCoarse, hAmbient, hFloor⟩ := hNumData
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hKbudget : K ∈ Set.Icc 0 ((Bstruct + 2) ^ inputPower) := ⟨hK0, hKPower⟩
  have hRreq := hRequired hp m hms G M vars nX ⟨Nat.cast_nonneg dim, hnum⟩
    ⟨le_rfl, hB⟩ ⟨hp0, hpB⟩ ⟨le_rfl, hB⟩ hM hVars (hX.trans hpB) hG
    hKbudget hKbudget hKbudget hKbudget hKbudget
  have hScale := preparedRelativeEndpointMinimumScale_bounds hSeed0 0 childCost cost floorLog
  have hGoodBounds := preparedRelativeEndpointGoodCutoff_bounds hTest.1
  have hLmin : (Lmin : ℝ) ≤ Real.exp K := hScale.2.2.1.trans (Real.exp_le_exp.mpr hMin)
  have hQgood : 1 ≤ Qgood := hGoodBounds.2.1
  have hQexp : (Qgood : ℝ) ≤ Real.exp K :=
    hGoodBounds.2.2.2.trans (Real.exp_le_exp.mpr hGood)

  let Rreq := preparedCanonicalRelativeSourceRequired L s outerDepth innerDepth
    entropy primitive 2 extra Bstruct p K
  have hRreqCanonical : Rreq ≤ (p + 2) ^ requiredPower := hRreq
  have hKnobRequired : K ≤ Rreq := preparedCanonicalRelativeSourceRequired_endpoint_le
    L s outerDepth innerDepth entropy primitive 2 extra K hB ⟨hp0, hpB⟩
  let pLate := preparedRelativeLateHeight Bstruct p preparationPower requiredPower
  obtain ⟨hpLate, hPadHeight, hPadSize, hLateCoord, hPadRankSum,
    hRoundedRank, hRankLate, hSourceRank, hSourceN, hPadSamplingRank,
    hPadDegree, hPadMem⟩ := preparedRelative_padded_input L (Nat.le_max_left m s)
      preparationPower requiredPower passagePower hp0 hB
      (by simpa only [M, hq] using hM) hheight hsize hRankSum
      N hrank hRreqCanonical (Nat.le_max_left _ _) hN
  have hKnobN : ∀ i, Real.exp K ≤ (N i : ℝ) := fun i =>
    (Real.exp_le_exp.mpr hKnobRequired).trans (hSourceN i)
  have hKnobRank : Real.exp K ≤ (preparedRoundedRank p requiredPower : ℝ) :=
    (Real.exp_le_exp.mpr hKnobRequired).trans hSourceRank
  have hCoordCanonical : ∀ j, Fintype.card (L.pad (max m s) j).Coord ≤ M :=
    fun j => (preparationCoordinateCap_bounds hPadSize (Nat.mul_le_mul_right D hms) j).1
  have hPrepLate : (p + 2) ^ preparationPower ≤ pLate :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hCapLate : (preparationCoordinateCap (max m s) D (s * D) : ℝ) ≤ pLate := by
    exact hM.trans (le_max_left _ _)
  let H := preparedSlicedForecastChildSize childCost
  have hHfloor : H ≤ Lmin := hScale.2.2.2.2.2.1
  have hHcut : Real.exp ((pRelative + 2 + 2) ^ childExponent) ≤ (H : ℝ) := by
    convert preparedSlicedForecastChildSize_lower childCost using 1
    dsimp only [childCost]
    congr 2
    ring
  have hHcost : (H : ℝ) ≤ Real.exp (childCost + 1) :=
    preparedSlicedForecastChildSize_upper hChild0

  have hEndpointDimensions := preparedNestedEndpointDimension_bounds s s le_rfl
    Aexp constants innerDepth outerDepth innerDepth hA.2.2.2.1
    (by dsimp only [outerDepth]; omega) hB
    (show (enlargedPreparedCommonSamplerDimension s M Jalloc : ℝ) ∈ Set.Icc 0 Bstruct from
      ⟨Nat.cast_nonneg _, by simpa only [dim, hq] using hnum⟩)
    nX M (hX.trans hpB) hM
  have hCap := preparedRelativeEndpointForecastCap_le_work s s Aexp le_rfl hA.2.2.1
    constants innerDepth outerDepth innerDepth M nX Jalloc hB
    ⟨hp0, hpB⟩ ⟨hChartLog0, hChartLogB⟩ ⟨hChild0, hChildB⟩
    hEndpointDimensions.1 hEndpointDimensions.2
  let Cslice := preparedFiniteNestedSourceSliceExponent (max m s) s primitive
  have hCsliceCanonical : preparedFiniteNestedSourceSliceExponent (max m s) s primitive = Cslice := rfl
  let sliceLog := (endpointParameter + Cslice) ^ Cslice
  have hBseed : Bstruct ≤ seed :=
    le_candidateNestedForwardSeed Aexp constants innerDepth outerDepth hA.1 hB
  obtain ⟨hModel0, hU0, hCost0, hSlice0, hCostSlice, hSliceWork, hChartSlice, hU⟩ :=
    preparedFiniteForward_endpoint_scalar_bounds Aexp Cslice constants innerDepth vars
      hA.1 (preparedFiniteNestedSourceSliceExponent_bounds (max m s) s primitive).1
      (by simpa only [Cslice, hq] using hA.2.2.2.2)
      hSeed0 hp0 (le_refl 0) (hVars.trans hBseed)
  have hSetupBounds := preparedRelativeEndpointInputScale_setup_bounds s earlyPower M nX Jalloc hB
    (by simpa only [dim, hq] using hData.2.1.2.trans hPowBase)
    (hData.2.2.1.2.trans hPowBase) (liftBase ⟨hB, le_rfl⟩) hCostBase
    (liftEarly hData.1) (liftBase ⟨hp0, hpB⟩) (liftBase ⟨le_rfl, hB⟩)
    (liftBase ⟨hChartLog0, hChartLogB⟩) (liftBase ⟨hChartLog0, hChartLogB⟩)
    (liftBase ⟨hChild0, hChildB⟩)
  obtain ⟨hSpatialLog, hBadLog, hPresLog, hTauLog, hRadiusLog, hDimensionLog,
    hPrimitiveCap, hLayerLog, hModularLog, hXLog, hScaleLog, hJacobianLog,
    hForwardLog, hChildLog⟩ := hSetupBounds
  have hInputBaseScale : preparedRelativeEndpointInputBase earlyPower Bstruct ≤ t :=
    (preparedRelativeEndpointInputScale_bounds s earlyPower hB).2.1
  have hModelK : modelLog ≤ K :=
    (liftEarly hData.2.2.2.2.2.1).2.trans (hInputBaseScale.trans (htT.trans hTK))
  have hCostK : cost ≤ K := hCostBase.2.trans (hInputBaseScale.trans (htT.trans hTK))
  have hFinalRequirements := preparedRelativeFinalEnvelope_ready_requirements s s D
    (nX + s * M) vars basePower inputPower preparationPower requiredPower discount
    hp0 hKPower hDreal (hModularLog.trans (htT.trans hTK)) hChildB hpLate le_rfl
    (by simpa only [add_assoc, show (2 : ℝ) + 2 = 4 by norm_num] using hNorm)
    (hCap.trans hModelK) (hnEarly.2.trans hTK) hCostK
  let lam := (1 - discount) ^ (stage + 1) * Λ
  have hlam : lam ∈ Set.Icc (0 : ℝ) 1 := by
    have hΛzero : 0 ≤ Λ := ((Real.exp_pos (-p)).le.trans ha).trans haΛ
    have hbasezero : 0 ≤ 1 - discount := sub_nonneg.mpr hdiscountOne
    have hbaseone : 1 - discount ≤ 1 := by linarith only [hdiscount]
    exact ⟨mul_nonneg (pow_nonneg hbasezero _) hΛzero,
      (mul_le_mul_of_nonneg_right (pow_le_one₀ hbasezero hbaseone) hΛzero).trans
        (by simpa only [one_mul] using hΛ)⟩

  have hSource := exists_preparedCanonicalInitializedRelativeSource
    L oldPatch F outerDepth innerDepth entropy primitive 2 extra
    (initialCost := childCost + 1)
    hheight hsize hms hs hnX hp (by positivity) hRoundedRank
    hPrepLate hRankLate hCapLate
    ((by norm_num : 1 ≤ 2).trans (preparedCommonRadiusPrimitiveExponent_two_le s)) hK0
    hStructOriginal hEarly hPrecision hX hProfile hCutoff N hrank
    hSourceN hSourceRank ip hip c err hprepare herr ih ha haΛ hΛ habsolute
    hcomplexity hD hrest hStage f (fun x _ => hf x) hfree hscore
    ⟨hdiscount.le, hdiscountOne⟩
    (by simpa only [add_assoc, show (2 : ℝ) + 2 = 4 by norm_num] using hChild0)
    (by
      have hchild : (pRelative + 2 + 2) ^ childExponent = childCost := by
        dsimp only [childCost]; congr 1; ring
      rw [hchild]
      linarith)
    H Lmin Qgood hHfloor hHcut hHcost hLmin hQgood hQexp

  let data := hheight.canonicalPaddedSamplerData L Vars (Nat.le_max_left m s)
    (by positivity) hRoundedRank hPrepLate hRankLate hsize
    (Nat.mul_le_mul_right D hms) hCapLate
  let U := fun j => (L.pad (max m s) j).space
  let : ∀ j, DecidableEq (L.pad (max m s) j).Coord := fun _ => Classical.decEq _
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
  let : CompactSpace (EuclideanJetLayers U (fun _ => Unit)) :=
    hPadHeight.euclideanJetLayers_compact (L.pad (max m s)) hpLate hRoundedRank (fun _ => Unit)
  obtain ⟨hR, σ, hσ, S, hRadius0, hRadius, hσone, hσK, hσinv, hSmin, hSmax,
    hgap, hgeometry, hscalars, hDirectAvailable, hModels, hProductive,
    hmargin, Acandidate, hξone, hEnhanced⟩ := hSource
  obtain ⟨centerLift, hMeasurable, hCenterLift, sampleFn, readFn, hGlobal, hChoose⟩ := hEnhanced
  obtain ⟨center, productive, hReady, hProductiveMass, hProductivePoints, hInit⟩ :=
    hChoose (boundedPrimes Qgood) (boundedPrimes_prime Qgood)
      (fun p => Nat.log p Qgood) (boundedPrimes_log_prime_power_le Qgood)
  let A := Acandidate center
  have hSeedScale : Real.exp seed ≤ (S.value : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (hScale.2.2.2.1.trans hSmin))
  have hPlateK := (preparedFiniteScheduleDirectCoarse_requested _ K).trans
    (hscalars anchor).coarse_late
  have hξK := Real.exp_le_exp.mpr (neg_le_neg hPlateK)
  let Plate : ℝ := (fun {a b : ℝ} (_ : a ≤ b) => b) hPlateK
  have nativeRule := degreeGlobalizationAt_of_preparedRelativePositiveSource_canonical
    (E := PreparedSamplerContinuous (L.pad (max m s))) A s hq Aexp hAeq
    (fun x => ((f x - (1 - discount) ^ (stage + 1) * Λ : ℝ) : ℂ))
    Bstruct dim 0 p 0 Plate hB ⟨Nat.cast_nonneg _, hnum⟩ ⟨le_rfl, hB⟩
    ⟨hp0, hpB⟩ ⟨le_rfl, hB⟩ hLayers hVariables
    (by simpa only [Fintype.card_fin] using hX.trans hpB) hG
    (by
      intro outerFront outerInner d hd hds pInput hpInput hpInner
      obtain ⟨profile, hx, hg, hu, hm, hn, hp, he, hc⟩ :=
        hReady.2 outerFront outerInner d hd hds pInput hpInput hpInner
      refine ⟨profile, hx, hg, hu, hm, ?_, hp, he, hc⟩
      simpa only [Fintype.card_fin] using hn.trans
        (preparedFiniteNestedSourceNative_literal_eq (max m s) s Aexp 2
          outerDepth innerDepth constants G vars nX Bstruct dim 0 p 0 Plate
          (outerFront, (0 : Fin (s + 1 + 1)), ⟨d, Nat.lt_succ_of_le hd⟩, false)))
    hSeedScale
  let Vtail : Fin (max m s) → ℝ≥0 := fun _ => ⟨Real.exp chartLog, (Real.exp_pos _).le⟩
  let rawCap := 4 * ∏ j, earlyConstantDensityCap
    (Fintype.card (PreparedSamplerContinuous (L.pad (max m s)) j))
    (preparedSamplerTransverse (L.pad (max m s)) j)
    (allocatedCommonProductRadius (max m s) Bstruct Bstruct) (Vtail j)
  let masters : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth s → ℝ :=
    preparedFiniteNestedSourceMaster (max m s) G vars nX
      (preparedFiniteForwardDetectorPolynomial s) Aexp 2 constants Bstruct dim 0 p 0
  let projectionPrecision := preparedFiniteNestedSourceProjectionPrecision
    (outerDepth := outerDepth) (innerDepth := innerDepth) (cutoff := s)
    (max m s) G vars nX Aexp 2 constants Bstruct dim 0 p 0 Plate K
  let : Nonempty A.Site := A.site_nonempty
  have hDirectReady := hReady.1.1
  have hExcessReady :
      let _ : DecidableEq (Fin nX) := Classical.decEq _
      (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
        (A.law.siteLaw (A.physicalBox hξone hmargin)) rawCap ≤
          6 * positiveProjectionAccuracy projectionPrecision := by
    exact hReady.1.2
  obtain ⟨_, _, hSigmaEndpoint, hXiEndpoint, hFloorEndpoint, hGridEndpoint⟩ :=
    preparedRelativeEndpoint_source_bounds (L.pad (max m s)) M nX Jalloc hCoordCanonical
      (fun _ => σ) _ S.value N hK0 hT
      (by simpa only [hq] using hLayerLog.trans htT)
      (by simpa only [hq] using hModularLog.trans htT)
      (by simpa only [hq] using hDimensionLog.2.trans htT)
      (by simpa only [hq] using hSpatialLog.2.trans htT)
      (hPrimitiveCap.2.trans htT)
      (by simpa only [hq] using hBadLog.2.trans htT)
      hCost0 (hPresLog.2.trans htT) hTest hCompare
      (hRadiusLog.2.trans htT) (hTauLog.2.trans htT)
      (by simpa only [hq] using hSigma)
      (by simpa only [hq] using hCoarse)
      (by simpa only [hq] using hFloor)
      (fun _ => hσ.le) (fun _ => hσK) hξK
      (by simpa only [hq] using hSmin) hKnobN
  have hMarginalCap := preparedRelativeEndpointMarginalCap_le_exp_work s Aexp hA.2.2.1
    (L.pad (max m s)) hq.le M Jalloc hCoordCanonical hB hnum Vtail
    (fun _ => Real.exp_le_exp.mpr hChartLogB) hProfile constants innerDepth outerDepth innerDepth
  obtain ⟨hCapOne, hCapExp, hForecastDetection, hForecastExcess⟩ :=
    preparedRelativePositiveForecastSource A s Aexp 2 Cslice constants Bstruct p 0 Plate masters
      hDirectReady
      hA.1 hB ⟨hp0, hpB⟩ ⟨le_rfl, hB⟩ hξone hξone hmargin hmargin K rawCap
      (preparedConcreteSlicedForecastCapLog (max m s) M nX Jalloc Bstruct cost pRadius p 0 chartLog childCost)
      hSliceWork ((le_max_right 1 rawCap).trans hMarginalCap)
      (by simpa only [pRadius, hq] using hCap)
      hExcessReady
  have hDetectorDecEq : (fun a b : Fin nX => Classical.propDecidable (a = b)) =
      instDecidableEqFin nX := Subsingleton.elim _ _
  rw [hDetectorDecEq] at hForecastDetection
  have hChildValue : ((fun r : ℝ => (r + 2) ^ childExponent)
      ((p + 2) ^ relativePower + 2)) = childCost := by
    dsimp only [childCost, pRelative]; congr 1; ring
  rw [hChildValue] at hInit
  let testLog := (preparedFiniteForwardDetectorPolynomial s).eval₂ (Nat.castRingHom ℝ)
    (allocatedModelTestLog
      (preparedFiniteForwardSourcePrecision Aexp constants innerDepth seed p 0) modelLog)
  have hTestTwo : 2 ≤ testLog := by
    have hsource0 : 0 ≤ preparedFiniteForwardSourcePrecision Aexp constants innerDepth seed p 0 := by
      simpa only [preparedFiniteForwardPairedSourcePrecision_model] using
        preparedFiniteForwardPairedSourcePrecision_nonneg Aexp 2 constants innerDepth false hSeed0
          ⟨hp0, hpB.trans hBseed⟩ ⟨le_rfl, hB.trans hBseed⟩
    dsimp only [testLog]
    rw [preparedFiniteForwardDetectorPolynomial_eval]
    unfold allocatedModelTestLog
    linarith only [hsource0, hModel0,
      Nat.cast_nonneg (α := ℝ) (preparedFiniteForwardDetectorOffset s)]
  let crtBudget := max 1 (max discount⁻¹ K)
  have hKcrt : K ≤ crtBudget := (le_max_right _ _).trans (le_max_right _ _)
  let finalBudget := preparedFinalScalarBudget s s
    (preparedRelativeFinalEnvelope s basePower inputPower preparationPower requiredPower discount p)
  obtain ⟨hBudgetOne, hBudgetRank, hBudgetDimension, hBudgetMatrix, hBudgetPatch,
    hBudgetCap, hBudgetNative, hBudgetCost⟩ := hFinalRequirements
  have hConclusion : RelativePatchSliceConclusion s N f ((1 - discount) * lam)
      (d₀ + s * (D + E)) (spatialPatchExtractionCost (recoveredKernelScalarBudget finalBudget)) :=
    relativePatchSliceConclusion_of_prepared_source_geometry
    (A := A) (S := S) (M := M) (Jalloc := Jalloc)
    (degree := s) (originalRank := d₀) (D := D) (E := E)
    (pRadius := pRadius) (Pdim := Bstruct) (Qstride := 0)
    (PF := chartLog) (Pchart := chartLog) (childLog := childCost)
    (u := u) (p := modelLog) (pSlice := sliceLog) (pTest := testLog)
    (localBudget := native) (precision := K) (C := max 1 rawCap)
    (Ecompare := Ecompare) (Ptest := Ptest) (budget := finalBudget)
    (prep := L.pad (max m s)) (hprep := hPadHeight) (hpPrep := hpLate) (hRprep := hRoundedRank)
    (eSpatial := preparedSpatialKernelBlocks (max m s) M nX)
    (bW := data.bW) (ν := data.measures.layer) (f := f) (lam := lam)
    (hchild := hChild0) (hgain := le_rfl) (hReady := hProductiveMass)
    (hregularityBudget := by simpa only [add_assoc, show (2 : ℝ) + 2 = 4 by norm_num] using hRegularity)
    (hpGlobal := hB) (hchartGlobal := hChartCost)
    (hscoreGlobal := by simpa only [add_assoc, show (2 : ℝ) + 2 = 4 by norm_num] using hNorm)
    (hmassGlobal := by simpa only [add_assoc, show (2 : ℝ) + 2 = 4 by norm_num] using hMass)
    (hfGlobal := hf) (hlam := hlam) (rule := nativeRule)
    (by omega : 0 < max m s) hCoordCanonical
    hData.1.1 hp0 (le_refl 0) hChartLog0 hChartLog0 hCost0
    (fun j => (data.covolume_bound j).2) (fun j => (hRadius j).1)
    (fun j => (hRadius j).2) (fun _ => hσone)
    Vtail data.chart_bound (fun _ => le_rfl)
    (fun _ => Real.exp chartLog) (fun _ => (Real.exp_pos _).le)
    data.inverse_chart_bound (fun _ => Real.exp_le_exp.mpr hChartLogB)
    (hgeometry anchor) hChild0 (centerLift center) hInit hξone hmargin
    hU0 hModel0 hData.2.2.2.2.2.2.1 hSliceWork hCapOne hCapExp
    (by simpa only [pRadius, hq] using hCap)
    (by simpa only [hq] using hModelRequired.2.trans hTK)
    (by simpa only [native, preparedFiniteNestedSourceNative, anchor,
      preparedFiniteNestedForwardAllDegreeAnchor_degree] using hForecastDetection)
    hForecastExcess hSlice0 hCostSlice
    (hChartSlice (childCost + 1) (hChartCost.trans hBseed)) hTestTwo
    (Fintype.equivFin (L.pad (max m s)).PreparedCoordinate).symm
    (by linarith only [hU])
    (by
      simp only [hq, Ecompare, preparedRelativeEndpointComparisonLog,
        preparedRelativeEndpointTestLog, nativeEarly, massEarly]
      exact le_rfl)
    (by simpa only [nativeEarly, hq] using
      (show max native (3 * nativeEarly + 3) ≤ Ptest from le_rfl))
    hSigmaEndpoint
    (fun i => by
      simpa only [hq] using (Real.exp_le_exp.mpr (hNativeAmbient.2.trans hTK)).trans (hKnobN i))
    (by simpa only [hq] using
      (Real.exp_le_exp.mpr (hNativeAmbient.2.trans hTK)).trans hKnobRank)
    hPadSamplingRank (sampleFn center) (readFn center) (hGlobal center)
    (fun z hz => (hProductivePoints z hz).2.2.2.1)
    (by simpa only [Qgood, preparedRelativeEndpointGoodCutoff,
        modularInitialRankStrength_eq_forecast] using
      (fun z hz => (hProductivePoints z hz).2.2.2.2.1))
    (fun z hz => by simpa only [Fintype.card_fin] using
      (hProductivePoints z hz).2.2.2.2.2)
    hB (by simpa only [Fintype.card_fin] using hX.trans hpB) hVariables
    (by simpa only [Fintype.card_fin] using hnX) hpB
    (fun _ => by simp only [Nat.cast_one, Real.exp_zero]; exact le_rfl)
    hCompare.1 hFloorEndpoint hXiEndpoint hGridEndpoint hLateCoord data.integral_basis_bound
    hdiscount hdiscountOne (le_max_left _ _)
    ((le_max_left _ _).trans (le_max_right _ _))
    ⟨hTest.1, hTest.2.trans (hTK.trans hKcrt)⟩
    (by simpa only [hq] using
      (show preparedSlicedForecastBadLog s nX 0 p ∈ Set.Icc 0 crtBudget from
        ⟨hBadLog.1, hBadLog.2.trans (htT.trans (hTK.trans hKcrt))⟩))
    ⟨hPresLog.1, hPresLog.2.trans (htT.trans (hTK.trans hKcrt))⟩
    hq.le (hPadRankSum.trans (Nat.mul_le_mul_right D (Nat.le_max_left m s)))
    hBudgetOne hBudgetRank (by simpa only [hq, Nat.cast_add, Nat.cast_mul] using hBudgetDimension)
    (by simpa only [hq] using hBudgetMatrix) hBudgetPatch
    (by simpa only [pRadius, hq] using hBudgetCap) (by simpa only [hq] using hBudgetNative)
    hBudgetCost hExtractionFinal.2
  have hTarget : (1 - discount) * lam = (1 - discount) ^ (stage + 2) * Λ := by
    dsimp only [lam]
    rw [show stage + 2 = (stage + 1) + 1 by omega, pow_succ]
    ring
  rw [hTarget] at hConclusion
  exact hConclusion.mono le_rfl hExtractionFinal.1

end Erdos3

end

end OAI
