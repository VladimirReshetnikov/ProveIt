import OAI.Combinatorics.Progressions.Estimates.PreparedFiniteNestedAnchorRequiredPower

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

theorem exists_preparedFiniteNestedSource_power_budget
    (m cutoff A Cdirect outerDepth innerDepth inputPower : ℕ)
    (constants : ℕ → ℕ) (hA : 2 ≤ A) (hcutoff : cutoff ≤ m)
    (hworkDepth : cutoff ≤ innerDepth) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (G : Type) [Fintype G] (M count nX : ℕ)
      {Bstruct pnum Qstride gainLog stageLog Vlog Qσ Pmin requestedCoarse endpoint : ℝ},
      2 ≤ Bstruct → pnum ∈ Set.Icc 0 Bstruct → Qstride ∈ Set.Icc 0 Bstruct →
      gainLog ∈ Set.Icc 0 Bstruct → stageLog ∈ Set.Icc 0 Bstruct →
      (M : ℝ) ≤ Bstruct → (count : ℝ) ≤ Bstruct → (nX : ℝ) ≤ Bstruct →
      (Fintype.card G : ℝ) ≤ Bstruct →
      Vlog ∈ Set.Icc 0 ((Bstruct + 2) ^ inputPower) →
      Qσ ∈ Set.Icc 0 ((Bstruct + 2) ^ inputPower) →
      Pmin ∈ Set.Icc 0 ((Bstruct + 2) ^ inputPower) →
      requestedCoarse ∈ Set.Icc 0 ((Bstruct + 2) ^ inputPower) →
      endpoint ∈ Set.Icc 0 ((Bstruct + 2) ^ inputPower) →
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
      let Econditional := preparedFiniteNestedSourceProjectionPrecision
        (outerDepth := outerDepth) (innerDepth := innerDepth) (cutoff := cutoff)
        m G count nX A Cdirect constants Bstruct pnum Qstride gainLog stageLog Plate endpoint
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
      let bound := (Bstruct + 2) ^ C
      pRadius ∈ Set.Icc 0 bound ∧ Pscale ∈ Set.Icc 0 bound ∧ Pseed ∈ Set.Icc 0 bound ∧
      Plate ∈ Set.Icc 0 bound ∧ Econditional ∈ Set.Icc 0 bound ∧ endpoint ≤ Econditional ∧
      baseB0 ∈ Set.Icc 0 bound ∧ Pwidth ∈ Set.Icc 0 bound ∧ Bcert ∈ Set.Icc 0 bound ∧
      Pgood ∈ Set.Icc 0 bound ∧ anchorRequired ≤ bound ∧ conditionalRequired ≤ bound ∧
      (∀ k, detectorRequired k ≤ bound) ∧ Rreq ≤ bound := by
  let K := PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff
  obtain ⟨Cgeom, hCgeom, hgeom⟩ := exists_preparedFiniteNestedSourceLate_power_budget
    m cutoff A Cdirect outerDepth innerDepth inputPower constants hA hcutoff
  let projectionInput := max Cgeom inputPower
  obtain ⟨Cproj, Cconditional, _, _, hprojection⟩ := exists_preparedFiniteNestedSourceProjection_budget
    m cutoff A Cdirect outerDepth innerDepth projectionInput constants hA hcutoff
  let primitivePoly : Polynomial ℕ := 8 * Polynomial.X + 3 * (Polynomial.X + 2) ^ inputPower + 64
  obtain ⟨Cprimitive, _, hprimitive⟩ := exists_natPolynomial_fixed_power_budget primitivePoly
  let anchorInput := max Cgeom (max Cproj Cprimitive)
  obtain ⟨Canchor, hCanchor, hanchor⟩ := exists_preparedFiniteNestedAnchorScalars_power_budget m anchorInput
  let componentPower := max Canchor (max Cconditional Cgeom)
  obtain ⟨Creq, _, hrequired⟩ := exists_preparedFiniteNestedSourceRequired_power_budget
    A constants innerDepth outerDepth componentPower (Fintype.card K) hA
  let C := max Creq (max Canchor (max Cgeom Cproj))
  refine ⟨C, hCanchor.trans ((le_max_left _ _).trans (le_max_right _ _)), ?_⟩
  intro G _ M count nX Bstruct pnum Qstride gainLog stageLog Vlog Qσ Pmin requestedCoarse endpoint
    hB hnum hstride hg hs hM hcount hnX hG hV hQσ hPmin hcoarse hend
    K' degree Pdetect Cdetect kModel sourceU modelLog pRadius D pDetect aDetect detectionGain Pk
    Pphysical target Eprofile Prho Ptail Pscale Tmod lengthLogs Pseed Qw Pmaster coarseTarget Plate
    Econditional baseB0 Pwidth Bcert Pgood anchorRequired conditionalRequired detectorRequired Rreq bound
  have hB0 : 0 ≤ Bstruct := (by norm_num : (0 : ℝ) ≤ 2).trans hB
  have hbase : 1 ≤ Bstruct + 2 := by linarith only [hB]
  have raise {a b : ℕ} (h : a ≤ b) : (Bstruct + 2) ^ a ≤ (Bstruct + 2) ^ b :=
    pow_le_pow_right₀ hbase h
  have lift {a b : ℕ} {x : ℝ} (h : a ≤ b) (hx : x ∈ Set.Icc 0 ((Bstruct + 2) ^ a)) :
      x ∈ Set.Icc 0 ((Bstruct + 2) ^ b) := ⟨hx.1, hx.2.trans (raise h)⟩
  have hgeometry := hgeom G count nX hB0 hnum hstride hg hs hcount hnX hG hV hQσ hPmin hcoarse
  obtain ⟨hSeed, _hWitness, hSchedule⟩ := hgeometry
  change Pseed ∈ Set.Icc 0 ((Bstruct + 2) ^ Cgeom) at hSeed
  obtain ⟨hRadius, _hD, hScale, _hCoarse, hPlate, hSlots⟩ := hSchedule
  have hMaster (k : K') : Pmaster k ∈ Set.Icc 0 ((Bstruct + 2) ^ Cgeom) :=
    (hSlots k).2.2.2.2.2.2.2.1
  have hDetector (k : K') : detectorRequired k ≤ (Bstruct + 2) ^ Cgeom :=
    (hSlots k).2.2.2.2.2.2.2.2.required.2
  have hMasterLate (k : K') : Pmaster k ≤ Plate := by
    apply (le_max_left _ _).trans
    exact Finset.single_le_sum
      (f := fun k => preparedUniformDegreeDirectLate (Pmaster k) Pscale (Pphysical k)
        coarseTarget (allocatedWitnessScaleLog Pseed Qw))
      (fun k _ => (hMaster k).1.trans (le_max_left _ _)) (Finset.mem_univ k)
  obtain ⟨hProjection, hEndpoint, hConditional⟩ := hprojection G count nX hB hnum hstride hg hs
    hcount hnX hG (lift (le_max_right _ _) hend) (lift (le_max_left _ _) hPlate)
  have hPrimitiveBound : 8 * Bstruct + 3 * (Bstruct + 2) ^ inputPower + 64 ≤
      (Bstruct + 2) ^ Cprimitive := by
    simpa [primitivePoly, Polynomial.eval₂_pow] using hprimitive Bstruct hB0
  have hInput0 : 0 ≤ (Bstruct + 2) ^ inputPower := by positivity
  have hBprimitive : Bstruct ≤ (Bstruct + 2) ^ Cprimitive := by
    linarith only [hPrimitiveBound, hB0, hInput0]
  have hVprimitive : Vlog ∈ Set.Icc 0 ((Bstruct + 2) ^ Cprimitive) := by
    exact ⟨hV.1, hV.2.trans (by linarith only [hPrimitiveBound, hB0, hInput0])⟩
  have hQwprimitive : Qw ∈ Set.Icc 0 ((Bstruct + 2) ^ Cprimitive) := by
    constructor
    · dsimp only [Qw]; have := hV.1; have := hg.1; positivity
    · dsimp only [Qw]
      linarith only [hPrimitiveBound, hg.2, hV.2, hB0, hInput0]
  have hPrimitiveAnchor : Cprimitive ≤ anchorInput := (le_max_right _ _).trans (le_max_right _ _)
  have hBanchor : Bstruct ≤ (Bstruct + 2) ^ anchorInput := hBprimitive.trans (raise hPrimitiveAnchor)
  obtain ⟨hBase, hWidth, hCertificate, hGood, hAnchor⟩ := hanchor hB M nX
    (hM.trans hBanchor) (hnX.trans hBanchor)
    (lift (le_max_left _ _) hRadius) (lift (le_max_left _ _) hScale)
    (lift (le_max_left _ _) hSeed) (lift hPrimitiveAnchor hQwprimitive)
    ⟨hg.1, hg.2.trans hBanchor⟩ (lift hPrimitiveAnchor hVprimitive)
    (lift ((le_max_left _ _).trans (le_max_right _ _)) hProjection)
    (hMaster kModel).1 (hMasterLate kModel) (hPlate.2.trans (raise (le_max_left _ _)))
  have hRreq : Rreq ≤ (Bstruct + 2) ^ Creq := hrequired K' cutoff hworkDepth le_rfl hB0
    (hAnchor.trans (raise (le_max_left _ _)))
    (hConditional.trans (raise ((le_max_left _ _).trans (le_max_right _ _))))
    detectorRequired (fun k => (hDetector k).trans
      (raise ((le_max_right _ _).trans (le_max_right _ _))))
  have hGeomFinal : Cgeom ≤ C := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hProjFinal : Cproj ≤ C := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hAnchorFinal : Canchor ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  refine ⟨lift hGeomFinal hRadius, lift hGeomFinal hScale, lift hGeomFinal hSeed,
    lift hGeomFinal hPlate, lift hProjFinal hProjection, hEndpoint,
    lift hAnchorFinal hBase, lift hAnchorFinal hWidth, lift hAnchorFinal hCertificate,
    lift hAnchorFinal hGood, hAnchor.trans (raise hAnchorFinal), ?_,
    fun k => (hDetector k).trans (raise hGeomFinal), hRreq.trans (raise (le_max_left _ _))⟩
  exact (conditionalRequired_le_preparedFiniteNestedSourceRequired A constants innerDepth outerDepth cutoff
    Bstruct anchorRequired conditionalRequired detectorRequired).trans
      (hRreq.trans (raise (le_max_left _ _)))

end Erdos3.VectorPolynomial

end

end OAI
