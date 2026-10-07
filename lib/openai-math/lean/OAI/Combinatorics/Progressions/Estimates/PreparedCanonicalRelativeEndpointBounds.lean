import OAI.Combinatorics.Progressions.Dynamics.PreparedFiniteNestedSourcePowerBudget
import OAI.Combinatorics.Progressions.Estimates.PreparedFiniteNestedEndpointRequirement
import OAI.Combinatorics.Progressions.Estimates.PreparedRelativeInitializerScalarInputs

namespace OAI

section

namespace Erdos3.RankPreparationFamily

open Module Submodule VectorPolynomial
open scoped BigOperators

variable {X J : Type} {m q : ℕ} (L : RankPreparationFamily X J m)

theorem pad_rank_sum (hmq : m ≤ q) :
    (∑ j, (L.pad q j).rank) = ∑ j, (L j).rank :=
  L.pad_sum hmq RankPreparationLayer.rank RankPreparationLayer.empty_rank

theorem PreparedHeights.padded_preparation_data
    {pPrep : ℝ} {R D t T : ℕ} (hL : L.PreparedHeights pPrep R)
    (hmq : m ≤ q) (hpPrep : 0 ≤ pPrep) (hsize : L.Sized D t) (ht : t ≤ T) :
    (L.pad q).PreparedHeights pPrep R ∧
    (L.pad q).Sized D t ∧
    (∀ j, Fintype.card (L.pad q j).Coord ≤ preparationCoordinateCap q D T ∧
      Fintype.card (L.pad q j).Column ≤ preparationCoordinateCap q D T ∧
      Fintype.card (L.pad q j).Row + 1 ≤ preparationCoordinateCap q D T) ∧
    (∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (L.pad q j).poly) ∧
    (∀ j α, coefficients (L.pad q j).poly α ∈ (L.pad q j).space) ∧
    (∑ j, (L.pad q j).rank) = ∑ j, (L j).rank := by
  have hpad := hL.pad hmq hpPrep
  have hsized := hsize.pad hmq
  exact ⟨hpad, hsized, preparationCoordinateCap_bounds hsized ht,
    fun j => (hpad j).1, fun j => (hpad j).2.1, L.pad_rank_sum hmq⟩

theorem PreparedHeights.exists_padded_early_late_sampler_geometry
    {pPrep pLate : ℝ} {R D t T : ℕ} (hL : L.PreparedHeights pPrep R)
    (hmq : m ≤ q) (hpPrep : 0 ≤ pPrep) (hR : 1 ≤ R) (hPrepLate : pPrep ≤ pLate)
    (hRLate : (R : ℝ) ≤ Real.exp pLate)
    (hsize : L.Sized D t) (ht : t ≤ T)
    (hcapLate : (preparationCoordinateCap q D T : ℝ) ≤ pLate) :
    let M := preparationCoordinateCap q D T
    ∃ (b : ∀ j, Basis (Fin (preparedSamplerTransverse (L.pad q) j)) ℝ
        (euclideanSubspace (L.pad q j).space)ᗮ)
      (_o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous (L.pad q) j) ℝ
        (euclideanSubspace (L.pad q j).space))
      (bW : ∀ j, Basis (PreparedSamplerContinuous (L.pad q) j) ℤ
        (latticeSection (standardEuclideanLattice (L.pad q j).Coord)
          (euclideanSubspace (L.pad q j).space))),
      (∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (L.pad q j).space)) ∧
      (∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (L.pad q j).space) (b j) z‖ ≤
        Real.exp (allocatedUniformChartLog (M : ℝ)) * ‖z‖) ∧
      (∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (L.pad q j).space) (b j)).symm z‖ ≤
        Real.exp (allocatedUniformChartLog (M : ℝ)) * ‖z‖) ∧
      (∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (L.pad q j).space) (b j) ∧
        mixedDensityCovolumeRatio (euclideanSubspace (L.pad q j).space) (b j) ≤
          Real.exp (allocatedUniformChartLog (M : ℝ))) ∧
      (∀ j a, ‖(bW j a).val‖ ≤
        Real.exp ((pLate + 2) ^ preparedIntegralBasisExponent q)) ∧
      (∀ j i, (basisAxisScale (b j) i : ℝ) ≤
        Real.exp ((pLate + 2) ^ preparedIntegralBasisExponent q)) := by
  exact (hL.pad hmq hpPrep).exists_early_late_sampler_geometry (L.pad q)
    hpPrep hR hPrepLate hRLate (hsize.pad hmq) ht hcapLate

end Erdos3.RankPreparationFamily

end

section

namespace Erdos3
open VectorPolynomial
open scoped BigOperators

noncomputable def preparedRelativeLateHeight
    (Bstruct p : ℝ) (preparationPower requiredPower : ℕ) : ℝ :=
  max Bstruct (max ((p + 2) ^ preparationPower) ((p + 2) ^ requiredPower + 1))

theorem preparedRelative_padded_input
    {X J : Type} {m q D : ℕ} (L : RankPreparationFamily X J m)
    (hmq : m ≤ q) {p Bstruct Rreq : ℝ}
    (preparationPower requiredPower passagePower : ℕ)
    (hp : 0 ≤ p) (hB : 0 ≤ Bstruct)
    (hcap : (preparationCoordinateCap q D (q * D) : ℝ) ≤ Bstruct)
    (hheight : L.PreparedHeights ((p + 2) ^ preparationPower)
      (preparedRoundedRank p requiredPower))
    (hsize : L.Sized D (m * D)) (hrankSum : (∑ j, (L j).rank) ≤ m * D)
    (N : X → ℕ)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ))
      (preparedRoundedRank p requiredPower) (L j).space (L j).poly)
    (hRreq : Rreq ≤ (p + 2) ^ requiredPower)
    (hpower : requiredPower ≤ passagePower)
    (hN : ∀ i, Real.exp ((p + 2) ^ passagePower) ≤ (N i : ℝ)) :
    let pLate := preparedRelativeLateHeight Bstruct p preparationPower requiredPower
    let R := preparedRoundedRank p requiredPower
    0 ≤ pLate ∧
      (L.pad q).PreparedHeights pLate R ∧
      (L.pad q).Sized D (m * D) ∧
      (∀ j, (Fintype.card (L.pad q j).Coord : ℝ) ≤ pLate) ∧
      (∑ j, (L.pad q j).rank) ≤ m * D ∧
      1 ≤ R ∧ (R : ℝ) ≤ Real.exp pLate ∧ Real.exp Rreq ≤ (R : ℝ) ∧
      (∀ i, Real.exp Rreq ≤ (N i : ℝ)) ∧
      (∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ))
        (R : ℝ) (L.pad q j).space (L.pad q j).poly) ∧
      (∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (L.pad q j).poly) ∧
      (∀ j ex, coefficients (L.pad q j).poly ex ∈ (L.pad q j).space) := by
  intro pLate R
  have hbase : 0 ≤ p + 2 := by linarith only [hp]
  have hprep0 : 0 ≤ (p + 2) ^ preparationPower := pow_nonneg hbase _
  have hreq0 : 0 ≤ (p + 2) ^ requiredPower := pow_nonneg hbase _
  have hBlate : Bstruct ≤ pLate := le_max_left _ _
  have hpreplate : (p + 2) ^ preparationPower ≤ pLate :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hreqlate : (p + 2) ^ requiredPower + 1 ≤ pLate :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hpad := hheight.pad hmq hprep0
  have hlate := hpad.mono_parameter (L.pad q) hprep0 hpreplate
  have hsized := hsize.pad hmq
  have hcoordinate := preparationCoordinateCap_bounds hsized
    (Nat.mul_le_mul_right D hmq)
  have hRupper : (R : ℝ) ≤ Real.exp pLate :=
    (ceil_exp_le_exp_add_one hreq0).trans (Real.exp_le_exp.mpr hreqlate)
  refine ⟨hB.trans hBlate, hlate, hsized,
    fun j => (Nat.cast_le.mpr (hcoordinate j).1).trans (hcap.trans hBlate),
    ?_, preparedRoundedRank_one_le p requiredPower, hRupper,
    preparedRoundedRank_exp_requirement hRreq, ?_, L.pad_samplingRank _ _ hrank,
    fun j => (hlate j).1, fun j => (hlate j).2.1⟩
  · rwa [L.pad_rank_sum hmq]
  · intro i
    exact (Real.exp_le_exp.mpr (hRreq.trans
      (pow_le_pow_right₀ (by linarith only [hp]) hpower))).trans (hN i)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

noncomputable def preparedFiniteNestedSourceRequiredLog
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
  Rreq

theorem exists_preparedFiniteNestedSourceRequiredLog_power_budget
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
      preparedFiniteNestedSourceRequiredLog m cutoff A Cdirect outerDepth innerDepth constants
        G M count nX Bstruct pnum Qstride gainLog stageLog Vlog Qσ Pmin requestedCoarse endpoint ≤
          (Bstruct + 2) ^ C := by
  obtain ⟨C, hC, hbound⟩ := exists_preparedFiniteNestedSource_power_budget
    m cutoff A Cdirect outerDepth innerDepth inputPower constants hA hcutoff hworkDepth
  refine ⟨C, hC, ?_⟩
  intro G _ M count nX Bstruct pnum Qstride gainLog stageLog Vlog Qσ Pmin requestedCoarse endpoint
    hB hnum hstride hg hs hM hcount hnX hG hV hQσ hPmin hcoarse hend
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hrequired⟩ :=
    hbound G M count nX hB hnum hstride hg hs hM hcount hnX hG hV hQσ hPmin hcoarse hend
  exact hrequired

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

noncomputable def preparedCanonicalRelativeSourceRequired
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
  preparedFiniteNestedSourceRequiredLog q s
    (preparedFiniteNestedSourceExponent q s e Cprimitive Cdirect extra) Cdirect outerDepth innerDepth
    AllocatedExternalCandidateSampler.degreeSourceCountConstants G M count nX Bstruct
    (enlargedPreparedCommonSamplerDimension q M Jalloc) 0 p 0 knob knob knob knob knob

structure PreparedCanonicalRelativeScalarInputs
    {nX m D : ℕ} (prep : RankPreparationFamily (Fin nX) (Fin D) m)
    (s : ℕ) (p pRelative Bstruct : ℝ) : Prop where
  hcoord : ∀ j, Fintype.card (prep j).Coord ≤ preparationCoordinateCap m D (m * D)
  hCoord : ∀ j, Fintype.card (prep j).Coord ≤ preparationCoordinateCap (max m s) D (s * D)
  hpRelative : 0 ≤ pRelative
  hpB : pRelative ≤ Bstruct
  hB : 0 ≤ Bstruct
  hp0 : 0 ≤ p
  hpInput : p ≤ pRelative
  hpSource : p ≤ Bstruct
  hnum :
    (enlargedPreparedCommonSamplerDimension (max m s)
      (preparationCoordinateCap (max m s) D (s * D))
      (modularInitialBlockCount (max m s)
        (nX + max m s * preparationCoordinateCap (max m s) D (s * D))) : ℝ) ≤ Bstruct
  hchartBudget : allocatedUniformChartLog
    (preparationCoordinateCap (max m s) D (s * D) : ℝ) + 1 ≤ Bstruct
  hChartExp : Real.exp (allocatedUniformChartLog
    (preparationCoordinateCap (max m s) D (s * D) : ℝ)) ≤ Real.exp Bstruct
  hEarlyRadius : ∀ j,
    Real.exp (6 * pRelative + 35) *
      ((Fintype.card (PreparedSamplerContinuous (prep.pad (max m s)) j) : ℝ) + 1) *
      allocatedCommonProductRadius (max m s) Bstruct Bstruct ≤ 1 / 4

theorem preparedCanonicalRelative_scalarInputs
    {nX m s D : ℕ} (prep : RankPreparationFamily (Fin nX) (Fin D) m)
    {p pRelative Bstruct : ℝ}
    (hsize : prep.Sized D (m * D)) (hms : m ≤ s) (hp : 2 ≤ p)
    (hstructure :
      let M := preparationCoordinateCap s D (s * D)
      let Jalloc := modularInitialBlockCount s (nX + s * M)
      let dim := enlargedPreparedCommonSamplerDimension s M Jalloc
      p ≤ pRelative ∧ (s : ℝ) + 3 ≤ pRelative ∧
        (M : ℝ) ≤ pRelative ∧ (Jalloc : ℝ) ≤ pRelative ∧
        (dim : ℝ) ≤ pRelative ∧ allocatedUniformChartLog (M : ℝ) + 1 ≤ pRelative)
    (hBrelative : 6 * pRelative + 35 ≤ Bstruct) :
    PreparedCanonicalRelativeScalarInputs prep s p pRelative Bstruct := by
  let q := max m s
  let M := preparationCoordinateCap q D (s * D)
  let Jalloc := modularInitialBlockCount q (nX + q * M)
  have hq : q = s := max_eq_right hms
  have hcoord : ∀ j, Fintype.card (prep j).Coord ≤ preparationCoordinateCap m D (m * D) :=
    fun j => (preparationCoordinateCap_bounds hsize le_rfl j).1
  have hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M := by
    intro j
    exact (hcoord j).trans (preparationCoordinateCap_mono (Nat.le_max_left m s)
      (Nat.mul_le_mul_right D hms))
  have hp0 : 0 ≤ p := (by norm_num : (0 : ℝ) ≤ 2).trans hp
  have hpInput : p ≤ pRelative := hstructure.1
  have hpRelative : 0 ≤ pRelative := hp0.trans hpInput
  have hpB : pRelative ≤ Bstruct := by linarith only [hpRelative, hBrelative]
  have hB : 0 ≤ Bstruct := hpRelative.trans hpB
  have hnum : (enlargedPreparedCommonSamplerDimension q M Jalloc : ℝ) ≤ Bstruct := by
    have h := hstructure.2.2.2.2.1
    simpa only [M, Jalloc, hq] using h.trans hpB
  have hchartBudget : allocatedUniformChartLog (M : ℝ) + 1 ≤ Bstruct := by
    have h := hstructure.2.2.2.2.2
    simpa only [M, hq] using h.trans hpB
  have hChartExp : Real.exp (allocatedUniformChartLog (M : ℝ)) ≤ Real.exp Bstruct :=
    Real.exp_le_exp.mpr (by linarith only [hchartBudget])
  exact {
    hcoord := hcoord
    hCoord := hCoord
    hpRelative := hpRelative
    hpB := hpB
    hB := hB
    hp0 := hp0
    hpInput := hpInput
    hpSource := hpInput.trans hpB
    hnum := hnum
    hchartBudget := hchartBudget
    hChartExp := hChartExp
    hEarlyRadius := preparedFiniteNestedSource_relative_radius prep nX M s hCoord hB hnum hBrelative
      (fun _ => Real.exp (6 * pRelative + 35)) (fun _ => (Real.exp_pos _).le) (fun _ => le_rfl) }

theorem preparedCanonicalRelativeSourceRequired_physicalSize
    {nX D m : ℕ} (prep : RankPreparationFamily (Fin nX) (Fin D) m)
    (s outerDepth innerDepth e Cprimitive Cdirect extra : ℕ)
    {Bstruct p knob : ℝ} (N : Fin nX → ℕ)
    (hs : 1 ≤ s) (hB : 0 ≤ Bstruct) (hp0 : 0 ≤ p)
    (hpSource : p ≤ Bstruct) (hnXp : (nX : ℝ) ≤ p)
    (hN : ∀ i, Real.exp (preparedCanonicalRelativeSourceRequired prep s outerDepth innerDepth
      e Cprimitive Cdirect extra Bstruct p knob) ≤ (N i : ℝ)) :
    ∀ i, 4 ≤ Real.exp (-(p + nX + 8)) * (N i : ℝ) := by
  have hA := (preparedFiniteNestedSourceExponent_bounds (max m s) s e Cprimitive Cdirect extra
    (preparedFiniteNestedSourceExponent (max m s) s e Cprimitive Cdirect extra) le_rfl).1
  exact (preparedFiniteNestedSourceRequired_trim_bounds
    (preparedFiniteNestedSourceExponent (max m s) s e Cprimitive Cdirect extra)
    AllocatedExternalCandidateSampler.degreeSourceCountConstants innerDepth outerDepth s
    Bstruct _ _ _ nX N hA hs hB hpSource (hnXp.trans hpSource) hp0 hN).2.2.2

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

theorem exists_preparedFiniteNestedCanonicalRequired_power_budget
    (s outerDepth innerDepth cutoff e Cprimitive Cdirect extra earlybasePower : ℕ)
    (constants : ℕ → ℕ) (hworkDepth : cutoff ≤ innerDepth) (hbasePower : 1 ≤ earlybasePower) :
    ∃ requiredPower : ℕ, 2 ≤ requiredPower ∧ ∀ {p : ℝ}, 2 ≤ p →
      ∀ m ≤ s, ∀ (G : Type) [Fintype G] (M count nX : ℕ)
      {pnum Qstride gainLog stageLog Vlog Qσ Pmin requestedCoarse endpoint : ℝ},
      let q := max m cutoff
      let A := preparedFiniteNestedSourceExponent q cutoff e Cprimitive Cdirect extra
      let Bstruct := (p + 2) ^ earlybasePower
      pnum ∈ Set.Icc 0 Bstruct → Qstride ∈ Set.Icc 0 Bstruct →
      gainLog ∈ Set.Icc 0 Bstruct → stageLog ∈ Set.Icc 0 Bstruct →
      (M : ℝ) ≤ Bstruct → (count : ℝ) ≤ Bstruct → (nX : ℝ) ≤ Bstruct →
      (Fintype.card G : ℝ) ≤ Bstruct → Vlog ∈ Set.Icc 0 Bstruct →
      Qσ ∈ Set.Icc 0 Bstruct → Pmin ∈ Set.Icc 0 Bstruct →
      requestedCoarse ∈ Set.Icc 0 Bstruct → endpoint ∈ Set.Icc 0 Bstruct →
      preparedFiniteNestedSourceRequiredLog q cutoff A Cdirect outerDepth innerDepth constants
        G M count nX Bstruct pnum Qstride gainLog stageLog Vlog Qσ Pmin requestedCoarse endpoint ≤
          (p + 2) ^ requiredPower := by
  let q := fun i : Fin (s + 1) => max i.val cutoff
  let A := fun i : Fin (s + 1) =>
    preparedFiniteNestedSourceExponent (q i) cutoff e Cprimitive Cdirect extra
  have hA (i : Fin (s + 1)) : 2 ≤ A i :=
    (preparedFiniteNestedSourceExponent_bounds (q i) cutoff e Cprimitive Cdirect extra (A i) le_rfl).1
  let exponent := fun i : Fin (s + 1) => Classical.choose
    (exists_preparedFiniteNestedSourceRequiredLog_power_budget (q i) cutoff (A i) Cdirect
      outerDepth innerDepth 1 constants (hA i) (Nat.le_max_right _ _) hworkDepth)
  let boundPoly : Polynomial ℕ := ∑ i : Fin (s + 1),
    ((Polynomial.X + 2) ^ earlybasePower + 2) ^ exponent i
  obtain ⟨requiredPower, hrequiredPower, hbound⟩ := exists_natPolynomial_fixed_power_budget boundPoly
  refine ⟨requiredPower, hrequiredPower, ?_⟩
  intro p hp m hm G _ M count nX pnum Qstride gainLog stageLog Vlog Qσ Pmin requestedCoarse endpoint
    q' A' Bstruct hnum hstride hg hs hM hcount hnX hG hV hQσ hPmin hcoarse hend
  let i : Fin (s + 1) := ⟨m, Nat.lt_succ_of_le hm⟩
  have hp0 : 0 ≤ p := (by norm_num : (0 : ℝ) ≤ 2).trans hp
  have hB : 2 ≤ Bstruct := by
    have hpower : p + 2 ≤ (p + 2) ^ earlybasePower := by
      simpa only [pow_one] using pow_le_pow_right₀
        (by linarith only [hp] : 1 ≤ p + 2) hbasePower
    exact (by linarith only [hp] : (2 : ℝ) ≤ p + 2).trans hpower
  have lift {x : ℝ} (hx : x ∈ Set.Icc 0 Bstruct) :
      x ∈ Set.Icc 0 ((Bstruct + 2) ^ 1) := by
    refine ⟨hx.1, ?_⟩
    simpa only [pow_one] using hx.2.trans
      (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2))
  have hlocal := (Classical.choose_spec
    (exists_preparedFiniteNestedSourceRequiredLog_power_budget (q i) cutoff (A i) Cdirect
      outerDepth innerDepth 1 constants (hA i) (Nat.le_max_right _ _) hworkDepth)).2
    G M count nX hB hnum hstride hg hs hM hcount hnX hG
    (lift hV) (lift hQσ) (lift hPmin) (lift hcoarse) (lift hend)
  have hentry : (Bstruct + 2) ^ exponent i ≤ (p + 2) ^ requiredPower := by
    apply le_trans _ (hbound p hp0)
    rw [Polynomial.eval₂_finsetSum]
    have hsingle := Finset.single_le_sum
      (f := fun j : Fin (s + 1) =>
        (((Polynomial.X + 2) ^ earlybasePower + 2) ^ exponent j).eval₂ (Nat.castRingHom ℝ) p)
      (fun j _ => natPolynomial_eval_nonneg _ hp0) (Finset.mem_univ i)
    simpa [Bstruct, Polynomial.eval₂_pow] using hsingle
  exact hlocal.trans hentry

theorem exists_preparedFiniteNestedCanonicalRequired_power_budget_of_inputPower
    (s outerDepth innerDepth cutoff e Cprimitive Cdirect extra earlybasePower inputPower : ℕ)
    (constants : ℕ → ℕ) (hworkDepth : cutoff ≤ innerDepth) (hbasePower : 1 ≤ earlybasePower) :
    ∃ requiredPower : ℕ, 2 ≤ requiredPower ∧ ∀ {p : ℝ}, 2 ≤ p →
      ∀ m ≤ s, ∀ (G : Type) [Fintype G] (M count nX : ℕ)
      {pnum Qstride gainLog stageLog Vlog Qσ Pmin requestedCoarse endpoint : ℝ},
      let q := max m cutoff
      let A := preparedFiniteNestedSourceExponent q cutoff e Cprimitive Cdirect extra
      let Bstruct := (p + 2) ^ earlybasePower
      pnum ∈ Set.Icc 0 Bstruct → Qstride ∈ Set.Icc 0 Bstruct →
      gainLog ∈ Set.Icc 0 Bstruct → stageLog ∈ Set.Icc 0 Bstruct →
      (M : ℝ) ≤ Bstruct → (count : ℝ) ≤ Bstruct → (nX : ℝ) ≤ Bstruct →
      (Fintype.card G : ℝ) ≤ Bstruct →
      Vlog ∈ Set.Icc 0 ((Bstruct + 2) ^ inputPower) →
      Qσ ∈ Set.Icc 0 ((Bstruct + 2) ^ inputPower) →
      Pmin ∈ Set.Icc 0 ((Bstruct + 2) ^ inputPower) →
      requestedCoarse ∈ Set.Icc 0 ((Bstruct + 2) ^ inputPower) →
      endpoint ∈ Set.Icc 0 ((Bstruct + 2) ^ inputPower) →
      preparedFiniteNestedSourceRequiredLog q cutoff A Cdirect outerDepth innerDepth constants
        G M count nX Bstruct pnum Qstride gainLog stageLog Vlog Qσ Pmin requestedCoarse endpoint ≤
          (p + 2) ^ requiredPower := by
  let q := fun i : Fin (s + 1) => max i.val cutoff
  let A := fun i : Fin (s + 1) =>
    preparedFiniteNestedSourceExponent (q i) cutoff e Cprimitive Cdirect extra
  have hA (i : Fin (s + 1)) : 2 ≤ A i :=
    (preparedFiniteNestedSourceExponent_bounds (q i) cutoff e Cprimitive Cdirect extra (A i) le_rfl).1
  let exponent := fun i : Fin (s + 1) => Classical.choose
    (exists_preparedFiniteNestedSourceRequiredLog_power_budget (q i) cutoff (A i) Cdirect
      outerDepth innerDepth inputPower constants (hA i) (Nat.le_max_right _ _) hworkDepth)
  let boundPoly : Polynomial ℕ := ∑ i : Fin (s + 1),
    ((Polynomial.X + 2) ^ earlybasePower + 2) ^ exponent i
  obtain ⟨requiredPower, hrequiredPower, hbound⟩ := exists_natPolynomial_fixed_power_budget boundPoly
  refine ⟨requiredPower, hrequiredPower, ?_⟩
  intro p hp m hm G _ M count nX pnum Qstride gainLog stageLog Vlog Qσ Pmin requestedCoarse endpoint
    q' A' Bstruct hnum hstride hg hs hM hcount hnX hG hV hQσ hPmin hcoarse hend
  let i : Fin (s + 1) := ⟨m, Nat.lt_succ_of_le hm⟩
  have hp0 : 0 ≤ p := (by norm_num : (0 : ℝ) ≤ 2).trans hp
  have hB : 2 ≤ Bstruct := by
    have hpower : p + 2 ≤ (p + 2) ^ earlybasePower := by
      simpa only [pow_one] using pow_le_pow_right₀
        (by linarith only [hp] : 1 ≤ p + 2) hbasePower
    exact (by linarith only [hp] : (2 : ℝ) ≤ p + 2).trans hpower
  have hlocal := (Classical.choose_spec
    (exists_preparedFiniteNestedSourceRequiredLog_power_budget (q i) cutoff (A i) Cdirect
      outerDepth innerDepth inputPower constants (hA i) (Nat.le_max_right _ _) hworkDepth)).2
    G M count nX hB hnum hstride hg hs hM hcount hnX hG
    hV hQσ hPmin hcoarse hend
  have hentry : (Bstruct + 2) ^ exponent i ≤ (p + 2) ^ requiredPower := by
    apply le_trans _ (hbound p hp0)
    rw [Polynomial.eval₂_finsetSum]
    have hsingle := Finset.single_le_sum
      (f := fun j : Fin (s + 1) =>
        (((Polynomial.X + 2) ^ earlybasePower + 2) ^ exponent j).eval₂ (Nat.castRingHom ℝ) p)
      (fun j _ => natPolynomial_eval_nonneg _ hp0) (Finset.mem_univ i)
    simpa [Bstruct, Polynomial.eval₂_pow] using hsingle
  exact hlocal.trans hentry

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

 theorem preparedFiniteNestedSourceProjectionPrecision_endpoint_le
    (m cutoff A Cdirect outerDepth innerDepth : ℕ)
    (constants : ℕ → ℕ) (G : Type) [Fintype G] (count nX : ℕ)
    {Bstruct gainLog stageLog : ℝ} (pnum Qstride Plate endpoint : ℝ)
    (hA : 2 ≤ A) (hB : 0 ≤ Bstruct)
    (hg : gainLog ∈ Set.Icc 0 Bstruct) (hs : stageLog ∈ Set.Icc 0 Bstruct) :
    endpoint ≤ preparedFiniteNestedSourceProjectionPrecision
      (outerDepth := outerDepth) (innerDepth := innerDepth) (cutoff := cutoff)
      m G count nX A Cdirect constants Bstruct pnum Qstride gainLog stageLog Plate endpoint := by
  exact preparedNestedFrontProjectionEnvelope_endpoint_le A constants innerDepth
    _ _ _ endpoint hA hB hg hs

 theorem preparedFiniteNestedSourceRequiredLog_endpoint_le
    (m cutoff A Cdirect outerDepth innerDepth : ℕ)
    (constants : ℕ → ℕ) (G : Type) [Fintype G] (M count nX : ℕ)
    {Bstruct gainLog stageLog : ℝ} (pnum Qstride Vlog Qσ Pmin requestedCoarse endpoint : ℝ)
    (hA : 2 ≤ A) (hB : 0 ≤ Bstruct)
    (hg : gainLog ∈ Set.Icc 0 Bstruct) (hs : stageLog ∈ Set.Icc 0 Bstruct) :
    endpoint ≤ preparedFiniteNestedSourceRequiredLog m cutoff A Cdirect outerDepth innerDepth
      constants G M count nX Bstruct pnum Qstride gainLog stageLog Vlog Qσ Pmin requestedCoarse endpoint := by
  unfold preparedFiniteNestedSourceRequiredLog
  apply preparedFiniteNestedSourceRequired_endpoint_le m A constants innerDepth outerDepth cutoff Bstruct
  exact preparedFiniteNestedSourceProjectionPrecision_endpoint_le m cutoff A Cdirect
    outerDepth innerDepth constants G count nX pnum Qstride _ endpoint hA hB hg hs

theorem preparedCanonicalRelativeSourceRequired_endpoint_le
    {nX D m : ℕ} (prep : RankPreparationFamily (Fin nX) (Fin D) m)
    (s outerDepth innerDepth e Cprimitive Cdirect extra : ℕ)
    {Bstruct p : ℝ} (knob : ℝ) (hB : 0 ≤ Bstruct) (hp : p ∈ Set.Icc 0 Bstruct) :
    knob ≤ preparedCanonicalRelativeSourceRequired prep s outerDepth innerDepth
      e Cprimitive Cdirect extra Bstruct p knob := by
  unfold preparedCanonicalRelativeSourceRequired
  apply preparedFiniteNestedSourceRequiredLog_endpoint_le
  · exact (preparedFiniteNestedSourceExponent_bounds (max m s) s e Cprimitive Cdirect extra
      (preparedFiniteNestedSourceExponent (max m s) s e Cprimitive Cdirect extra) le_rfl).1
  · exact hB
  · exact hp
  · exact ⟨le_rfl, hB⟩

theorem preparedCanonicalRelativeProjection_endpoint_le
    {Slot : Type*} [Fintype Slot]
    (m cutoff e Cprimitive Cdirect extra innerDepth : ℕ) (constants : ℕ → ℕ)
    (outer inner : Slot → ℕ) (native : Slot → ℝ)
    {Bstruct p : ℝ} (knob : ℝ) (hB : 0 ≤ Bstruct) (hp : p ∈ Set.Icc 0 Bstruct) :
    knob ≤ preparedNestedFrontProjectionEnvelope
      (preparedFiniteNestedSourceExponent m cutoff e Cprimitive Cdirect extra)
      constants innerDepth outer inner native Bstruct p 0 knob := by
  exact preparedNestedFrontProjectionEnvelope_endpoint_le _ constants innerDepth
    outer inner native knob
    (preparedFiniteNestedSourceExponent_bounds m cutoff e Cprimitive Cdirect extra
      (preparedFiniteNestedSourceExponent m cutoff e Cprimitive Cdirect extra) le_rfl).1
    hB hp ⟨le_rfl, hB⟩

end Erdos3.VectorPolynomial

end

end OAI
