import OAI.Combinatorics.Progressions.Estimates.AllocatedCandidateInnerSourceGain
import OAI.Combinatorics.Progressions.Linear.PreparedFiniteNestedSourceProjectionBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {X₀ J₀ G X : Type} [Fintype G] [Fintype X]
    (prep : RankPreparationFamily X₀ J₀ m)
    {B : LayerSamplerAxis (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) → Type}
    [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ ((prep j).Coord → ℝ)}
    {b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ ((prep j).Coord → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern
      (Option (LayerSamplerVariables G (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice ((prep j).Coord)) (euclideanSubspace (U j)))]
    (sampler : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateSampler

local instance nestedDegreeSourceSiteNonempty : Nonempty sampler.Site := sampler.site_nonempty
local notation "countConstants" => degreeSourceCountConstants

variable (outerDepth innerDepth cutoff exponent Cprimitive Cslice Cdirect M Jalloc : ℕ)
    (Bstruct gainLog stageLog Qstride Plate E endpoint rankThreshold : ℝ)

local notation "Slots" => PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff
local notation "count" => Fintype.card (LayerSamplerVariables G
    (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) B)
local notation "pnum" => (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ)
local notation "seed" => candidateNestedForwardSeed exponent countConstants innerDepth
local notation "native" => preparedFiniteNestedSourceNative m G count (Fintype.card X)
    (preparedFiniteForwardDetectorPolynomial cutoff) exponent Cdirect countConstants
    Bstruct pnum Qstride gainLog stageLog Plate
local notation "slotSeed" => preparedFiniteNestedForwardAllDegreeSeed exponent countConstants Bstruct
local notation "slotStage" => preparedFiniteNestedForwardAllDegreeStage
local notation "slotDegree" => preparedFiniteNestedForwardAllDegreeDegree

attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection

noncomputable def preparedFiniteNestedDegreeSourceProfile
    (outerFront outerInner : Fin (outerDepth + 1)) {degree e : ℕ} {p chartLog : ℝ}
    (hdegree : degree ≤ cutoff) (hcutoff : cutoff ≤ m) (hdepth : degree ≤ innerDepth)
    (hFrontExponent : preparedFiniteForwardFrontProfileExponent e ≤ exponent)
    (hCapExponent : preparedCommonRadiusDensityCapNestedExponent m ≤ exponent)
    (hInnerExponent : allocatedCandidateForwardScheduleExponent degree m Cprimitive
      (preparedFiniteForwardInnerSourceExponent Cdirect
        (preparedFiniteForwardActualNativeBudgetExponent m
          (preparedFiniteForwardDetectorPolynomial cutoff))) 2 ≤ exponent)
    (hCslice : 1 ≤ Cslice) (hSliceExponent : Cslice + 1 ≤ exponent)
    (hInnerSlice : allocatedCandidateStageSliceExponent degree m Cprimitive ≤ Cslice)
    (hprimitive : 1 ≤ Cprimitive)
    (hBstruct : 0 ≤ Bstruct) (hg : gainLog ∈ Set.Icc 0 Bstruct)
    (hs : stageLog ∈ Set.Icc 0 Bstruct) (hQstride : Qstride ∈ Set.Icc 0 Bstruct)
    (hM : ∀ j, Fintype.card (prep j).Coord ≤ M) (hnum : pnum ≤ Bstruct)
    (hG : (Fintype.card G : ℝ) ≤ Bstruct)
    (htags : (Fintype.card (X ⊕ (Σ j, (prep j).Coord)) : ℝ) ≤ Bstruct)
    (hvariables : (count : ℝ) ≤ Bstruct)
    (hpFront : p ∈ Set.Icc 0 (seed outerFront.val Bstruct))
    (hpInner : p ≤ seed outerInner.val Bstruct)
    (hξ : ξ ≤ 1) (hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i)
    (Vtail : Fin m → ℝ≥0) (hVtail : ∀ j, (Vtail j : ℝ) ≤ Real.exp Bstruct)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Bstruct)
    (hendpoint : 0 ≤ endpoint)
    (hE : preparedNestedFrontProjectionEnvelope exponent countConstants innerDepth
      (fun k : Slots => (preparedFiniteNestedForwardAllDegreeOuter k).val)
      (fun k : Slots => (slotStage k).val) native
      Bstruct gainLog stageLog endpoint ≤ E)
    (hNative : ∀ k : Slots, sampler.NativeDetection (slotDegree k)
      ((preparedFiniteForwardParameter exponent countConstants (slotStage k).val (slotSeed k) + Cslice) ^ Cslice)
      ((preparedFiniteForwardDetectorPolynomial cutoff).eval₂ (Nat.castRingHom ℝ)
        (allocatedModelTestLog
          (preparedFiniteForwardPairedSourcePrecision exponent Cdirect countConstants
            (slotStage k).val (preparedFiniteNestedForwardAllDegreeIsDirect k)
            (slotSeed k) gainLog stageLog)
          (preparedFiniteForwardWork exponent countConstants (slotStage k).val (slotSeed k))))
      (native k)
      (Real.exp (-(2 * preparedFiniteForwardModelPrecision exponent countConstants
        (slotStage k).val (slotSeed k) gainLog stageLog +
        4 * preparedFiniteForwardWork exponent countConstants (slotStage k).val (slotSeed k) + 8))))
    (hexcess :
      (FiniteProbabilityWeights.uniformFinset (integerBox N) sampler.integerBox_nonempty).excessMass
        (sampler.law.siteLaw (sampler.physicalBox hξ hmargin))
        (4 * ∏ j, earlyConstantDensityCap (Fintype.card (PreparedSamplerContinuous prep j))
          (preparedSamplerTransverse prep j) (R j) (Vtail j)) ≤
        6 * positiveProjectionAccuracy E)
    (hsize : ∀ i, Real.exp (preparedFiniteForwardCumulative exponent countConstants degree
      (seed outerInner.val Bstruct)) ≤ (N i : ℝ))
    (hrank : Real.exp (preparedFiniteForwardCumulative exponent countConstants degree
      (seed outerInner.val Bstruct)) ≤ rankThreshold)
    (hsampling : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) rankThreshold (U j) (poly j))
    (hτ : τ ≤ 1) (hσone : ∀ j, σ j ≤ 1)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v,
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hCbound : ∀ j, C j ≤ Real.exp chartLog) (hallow : chartLog + 1 ≤ Bstruct)
    (hRadius : ∀ j, R j = allocatedCommonProductRadius m Bstruct Bstruct) :
    sampler.DegreeSourceProfile degree p e := by
  have hA : 2 ≤ exponent :=
    (preparedFiniteForwardFrontProfileExponent_two_le e).trans hFrontExponent
  have hseed0 (o : ℕ) : 0 ≤ seed o Bstruct :=
    candidateNestedForwardSeed_nonneg exponent countConstants innerDepth o hBstruct
  have hseed (o : ℕ) : Bstruct ≤ seed o Bstruct :=
    le_candidateNestedForwardSeed exponent countConstants innerDepth o hA hBstruct
  have hX : (Fintype.card X : ℝ) ≤ Bstruct := by
    have h : Fintype.card X ≤ Fintype.card (X ⊕ (Σ j, (prep j).Coord)) := by
      rw [Fintype.card_sum]
      exact Nat.le_add_right _ _
    exact (Nat.cast_le.mpr h).trans htags
  obtain ⟨_, hI, hn⟩ := enlargedPreparedCommonSampler_dimensions prep Jalloc hM
  have hmnum : m ≤ enlargedPreparedCommonSamplerDimension m M Jalloc := by
    unfold enlargedPreparedCommonSamplerDimension
    omega
  have hcap := prepared_commonRadius_densityCap_nested_bound m exponent hCapExponent
    prep le_rfl M Jalloc hM Bstruct hBstruct hnum Vtail hVtail hprofile
    countConstants innerDepth outerFront.val 0
  have hcapR : 4 * ∏ j, earlyConstantDensityCap (Fintype.card (PreparedSamplerContinuous prep j))
      (preparedSamplerTransverse prep j) (R j) (Vtail j) ≤
      Real.exp (preparedFiniteForwardWork exponent countConstants 0 (seed outerFront.val Bstruct)) := by
    simpa only [hRadius] using hcap
  let kFront : Slots := (outerFront, 0, ⟨degree, Nat.lt_succ_of_le hdegree⟩, false)
  let entry := fun k : Slots => preparedFiniteForwardFrontProjectionPrecision
    (preparedFiniteForwardModelPrecision exponent countConstants (slotStage k).val
      (slotSeed k) gainLog stageLog)
    (preparedFiniteForwardWork exponent countConstants (slotStage k).val (slotSeed k)) (native k)
  have hentry : ∀ k, 0 ≤ entry k := by
    intro k
    have hsk := hseed (preparedFiniteNestedForwardAllDegreeOuter k).val
    exact preparedFiniteForwardFrontProjectionPrecision_nonneg
      (preparedFiniteForward_model_precision_bounds exponent countConstants (slotStage k).val
        (hseed0 _) ⟨hg.1, hg.2.trans hsk⟩ ⟨hs.1, hs.2.trans hsk⟩).1
      (preparedFiniteForwardWork_nonneg exponent countConstants (slotStage k).val (hseed0 _))
  have hprojection : entry kFront ≤ E := by
    have hsingle : entry kFront ≤ ∑ k, entry k :=
      Finset.single_le_sum (fun k _ => hentry k) (Finset.mem_univ kFront)
    have he : endpoint + 1 + ∑ k, entry k ≤ E := hE
    linarith only [hsingle, he, hendpoint]
  have hfrontDetection := hNative kFront
  simp only [kFront, preparedFiniteNestedForwardAllDegreeStage_slot,
    preparedFiniteNestedForwardAllDegreeDegree_slot, preparedFiniteNestedForwardAllDegreeSeed_slot,
    preparedFiniteNestedForwardAllDegreeIsDirect_slot, Fin.val_zero,
    preparedFiniteForwardParameter_zero, preparedFiniteForwardPairedSourcePrecision_model,
    preparedFiniteNestedSourceNative, preparedFiniteNestedSourceMaster_front] at hfrontDetection
  have hfrontProjection := hprojection
  simp only [entry, kFront, preparedFiniteNestedForwardAllDegreeStage_slot,
    preparedFiniteNestedForwardAllDegreeSeed_slot, Fin.val_zero,
    preparedFiniteNestedSourceNative, preparedFiniteNestedForwardAllDegreeDegree_slot,
    preparedFiniteNestedSourceMaster_front, preparedFiniteForwardFrontProjectionPrecision] at hfrontProjection
  let front := sampler.preparedFiniteForwardActualFrontSourceProfile cutoff exponent Cslice Cdirect
    countConstants hFrontExponent hCslice hSliceExponent (hdegree.trans hcutoff)
    (hseed0 _) hpFront ⟨hg.1, hg.2.trans (hseed _)⟩ ⟨hs.1, hs.2.trans (hseed _)⟩
    ⟨hBstruct, hseed _⟩ ⟨Nat.cast_nonneg _, hnum.trans (hseed _)⟩
    ⟨hBstruct, hseed _⟩ ⟨hQstride.1, hQstride.2.trans (hseed _)⟩
    (hvariables.trans (hseed _)) (hX.trans (hseed _)) (hG.trans (hseed _))
    hξ hmargin hcapR hfrontProjection hfrontDetection hexcess
  have hinnerDetection : ∀ r < degree, sampler.NativeDetection r
      ((preparedFiniteForwardParameter exponent countConstants r (seed outerInner.val Bstruct) + Cslice) ^ Cslice)
      ((preparedFiniteForwardDetectorPolynomial cutoff).eval₂ (Nat.castRingHom ℝ)
        (allocatedModelTestLog
          (preparedFiniteForwardPairedSourcePrecision exponent Cdirect countConstants r true
            (seed outerInner.val Bstruct) gainLog stageLog)
          (preparedFiniteForwardWork exponent countConstants r (seed outerInner.val Bstruct))))
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m r) (r + 1)
        (preparedFiniteForwardActualLocalMaster m G count (Fintype.card X)
          (preparedFiniteForwardDetectorPolynomial cutoff) exponent Cdirect countConstants r
          (seed outerInner.val Bstruct) gainLog stageLog Bstruct pnum Bstruct Qstride) Plate).nativeBudget
      (Real.exp (-(2 * preparedFiniteForwardModelPrecision exponent countConstants r
        (seed outerInner.val Bstruct) gainLog stageLog +
        4 * preparedFiniteForwardWork exponent countConstants r (seed outerInner.val Bstruct) + 8))) := by
    intro r hr
    have hi : r < innerDepth + 1 := Nat.lt_succ_of_le (hr.le.trans hdepth)
    have hd : r < cutoff + 1 := Nat.lt_succ_of_le (hr.le.trans hdegree)
    simpa only [preparedFiniteNestedForwardAllDegreeStage_slot,
      preparedFiniteNestedForwardAllDegreeDegree_slot, preparedFiniteNestedForwardAllDegreeSeed_slot,
      preparedFiniteNestedForwardAllDegreeIsDirect_slot, preparedFiniteNestedSourceNative,
      preparedFiniteNestedSourceMaster_direct] using
        hNative (outerInner, ⟨r, hi⟩, ⟨r, hd⟩, true)
  let inner := preparedFiniteForwardActualInnerSourceProfile sampler degree cutoff exponent
    Cprimitive Cslice Cdirect (seed outerInner.val Bstruct) gainLog stageLog Bstruct pnum
    Bstruct Qstride Plate rankThreshold (hseed0 _)
    ⟨hg.1, hg.2.trans (hseed _)⟩ ⟨hs.1, hs.2.trans (hseed _)⟩ hprimitive hdegree hcutoff
    ⟨hBstruct, hseed _⟩ ⟨Nat.cast_nonneg _, hnum.trans (hseed _)⟩
    ⟨hBstruct, hseed _⟩ ⟨hQstride.1, hQstride.2.trans (hseed _)⟩
    (hG.trans (hseed _)) hInnerExponent hInnerSlice hinnerDetection
    (htags.trans (hseed _)) ((Nat.cast_le.mpr hmnum).trans (hnum.trans (hseed _)))
    (hvariables.trans (hseed _)) hsize hrank hsampling
  have hstrong : ∀ r < degree, sampler.NativeDetection r
      (allocatedCandidateStageSlice degree m inner.Cprimitive
        (preparedFiniteForwardParameter inner.scheduleExponent countConstants r inner.x))
      (inner.pTest r) (inner.sourceNative r) (Real.exp (-(seed outerInner.val Bstruct)) / 2) := by
    intro r hr
    have hb0 : 0 ≤ preparedFiniteForwardParameter exponent countConstants r
        (seed outerInner.val Bstruct) :=
      preparedFiniteForwardParameter_nonneg exponent countConstants r (hseed0 _)
    have hCtwo : 2 ≤ Cslice :=
      (allocatedCandidateStageSlice_bounds degree m Cprimitive hb0).1.trans hInnerSlice
    have hslice : allocatedCandidateStageSlice degree m Cprimitive
        (preparedFiniteForwardParameter exponent countConstants r (seed outerInner.val Bstruct)) ≤
        (preparedFiniteForwardParameter exponent countConstants r (seed outerInner.val Bstruct) + Cslice) ^ Cslice := by
      unfold allocatedCandidateStageSlice
      apply (pow_le_pow_left₀ (add_nonneg hb0 (Nat.cast_nonneg _))
        (add_le_add le_rfl (Nat.cast_le.mpr hInnerSlice)) _).trans
      exact pow_le_pow_right₀ (by
        have hCtwoReal : (2 : ℝ) ≤ Cslice := Nat.cast_le.mpr hCtwo
        linarith only [hb0, hCtwoReal]) hInnerSlice
    exact AllocatedExternalCandidateSampler.NativeDetection.mono_tests sampler
      (hinnerDetection r hr) hslice le_rfl
      (preparedFiniteForwardFixedCenterThreshold_le_seed_half exponent countConstants r
        hA (hseed0 _) hg.1 hs.1)
  let innerStrong := inner.with_gain_detection (seed outerInner.val Bstruct)
    (hg.2.trans (hseed _)) le_rfl (fun _ => Real.exp (-(seed outerInner.val Bstruct)) / 2)
    (fun _ _ => div_nonneg (Real.exp_nonneg _) (by norm_num)) (fun _ _ => le_rfl) hstrong
  exact sampler.preparedCommonRadiusDegreeSourceProfile front innerStrong hpInner
    hτ hσone hpoly C hC hchart hCbound hallow hBstruct hvariables
    (fun j => (Nat.cast_le.mpr (hI j)).trans hnum)
    (fun j => (Nat.cast_le.mpr (hn j)).trans hnum) hRadius

noncomputable def preparedFiniteNestedDegreeSourceProfile_of_exponent
    (extra : ℕ) (outerFront outerInner : Fin (outerDepth + 1)) {degree e : ℕ}
    {p chartLog : ℝ}
    (hdegree : degree ≤ cutoff) (hcutoff : cutoff ≤ m) (hdepth : degree ≤ innerDepth)
    (hExponent : preparedFiniteNestedSourceExponent m cutoff e Cprimitive Cdirect extra ≤ exponent) :=
  let he := preparedFiniteNestedSourceExponent_bounds m cutoff e Cprimitive Cdirect extra exponent hExponent
  let hc := preparedFiniteNestedSourceSliceExponent_bounds m cutoff Cprimitive
  preparedFiniteNestedDegreeSourceProfile prep sampler outerDepth innerDepth cutoff exponent
    Cprimitive (preparedFiniteNestedSourceSliceExponent m cutoff Cprimitive) Cdirect M Jalloc
    Bstruct gainLog stageLog Qstride Plate E endpoint rankThreshold outerFront outerInner
    (e := e) (p := p) (chartLog := chartLog) hdegree hcutoff hdepth he.2.2.1 he.2.2.2.1
    (he.2.2.2.2.2 degree hdegree) hc.1 he.2.2.2.2.1 (hc.2 degree hdegree)

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

private theorem nestedSourceFullScalar_and_rec {a b : Prop} {α : Sort*}
    (f : a → b → α) (h : a ∧ b) : And.rec f h = f h.1 h.2 := by
  cases h
  rfl

variable {m : ℕ} {X₀ J₀ G X : Type} [Fintype G] [Fintype X]
    (prep : RankPreparationFamily X₀ J₀ m)
    {B : LayerSamplerAxis (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) → Type}
    [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ ((prep j).Coord → ℝ)}
    {b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ ((prep j).Coord → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern
      (Option (LayerSamplerVariables G (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice ((prep j).Coord)) (euclideanSubspace (U j)))]
    (sampler : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateSampler

local instance nestedDegreeSourceFullScalarsSiteNonempty : Nonempty sampler.Site := sampler.site_nonempty
local notation "countConstants" => degreeSourceCountConstants

variable (outerDepth innerDepth cutoff exponent Cprimitive Cslice Cdirect M Jalloc : ℕ)
    (Bstruct gainLog stageLog Qstride Plate E endpoint rankThreshold : ℝ)

local notation "Slots" => PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff
local notation "count" => Fintype.card (LayerSamplerVariables G
    (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) B)
local notation "pnum" => (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ)
local notation "seed" => candidateNestedForwardSeed exponent countConstants innerDepth
local notation "native" => preparedFiniteNestedSourceNative m G count (Fintype.card X)
    (preparedFiniteForwardDetectorPolynomial cutoff) exponent Cdirect countConstants
    Bstruct pnum Qstride gainLog stageLog Plate
local notation "slotSeed" => preparedFiniteNestedForwardAllDegreeSeed exponent countConstants Bstruct
local notation "slotStage" => preparedFiniteNestedForwardAllDegreeStage
local notation "slotDegree" => preparedFiniteNestedForwardAllDegreeDegree

attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection

theorem exists_preparedFiniteNestedDegreeSourceProfile_fullScalars
    (outerFront outerInner : Fin (outerDepth + 1)) {degree e : ℕ} {p chartLog : ℝ}
    (hdegree : degree ≤ cutoff) (hcutoff : cutoff ≤ m) (hdepth : degree ≤ innerDepth)
    (hFrontExponent : preparedFiniteForwardFrontProfileExponent e ≤ exponent)
    (hCapExponent : preparedCommonRadiusDensityCapNestedExponent m ≤ exponent)
    (hInnerExponent : allocatedCandidateForwardScheduleExponent degree m Cprimitive
      (preparedFiniteForwardInnerSourceExponent Cdirect
        (preparedFiniteForwardActualNativeBudgetExponent m
          (preparedFiniteForwardDetectorPolynomial cutoff))) 2 ≤ exponent)
    (hCslice : 1 ≤ Cslice) (hSliceExponent : Cslice + 1 ≤ exponent)
    (hInnerSlice : allocatedCandidateStageSliceExponent degree m Cprimitive ≤ Cslice)
    (hprimitive : 1 ≤ Cprimitive)
    (hBstruct : 0 ≤ Bstruct) (hg : gainLog ∈ Set.Icc 0 Bstruct)
    (hs : stageLog ∈ Set.Icc 0 Bstruct) (hQstride : Qstride ∈ Set.Icc 0 Bstruct)
    (hM : ∀ j, Fintype.card (prep j).Coord ≤ M) (hnum : pnum ≤ Bstruct)
    (hG : (Fintype.card G : ℝ) ≤ Bstruct)
    (htags : (Fintype.card (X ⊕ (Σ j, (prep j).Coord)) : ℝ) ≤ Bstruct)
    (hvariables : (count : ℝ) ≤ Bstruct)
    (hpFront : p ∈ Set.Icc 0 (seed outerFront.val Bstruct))
    (hpInner : p ≤ seed outerInner.val Bstruct)
    (hξ : ξ ≤ 1) (hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i)
    (Vtail : Fin m → ℝ≥0) (hVtail : ∀ j, (Vtail j : ℝ) ≤ Real.exp Bstruct)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Bstruct)
    (hendpoint : 0 ≤ endpoint)
    (hE : preparedNestedFrontProjectionEnvelope exponent countConstants innerDepth
      (fun k : Slots => (preparedFiniteNestedForwardAllDegreeOuter k).val)
      (fun k : Slots => (slotStage k).val) native
      Bstruct gainLog stageLog endpoint ≤ E)
    (hNative : ∀ k : Slots, sampler.NativeDetection (slotDegree k)
      ((preparedFiniteForwardParameter exponent countConstants (slotStage k).val (slotSeed k) + Cslice) ^ Cslice)
      ((preparedFiniteForwardDetectorPolynomial cutoff).eval₂ (Nat.castRingHom ℝ)
        (allocatedModelTestLog
          (preparedFiniteForwardPairedSourcePrecision exponent Cdirect countConstants
            (slotStage k).val (preparedFiniteNestedForwardAllDegreeIsDirect k)
            (slotSeed k) gainLog stageLog)
          (preparedFiniteForwardWork exponent countConstants (slotStage k).val (slotSeed k))))
      (native k)
      (Real.exp (-(2 * preparedFiniteForwardModelPrecision exponent countConstants
        (slotStage k).val (slotSeed k) gainLog stageLog +
        4 * preparedFiniteForwardWork exponent countConstants (slotStage k).val (slotSeed k) + 8))))
    (hexcess :
      (FiniteProbabilityWeights.uniformFinset (integerBox N) sampler.integerBox_nonempty).excessMass
        (sampler.law.siteLaw (sampler.physicalBox hξ hmargin))
        (4 * ∏ j, earlyConstantDensityCap (Fintype.card (PreparedSamplerContinuous prep j))
          (preparedSamplerTransverse prep j) (R j) (Vtail j)) ≤
        6 * positiveProjectionAccuracy E)
    (hsize : ∀ i, Real.exp (preparedFiniteForwardCumulative exponent countConstants degree
      (seed outerInner.val Bstruct)) ≤ (N i : ℝ))
    (hrank : Real.exp (preparedFiniteForwardCumulative exponent countConstants degree
      (seed outerInner.val Bstruct)) ≤ rankThreshold)
    (hsampling : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) rankThreshold (U j) (poly j))
    (hτ : τ ≤ 1) (hσone : ∀ j, σ j ≤ 1)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v,
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hCbound : ∀ j, C j ≤ Real.exp chartLog) (hallow : chartLog + 1 ≤ Bstruct)
    (hRadius : ∀ j, R j = allocatedCommonProductRadius m Bstruct Bstruct) :
    ∃ P : sampler.DegreeSourceProfile degree p e,
      P.inner.x = seed outerInner.val Bstruct ∧
      P.inner.gainLog = seed outerInner.val Bstruct ∧
      P.front.u = preparedFiniteForwardModelPrecision exponent countConstants 0
        (seed outerFront.val Bstruct) gainLog stageLog ∧
      P.front.pModel = preparedFiniteForwardWork exponent countConstants 0
        (seed outerFront.val Bstruct) ∧
      P.front.nativeBudget = native
        ((outerFront, 0, ⟨degree, Nat.lt_succ_of_le hdegree⟩, false) : Slots) ∧
      P.inner.Cprimitive = Cprimitive ∧
      P.inner.scheduleExponent = exponent ∧
      P.inner.Csource = preparedFiniteNestedSourceNativeExponent m cutoff Cdirect := by
  let P := preparedFiniteNestedDegreeSourceProfile prep sampler
    outerDepth innerDepth cutoff exponent Cprimitive Cslice Cdirect M Jalloc
    Bstruct gainLog stageLog Qstride Plate E endpoint rankThreshold outerFront outerInner
    hdegree hcutoff hdepth hFrontExponent hCapExponent hInnerExponent hCslice hSliceExponent
    hInnerSlice hprimitive hBstruct hg hs hQstride hM hnum hG htags hvariables hpFront hpInner
    hξ hmargin Vtail hVtail hprofile hendpoint hE hNative hexcess hsize hrank hsampling
    hτ hσone hpoly C hC hchart hCbound hallow hRadius
  refine ⟨P, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [P, preparedFiniteNestedDegreeSourceProfile,
    nestedSourceFullScalar_and_rec,
    preparedCommonRadiusDegreeSourceProfile, preparedFiniteForwardActualFrontSourceProfile,
    preparedFiniteForwardFrontSourceProfile, preparedFixedCenterFrontSourceProfile,
    InnerSourceProfile.with_gain_detection, InnerSourceProfile.raise_gain,
    preparedFiniteForwardActualInnerSourceProfile, preparedFiniteForwardInnerSourceProfile,
    preparedFiniteNestedSourceNative, preparedFiniteNestedForwardAllDegreeDegree_slot,
    preparedFiniteNestedSourceMaster_front, preparedFiniteNestedSourceNativeExponent]

theorem exists_preparedFiniteNestedDegreeSourceProfile_of_exponent_fullScalars
    (extra : ℕ)
    (outerFront outerInner : Fin (outerDepth + 1)) {degree e : ℕ} {p chartLog : ℝ}
    (hdegree : degree ≤ cutoff) (hcutoff : cutoff ≤ m) (hdepth : degree ≤ innerDepth)
    (hExponent : preparedFiniteNestedSourceExponent m cutoff e Cprimitive Cdirect extra ≤ exponent)
    (hprimitive : 1 ≤ Cprimitive)
    (hBstruct : 0 ≤ Bstruct) (hg : gainLog ∈ Set.Icc 0 Bstruct)
    (hs : stageLog ∈ Set.Icc 0 Bstruct) (hQstride : Qstride ∈ Set.Icc 0 Bstruct)
    (hM : ∀ j, Fintype.card (prep j).Coord ≤ M) (hnum : pnum ≤ Bstruct)
    (hG : (Fintype.card G : ℝ) ≤ Bstruct)
    (htags : (Fintype.card (X ⊕ (Σ j, (prep j).Coord)) : ℝ) ≤ Bstruct)
    (hvariables : (count : ℝ) ≤ Bstruct)
    (hpFront : p ∈ Set.Icc 0 (seed outerFront.val Bstruct))
    (hpInner : p ≤ seed outerInner.val Bstruct)
    (hξ : ξ ≤ 1) (hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i)
    (Vtail : Fin m → ℝ≥0) (hVtail : ∀ j, (Vtail j : ℝ) ≤ Real.exp Bstruct)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Bstruct)
    (hendpoint : 0 ≤ endpoint)
    (hE : preparedNestedFrontProjectionEnvelope exponent countConstants innerDepth
      (fun k : Slots => (preparedFiniteNestedForwardAllDegreeOuter k).val)
      (fun k : Slots => (slotStage k).val) native
      Bstruct gainLog stageLog endpoint ≤ E)
    (hNative : ∀ k : Slots, sampler.NativeDetection (slotDegree k)
      ((preparedFiniteForwardParameter exponent countConstants (slotStage k).val (slotSeed k) + (preparedFiniteNestedSourceSliceExponent m cutoff Cprimitive)) ^ (preparedFiniteNestedSourceSliceExponent m cutoff Cprimitive))
      ((preparedFiniteForwardDetectorPolynomial cutoff).eval₂ (Nat.castRingHom ℝ)
        (allocatedModelTestLog
          (preparedFiniteForwardPairedSourcePrecision exponent Cdirect countConstants
            (slotStage k).val (preparedFiniteNestedForwardAllDegreeIsDirect k)
            (slotSeed k) gainLog stageLog)
          (preparedFiniteForwardWork exponent countConstants (slotStage k).val (slotSeed k))))
      (native k)
      (Real.exp (-(2 * preparedFiniteForwardModelPrecision exponent countConstants
        (slotStage k).val (slotSeed k) gainLog stageLog +
        4 * preparedFiniteForwardWork exponent countConstants (slotStage k).val (slotSeed k) + 8))))
    (hexcess :
      (FiniteProbabilityWeights.uniformFinset (integerBox N) sampler.integerBox_nonempty).excessMass
        (sampler.law.siteLaw (sampler.physicalBox hξ hmargin))
        (4 * ∏ j, earlyConstantDensityCap (Fintype.card (PreparedSamplerContinuous prep j))
          (preparedSamplerTransverse prep j) (R j) (Vtail j)) ≤
        6 * positiveProjectionAccuracy E)
    (hsize : ∀ i, Real.exp (preparedFiniteForwardCumulative exponent countConstants degree
      (seed outerInner.val Bstruct)) ≤ (N i : ℝ))
    (hrank : Real.exp (preparedFiniteForwardCumulative exponent countConstants degree
      (seed outerInner.val Bstruct)) ≤ rankThreshold)
    (hsampling : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) rankThreshold (U j) (poly j))
    (hτ : τ ≤ 1) (hσone : ∀ j, σ j ≤ 1)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v,
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hCbound : ∀ j, C j ≤ Real.exp chartLog) (hallow : chartLog + 1 ≤ Bstruct)
    (hRadius : ∀ j, R j = allocatedCommonProductRadius m Bstruct Bstruct) :
    ∃ P : sampler.DegreeSourceProfile degree p e,
      P.inner.x = seed outerInner.val Bstruct ∧
      P.inner.gainLog = seed outerInner.val Bstruct ∧
      P.front.u = preparedFiniteForwardModelPrecision exponent countConstants 0
        (seed outerFront.val Bstruct) gainLog stageLog ∧
      P.front.pModel = preparedFiniteForwardWork exponent countConstants 0
        (seed outerFront.val Bstruct) ∧
      P.front.nativeBudget = native
        ((outerFront, 0, ⟨degree, Nat.lt_succ_of_le hdegree⟩, false) : Slots) ∧
      P.inner.Cprimitive = Cprimitive ∧
      P.inner.scheduleExponent = exponent ∧
      P.inner.Csource = preparedFiniteNestedSourceNativeExponent m cutoff Cdirect := by
  have he := preparedFiniteNestedSourceExponent_bounds m cutoff e Cprimitive Cdirect extra exponent hExponent
  have hc := preparedFiniteNestedSourceSliceExponent_bounds m cutoff Cprimitive
  exact exists_preparedFiniteNestedDegreeSourceProfile_fullScalars prep sampler
    outerDepth innerDepth cutoff exponent Cprimitive
    (preparedFiniteNestedSourceSliceExponent m cutoff Cprimitive) Cdirect M Jalloc
    Bstruct gainLog stageLog Qstride Plate E endpoint rankThreshold outerFront outerInner
    hdegree hcutoff hdepth he.2.2.1 he.2.2.2.1 (he.2.2.2.2.2 degree hdegree)
    hc.1 he.2.2.2.2.1 (hc.2 degree hdegree)
    hprimitive hBstruct hg hs hQstride hM hnum hG htags hvariables hpFront hpInner
    hξ hmargin Vtail hVtail hprofile hendpoint hE hNative hexcess hsize hrank hsampling
    hτ hσone hpoly C hC hchart hCbound hallow hRadius

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

private theorem nestedSourceScalar_and_rec {a b : Prop} {α : Sort*}
    (f : a → b → α) (h : a ∧ b) : And.rec f h = f h.1 h.2 := by
  cases h
  rfl

variable {m : ℕ} {X₀ J₀ G X : Type} [Fintype G] [Fintype X]
    (prep : RankPreparationFamily X₀ J₀ m)
    {B : LayerSamplerAxis (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) → Type}
    [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ ((prep j).Coord → ℝ)}
    {b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ ((prep j).Coord → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern
      (Option (LayerSamplerVariables G (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice ((prep j).Coord)) (euclideanSubspace (U j)))]
    (sampler : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateSampler

local instance nestedDegreeSourceScalarsSiteNonempty : Nonempty sampler.Site := sampler.site_nonempty
local notation "countConstants" => degreeSourceCountConstants

variable (outerDepth innerDepth cutoff exponent Cprimitive Cslice Cdirect M Jalloc : ℕ)
    (Bstruct gainLog stageLog Qstride Plate E endpoint rankThreshold : ℝ)

local notation "Slots" => PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff
local notation "count" => Fintype.card (LayerSamplerVariables G
    (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) B)
local notation "pnum" => (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ)
local notation "seed" => candidateNestedForwardSeed exponent countConstants innerDepth
local notation "native" => preparedFiniteNestedSourceNative m G count (Fintype.card X)
    (preparedFiniteForwardDetectorPolynomial cutoff) exponent Cdirect countConstants
    Bstruct pnum Qstride gainLog stageLog Plate
local notation "slotSeed" => preparedFiniteNestedForwardAllDegreeSeed exponent countConstants Bstruct
local notation "slotStage" => preparedFiniteNestedForwardAllDegreeStage
local notation "slotDegree" => preparedFiniteNestedForwardAllDegreeDegree

attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection

theorem exists_preparedFiniteNestedDegreeSourceProfile_scalars
    (outerFront outerInner : Fin (outerDepth + 1)) {degree e : ℕ} {p chartLog : ℝ}
    (hdegree : degree ≤ cutoff) (hcutoff : cutoff ≤ m) (hdepth : degree ≤ innerDepth)
    (hFrontExponent : preparedFiniteForwardFrontProfileExponent e ≤ exponent)
    (hCapExponent : preparedCommonRadiusDensityCapNestedExponent m ≤ exponent)
    (hInnerExponent : allocatedCandidateForwardScheduleExponent degree m Cprimitive
      (preparedFiniteForwardInnerSourceExponent Cdirect
        (preparedFiniteForwardActualNativeBudgetExponent m
          (preparedFiniteForwardDetectorPolynomial cutoff))) 2 ≤ exponent)
    (hCslice : 1 ≤ Cslice) (hSliceExponent : Cslice + 1 ≤ exponent)
    (hInnerSlice : allocatedCandidateStageSliceExponent degree m Cprimitive ≤ Cslice)
    (hprimitive : 1 ≤ Cprimitive)
    (hBstruct : 0 ≤ Bstruct) (hg : gainLog ∈ Set.Icc 0 Bstruct)
    (hs : stageLog ∈ Set.Icc 0 Bstruct) (hQstride : Qstride ∈ Set.Icc 0 Bstruct)
    (hM : ∀ j, Fintype.card (prep j).Coord ≤ M) (hnum : pnum ≤ Bstruct)
    (hG : (Fintype.card G : ℝ) ≤ Bstruct)
    (htags : (Fintype.card (X ⊕ (Σ j, (prep j).Coord)) : ℝ) ≤ Bstruct)
    (hvariables : (count : ℝ) ≤ Bstruct)
    (hpFront : p ∈ Set.Icc 0 (seed outerFront.val Bstruct))
    (hpInner : p ≤ seed outerInner.val Bstruct)
    (hξ : ξ ≤ 1) (hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i)
    (Vtail : Fin m → ℝ≥0) (hVtail : ∀ j, (Vtail j : ℝ) ≤ Real.exp Bstruct)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Bstruct)
    (hendpoint : 0 ≤ endpoint)
    (hE : preparedNestedFrontProjectionEnvelope exponent countConstants innerDepth
      (fun k : Slots => (preparedFiniteNestedForwardAllDegreeOuter k).val)
      (fun k : Slots => (slotStage k).val) native
      Bstruct gainLog stageLog endpoint ≤ E)
    (hNative : ∀ k : Slots, sampler.NativeDetection (slotDegree k)
      ((preparedFiniteForwardParameter exponent countConstants (slotStage k).val (slotSeed k) + Cslice) ^ Cslice)
      ((preparedFiniteForwardDetectorPolynomial cutoff).eval₂ (Nat.castRingHom ℝ)
        (allocatedModelTestLog
          (preparedFiniteForwardPairedSourcePrecision exponent Cdirect countConstants
            (slotStage k).val (preparedFiniteNestedForwardAllDegreeIsDirect k)
            (slotSeed k) gainLog stageLog)
          (preparedFiniteForwardWork exponent countConstants (slotStage k).val (slotSeed k))))
      (native k)
      (Real.exp (-(2 * preparedFiniteForwardModelPrecision exponent countConstants
        (slotStage k).val (slotSeed k) gainLog stageLog +
        4 * preparedFiniteForwardWork exponent countConstants (slotStage k).val (slotSeed k) + 8))))
    (hexcess :
      (FiniteProbabilityWeights.uniformFinset (integerBox N) sampler.integerBox_nonempty).excessMass
        (sampler.law.siteLaw (sampler.physicalBox hξ hmargin))
        (4 * ∏ j, earlyConstantDensityCap (Fintype.card (PreparedSamplerContinuous prep j))
          (preparedSamplerTransverse prep j) (R j) (Vtail j)) ≤
        6 * positiveProjectionAccuracy E)
    (hsize : ∀ i, Real.exp (preparedFiniteForwardCumulative exponent countConstants degree
      (seed outerInner.val Bstruct)) ≤ (N i : ℝ))
    (hrank : Real.exp (preparedFiniteForwardCumulative exponent countConstants degree
      (seed outerInner.val Bstruct)) ≤ rankThreshold)
    (hsampling : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) rankThreshold (U j) (poly j))
    (hτ : τ ≤ 1) (hσone : ∀ j, σ j ≤ 1)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v,
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hCbound : ∀ j, C j ≤ Real.exp chartLog) (hallow : chartLog + 1 ≤ Bstruct)
    (hRadius : ∀ j, R j = allocatedCommonProductRadius m Bstruct Bstruct) :
    ∃ P : sampler.DegreeSourceProfile degree p e,
      P.inner.x = seed outerInner.val Bstruct ∧
      P.inner.gainLog = seed outerInner.val Bstruct ∧
      P.front.u = preparedFiniteForwardModelPrecision exponent countConstants 0
        (seed outerFront.val Bstruct) gainLog stageLog ∧
      P.front.pModel = preparedFiniteForwardWork exponent countConstants 0
        (seed outerFront.val Bstruct) ∧
      P.front.nativeBudget = native
        ((outerFront, 0, ⟨degree, Nat.lt_succ_of_le hdegree⟩, false) : Slots) := by
  let P := preparedFiniteNestedDegreeSourceProfile prep sampler
    outerDepth innerDepth cutoff exponent Cprimitive Cslice Cdirect M Jalloc
    Bstruct gainLog stageLog Qstride Plate E endpoint rankThreshold outerFront outerInner
    hdegree hcutoff hdepth hFrontExponent hCapExponent hInnerExponent hCslice hSliceExponent
    hInnerSlice hprimitive hBstruct hg hs hQstride hM hnum hG htags hvariables hpFront hpInner
    hξ hmargin Vtail hVtail hprofile hendpoint hE hNative hexcess hsize hrank hsampling
    hτ hσone hpoly C hC hchart hCbound hallow hRadius
  refine ⟨P, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [P, preparedFiniteNestedDegreeSourceProfile,
    nestedSourceScalar_and_rec,
    preparedCommonRadiusDegreeSourceProfile, preparedFiniteForwardActualFrontSourceProfile,
    preparedFiniteForwardFrontSourceProfile, preparedFixedCenterFrontSourceProfile,
    InnerSourceProfile.with_gain_detection, InnerSourceProfile.raise_gain,
    preparedFiniteForwardActualInnerSourceProfile, preparedFiniteForwardInnerSourceProfile,
    preparedFiniteNestedSourceNative, preparedFiniteNestedForwardAllDegreeDegree_slot,
    preparedFiniteNestedSourceMaster_front]

theorem exists_preparedFiniteNestedDegreeSourceProfile_of_exponent_scalars
    (extra : ℕ)
    (outerFront outerInner : Fin (outerDepth + 1)) {degree e : ℕ} {p chartLog : ℝ}
    (hdegree : degree ≤ cutoff) (hcutoff : cutoff ≤ m) (hdepth : degree ≤ innerDepth)
    (hExponent : preparedFiniteNestedSourceExponent m cutoff e Cprimitive Cdirect extra ≤ exponent)
    (hprimitive : 1 ≤ Cprimitive)
    (hBstruct : 0 ≤ Bstruct) (hg : gainLog ∈ Set.Icc 0 Bstruct)
    (hs : stageLog ∈ Set.Icc 0 Bstruct) (hQstride : Qstride ∈ Set.Icc 0 Bstruct)
    (hM : ∀ j, Fintype.card (prep j).Coord ≤ M) (hnum : pnum ≤ Bstruct)
    (hG : (Fintype.card G : ℝ) ≤ Bstruct)
    (htags : (Fintype.card (X ⊕ (Σ j, (prep j).Coord)) : ℝ) ≤ Bstruct)
    (hvariables : (count : ℝ) ≤ Bstruct)
    (hpFront : p ∈ Set.Icc 0 (seed outerFront.val Bstruct))
    (hpInner : p ≤ seed outerInner.val Bstruct)
    (hξ : ξ ≤ 1) (hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i)
    (Vtail : Fin m → ℝ≥0) (hVtail : ∀ j, (Vtail j : ℝ) ≤ Real.exp Bstruct)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Bstruct)
    (hendpoint : 0 ≤ endpoint)
    (hE : preparedNestedFrontProjectionEnvelope exponent countConstants innerDepth
      (fun k : Slots => (preparedFiniteNestedForwardAllDegreeOuter k).val)
      (fun k : Slots => (slotStage k).val) native
      Bstruct gainLog stageLog endpoint ≤ E)
    (hNative : ∀ k : Slots, sampler.NativeDetection (slotDegree k)
      ((preparedFiniteForwardParameter exponent countConstants (slotStage k).val (slotSeed k) + (preparedFiniteNestedSourceSliceExponent m cutoff Cprimitive)) ^ (preparedFiniteNestedSourceSliceExponent m cutoff Cprimitive))
      ((preparedFiniteForwardDetectorPolynomial cutoff).eval₂ (Nat.castRingHom ℝ)
        (allocatedModelTestLog
          (preparedFiniteForwardPairedSourcePrecision exponent Cdirect countConstants
            (slotStage k).val (preparedFiniteNestedForwardAllDegreeIsDirect k)
            (slotSeed k) gainLog stageLog)
          (preparedFiniteForwardWork exponent countConstants (slotStage k).val (slotSeed k))))
      (native k)
      (Real.exp (-(2 * preparedFiniteForwardModelPrecision exponent countConstants
        (slotStage k).val (slotSeed k) gainLog stageLog +
        4 * preparedFiniteForwardWork exponent countConstants (slotStage k).val (slotSeed k) + 8))))
    (hexcess :
      (FiniteProbabilityWeights.uniformFinset (integerBox N) sampler.integerBox_nonempty).excessMass
        (sampler.law.siteLaw (sampler.physicalBox hξ hmargin))
        (4 * ∏ j, earlyConstantDensityCap (Fintype.card (PreparedSamplerContinuous prep j))
          (preparedSamplerTransverse prep j) (R j) (Vtail j)) ≤
        6 * positiveProjectionAccuracy E)
    (hsize : ∀ i, Real.exp (preparedFiniteForwardCumulative exponent countConstants degree
      (seed outerInner.val Bstruct)) ≤ (N i : ℝ))
    (hrank : Real.exp (preparedFiniteForwardCumulative exponent countConstants degree
      (seed outerInner.val Bstruct)) ≤ rankThreshold)
    (hsampling : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) rankThreshold (U j) (poly j))
    (hτ : τ ≤ 1) (hσone : ∀ j, σ j ≤ 1)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v,
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hCbound : ∀ j, C j ≤ Real.exp chartLog) (hallow : chartLog + 1 ≤ Bstruct)
    (hRadius : ∀ j, R j = allocatedCommonProductRadius m Bstruct Bstruct) :
    ∃ P : sampler.DegreeSourceProfile degree p e,
      P.inner.x = seed outerInner.val Bstruct ∧
      P.inner.gainLog = seed outerInner.val Bstruct ∧
      P.front.u = preparedFiniteForwardModelPrecision exponent countConstants 0
        (seed outerFront.val Bstruct) gainLog stageLog ∧
      P.front.pModel = preparedFiniteForwardWork exponent countConstants 0
        (seed outerFront.val Bstruct) ∧
      P.front.nativeBudget = native
        ((outerFront, 0, ⟨degree, Nat.lt_succ_of_le hdegree⟩, false) : Slots) := by
  have he := preparedFiniteNestedSourceExponent_bounds m cutoff e Cprimitive Cdirect extra exponent hExponent
  have hc := preparedFiniteNestedSourceSliceExponent_bounds m cutoff Cprimitive
  exact exists_preparedFiniteNestedDegreeSourceProfile_scalars prep sampler
    outerDepth innerDepth cutoff exponent Cprimitive
    (preparedFiniteNestedSourceSliceExponent m cutoff Cprimitive) Cdirect M Jalloc
    Bstruct gainLog stageLog Qstride Plate E endpoint rankThreshold outerFront outerInner
    hdegree hcutoff hdepth he.2.2.1 he.2.2.2.1 (he.2.2.2.2.2 degree hdegree)
    hc.1 he.2.2.2.2.1 (hc.2 degree hdegree)
    hprimitive hBstruct hg hs hQstride hM hnum hG htags hvariables hpFront hpInner
    hξ hmargin Vtail hVtail hprofile hendpoint hE hNative hexcess hsize hrank hsampling
    hτ hσone hpoly C hC hchart hCbound hallow hRadius

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

end OAI
