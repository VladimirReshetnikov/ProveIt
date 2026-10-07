import OAI.Combinatorics.Progressions.Estimates.AllocatedCandidateInnerSourceGain
import OAI.Combinatorics.Progressions.Estimates.PreparedRelativePositiveNativeRuleCanonical
import OAI.Combinatorics.Progressions.Estimates.PreparedScalarNestedPowerDetection
import OAI.Combinatorics.Progressions.Geometry.PreparedScalarSpatialWidthPower

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin 0 → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin 0 → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin 0 → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

namespace AllocatedExternalCandidateSampler

variable (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

local instance zeroLayerNestedDegreeSiteNonempty : Nonempty A.Site := A.site_nonempty
local notation "countConstants" => degreeSourceCountConstants

variable (q outerDepth innerDepth cutoff exponent Cprimitive Cslice Cdirect : ℕ)
    (Bstruct gainLog stageLog Qstride Plate : ℝ)
local notation "Slots" => PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff
local notation "count" => Fintype.card (LayerSamplerVariables G I n B)
local notation "pnum" => (Fintype.card G : ℝ)
local notation "seed" => candidateNestedForwardSeed exponent countConstants innerDepth
local notation "native" => preparedFiniteNestedSourceNative q G count (Fintype.card X)
    (preparedFiniteForwardDetectorPolynomial cutoff) exponent Cdirect countConstants
    Bstruct pnum Qstride gainLog stageLog Plate
local notation "slotSeed" => preparedFiniteNestedForwardAllDegreeSeed exponent countConstants Bstruct
local notation "slotStage" => preparedFiniteNestedForwardAllDegreeStage
local notation "slotDegree" => preparedFiniteNestedForwardAllDegreeDegree
attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection

noncomputable def zeroLayerNestedDegreeSourceProfile
    (outerFront outerInner : Fin (outerDepth + 1)) {degree e : ℕ} {p : ℝ}
    (hdegree : degree ≤ cutoff) (hcutoff : cutoff ≤ q) (hdepth : degree ≤ innerDepth)
    (hFrontExponent : preparedFiniteForwardFrontProfileExponent e ≤ exponent)
    (hInnerExponent : allocatedCandidateForwardScheduleExponent degree 0 Cprimitive
      (preparedFiniteForwardInnerSourceExponent Cdirect
        (preparedFiniteForwardActualNativeBudgetExponent q
          (preparedFiniteForwardDetectorPolynomial cutoff))) 2 ≤ exponent)
    (hCslice : 1 ≤ Cslice) (hSliceExponent : Cslice + 1 ≤ exponent)
    (hInnerSlice : allocatedCandidateStageSliceExponent degree 0 Cprimitive ≤ Cslice)
    (hprimitive : 1 ≤ Cprimitive)
    (hBstruct : 0 ≤ Bstruct) (hg : gainLog ∈ Set.Icc 0 Bstruct)
    (hs : stageLog ∈ Set.Icc 0 Bstruct) (hQstride : Qstride ∈ Set.Icc 0 Bstruct)
    (hG : (Fintype.card G : ℝ) ≤ Bstruct)
    (hX : (Fintype.card X : ℝ) ≤ Bstruct)
    (hpFront : p ∈ Set.Icc 0 (seed outerFront.val Bstruct))
    (hpInner : p ≤ seed outerInner.val Bstruct)
    (hξ : ξ ≤ 1)
    {surplus L : ℝ} (hsurplus : 0 < surplus) (hsurplus1 : surplus ≤ 1)
    (htrim : τ = unconditionedSpatialTrimFraction (Fintype.card X) surplus)
    (hN : ∀ i, unconditionedSpatialWidthCutoff
      (allocatedExternalCandidateRootBudget B U b S) τ L ≤ (N i : ℝ))
    (hNative : ∀ k : Slots, A.NativeDetection (slotDegree k)
      ((preparedFiniteForwardParameter exponent countConstants (slotStage k).val (slotSeed k) + Cslice) ^ Cslice)
      ((preparedFiniteForwardDetectorPolynomial cutoff).eval₂ (Nat.castRingHom ℝ)
        (allocatedModelTestLog
          (preparedFiniteForwardPairedSourcePrecision exponent Cdirect countConstants
            (slotStage k).val (preparedFiniteNestedForwardAllDegreeIsDirect k)
            (slotSeed k) gainLog stageLog)
          (preparedFiniteForwardWork exponent countConstants (slotStage k).val (slotSeed k))))
      (native k)
      (preparedFiniteNestedForwardFixedCenterThreshold exponent countConstants Bstruct gainLog stageLog k))
    (hsize : ∀ i, Real.exp (preparedFiniteForwardCumulative exponent countConstants degree
      (seed outerInner.val Bstruct)) ≤ (N i : ℝ)) :
    A.DegreeSourceProfile degree p e := by
  have hA : 2 ≤ exponent :=
    (preparedFiniteForwardFrontProfileExponent_two_le e).trans hFrontExponent
  have hseed0 (o : ℕ) : 0 ≤ seed o Bstruct :=
    candidateNestedForwardSeed_nonneg exponent countConstants innerDepth o hBstruct
  have hseed (o : ℕ) : Bstruct ≤ seed o Bstruct :=
    le_candidateNestedForwardSeed exponent countConstants innerDepth o hA hBstruct
  have hvariables : (count : ℝ) ≤ Bstruct := by
    simpa only [zeroLayerVariables_card] using hG
  have htags : (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ Bstruct := by
    simpa using hX
  let kFront : Slots := (outerFront, 0, ⟨degree, Nat.lt_succ_of_le hdegree⟩, false)
  have hfrontDetection := hNative kFront
  simp only [kFront, preparedFiniteNestedForwardAllDegreeStage_slot,
    preparedFiniteNestedForwardAllDegreeDegree_slot,
    preparedFiniteNestedForwardAllDegreeIsDirect_slot, Fin.val_zero,
    preparedFiniteForwardParameter_zero, preparedFiniteForwardPairedSourcePrecision_model,
    preparedFiniteNestedSourceNative, preparedFiniteNestedSourceMaster_front,
    preparedFiniteNestedForwardFixedCenterThreshold, preparedFiniteNestedForwardAllDegreeSeed] at hfrontDetection
  let front := A.zeroLayerForwardFrontSourceProfile q cutoff exponent Cslice Cdirect
    countConstants hFrontExponent hCslice hSliceExponent (hdegree.trans hcutoff)
    (hseed0 _) hpFront ⟨hg.1, hg.2.trans (hseed _)⟩ ⟨hs.1, hs.2.trans (hseed _)⟩
    ⟨hBstruct, hseed _⟩ ⟨Nat.cast_nonneg _, hG.trans (hseed _)⟩
    ⟨hBstruct, hseed _⟩ ⟨hQstride.1, hQstride.2.trans (hseed _)⟩
    (hvariables.trans (hseed _)) (hX.trans (hseed _)) (hG.trans (hseed _))
    hξ hsurplus hsurplus1 htrim hN hfrontDetection
  have hinnerDetection : ∀ r < degree, A.NativeDetection r
      ((preparedFiniteForwardParameter exponent countConstants r (seed outerInner.val Bstruct) + Cslice) ^ Cslice)
      ((preparedFiniteForwardDetectorPolynomial cutoff).eval₂ (Nat.castRingHom ℝ)
        (allocatedModelTestLog
          (preparedFiniteForwardPairedSourcePrecision exponent Cdirect countConstants r true
            (seed outerInner.val Bstruct) gainLog stageLog)
          (preparedFiniteForwardWork exponent countConstants r (seed outerInner.val Bstruct))))
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants q r) (r + 1)
        (preparedFiniteForwardActualLocalMaster q G count (Fintype.card X)
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
      preparedFiniteNestedSourceMaster_direct, preparedFiniteNestedForwardFixedCenterThreshold,
      preparedFiniteNestedForwardAllDegreeSeed] using
        hNative (outerInner, ⟨r, hi⟩, ⟨r, hd⟩, true)
  let rankThreshold := Real.exp (preparedFiniteForwardCumulative exponent countConstants degree
    (seed outerInner.val Bstruct))
  let inner := preparedFiniteForwardActualResourceLayerInnerSourceProfile A q degree cutoff exponent
    Cprimitive Cslice Cdirect (seed outerInner.val Bstruct) gainLog stageLog Bstruct pnum
    Bstruct Qstride Plate rankThreshold (hseed0 _)
    ⟨hg.1, hg.2.trans (hseed _)⟩ ⟨hs.1, hs.2.trans (hseed _)⟩ hprimitive hdegree hcutoff
    ⟨hBstruct, hseed _⟩ ⟨Nat.cast_nonneg _, hG.trans (hseed _)⟩
    ⟨hBstruct, hseed _⟩ ⟨hQstride.1, hQstride.2.trans (hseed _)⟩
    (hG.trans (hseed _)) hInnerExponent hInnerSlice hinnerDetection
    (htags.trans (hseed _)) (by simpa using hseed0 outerInner.val)
    (hvariables.trans (hseed _)) hsize le_rfl (fun j => Fin.elim0 j)
  have hstrong : ∀ r < degree, A.NativeDetection r
      (allocatedCandidateStageSlice degree 0 inner.Cprimitive
        (preparedFiniteForwardParameter inner.scheduleExponent countConstants r inner.x))
      (inner.pTest r) (inner.sourceNative r) (Real.exp (-(seed outerInner.val Bstruct)) / 2) := by
    intro r hr
    have hb0 : 0 ≤ preparedFiniteForwardParameter exponent countConstants r
        (seed outerInner.val Bstruct) :=
      preparedFiniteForwardParameter_nonneg exponent countConstants r (hseed0 _)
    have hCtwo : 2 ≤ Cslice :=
      (allocatedCandidateStageSlice_bounds degree 0 Cprimitive hb0).1.trans hInnerSlice
    have hslice : allocatedCandidateStageSlice degree 0 Cprimitive
        (preparedFiniteForwardParameter exponent countConstants r (seed outerInner.val Bstruct)) ≤
        (preparedFiniteForwardParameter exponent countConstants r (seed outerInner.val Bstruct) + Cslice) ^ Cslice := by
      unfold allocatedCandidateStageSlice
      apply (pow_le_pow_left₀ (add_nonneg hb0 (Nat.cast_nonneg _))
        (add_le_add le_rfl (Nat.cast_le.mpr hInnerSlice)) _).trans
      exact pow_le_pow_right₀ (by
        have hCtwoReal : (2 : ℝ) ≤ Cslice := Nat.cast_le.mpr hCtwo
        linarith only [hb0, hCtwoReal]) hInnerSlice
    exact AllocatedExternalCandidateSampler.NativeDetection.mono_tests A
      (hinnerDetection r hr) hslice le_rfl
      (preparedFiniteForwardFixedCenterThreshold_le_seed_half exponent countConstants r
        hA (hseed0 _) hg.1 hs.1)
  let innerStrong := inner.with_gain_detection (seed outerInner.val Bstruct)
    (hg.2.trans (hseed _)) le_rfl (fun _ => Real.exp (-(seed outerInner.val Bstruct)) / 2)
    (fun _ _ => div_nonneg (Real.exp_nonneg _) (by norm_num)) (fun _ _ => le_rfl) hstrong
  have hτ : τ ≤ 1 := by
    rw [htrim]
    exact (unconditionedSpatialTrimFraction_bounds (Fintype.card X) hsurplus hsurplus1).2.1.trans (by norm_num)
  exact A.zeroLayerDegreeSourceProfile front innerStrong hpInner hτ

noncomputable def zeroLayerNestedDegreeSourceProfile_of_exponent
    (extra : ℕ) (outerFront outerInner : Fin (outerDepth + 1)) {degree e : ℕ} {p : ℝ}
    (hdegree : degree ≤ cutoff) (hcutoff : cutoff ≤ q) (hdepth : degree ≤ innerDepth)
    (hExponent : preparedFiniteNestedResourceLayerSourceExponent 0 q cutoff e
      Cprimitive Cdirect extra ≤ exponent) :=
  let he := preparedFiniteNestedResourceLayerSourceExponent_bounds 0 q cutoff e
    Cprimitive Cdirect extra exponent hExponent
  let hc := preparedFiniteNestedResourceLayerSourceSliceExponent_bounds 0 cutoff Cprimitive
  A.zeroLayerNestedDegreeSourceProfile q outerDepth innerDepth cutoff exponent Cprimitive
    (preparedFiniteNestedSourceSliceExponent 0 cutoff Cprimitive) Cdirect
    Bstruct gainLog stageLog Qstride Plate outerFront outerInner
    (p := p) hdegree hcutoff hdepth he.2.2.1 (he.2.2.2.2 degree hdegree)
    hc.1 he.2.2.2.1 (hc.2 degree hdegree)

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin 0 → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin 0 → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin 0 → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

namespace AllocatedExternalCandidateSampler

variable (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

local instance zeroLayerNestedDegreeScalarsSiteNonempty : Nonempty A.Site := A.site_nonempty
local notation "countConstants" => degreeSourceCountConstants

variable (q outerDepth innerDepth cutoff exponent Cprimitive Cslice Cdirect : ℕ)
    (Bstruct gainLog stageLog Qstride Plate : ℝ)
local notation "Slots" => PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff
local notation "count" => Fintype.card (LayerSamplerVariables G I n B)
local notation "pnum" => (Fintype.card G : ℝ)
local notation "seed" => candidateNestedForwardSeed exponent countConstants innerDepth
local notation "native" => preparedFiniteNestedSourceNative q G count (Fintype.card X)
    (preparedFiniteForwardDetectorPolynomial cutoff) exponent Cdirect countConstants
    Bstruct pnum Qstride gainLog stageLog Plate
local notation "slotSeed" => preparedFiniteNestedForwardAllDegreeSeed exponent countConstants Bstruct
local notation "slotStage" => preparedFiniteNestedForwardAllDegreeStage
local notation "slotDegree" => preparedFiniteNestedForwardAllDegreeDegree
attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection

theorem exists_zeroLayerNestedDegreeSourceProfile_scalars
    (outerFront outerInner : Fin (outerDepth + 1)) {degree e : ℕ} {p : ℝ}
    (hdegree : degree ≤ cutoff) (hcutoff : cutoff ≤ q) (hdepth : degree ≤ innerDepth)
    (hFrontExponent : preparedFiniteForwardFrontProfileExponent e ≤ exponent)
    (hInnerExponent : allocatedCandidateForwardScheduleExponent degree 0 Cprimitive
      (preparedFiniteForwardInnerSourceExponent Cdirect
        (preparedFiniteForwardActualNativeBudgetExponent q
          (preparedFiniteForwardDetectorPolynomial cutoff))) 2 ≤ exponent)
    (hCslice : 1 ≤ Cslice) (hSliceExponent : Cslice + 1 ≤ exponent)
    (hInnerSlice : allocatedCandidateStageSliceExponent degree 0 Cprimitive ≤ Cslice)
    (hprimitive : 1 ≤ Cprimitive)
    (hBstruct : 0 ≤ Bstruct) (hg : gainLog ∈ Set.Icc 0 Bstruct)
    (hs : stageLog ∈ Set.Icc 0 Bstruct) (hQstride : Qstride ∈ Set.Icc 0 Bstruct)
    (hG : (Fintype.card G : ℝ) ≤ Bstruct)
    (hX : (Fintype.card X : ℝ) ≤ Bstruct)
    (hpFront : p ∈ Set.Icc 0 (seed outerFront.val Bstruct))
    (hpInner : p ≤ seed outerInner.val Bstruct)
    (hξ : ξ ≤ 1)
    {surplus L : ℝ} (hsurplus : 0 < surplus) (hsurplus1 : surplus ≤ 1)
    (htrim : τ = unconditionedSpatialTrimFraction (Fintype.card X) surplus)
    (hN : ∀ i, unconditionedSpatialWidthCutoff
      (allocatedExternalCandidateRootBudget B U b S) τ L ≤ (N i : ℝ))
    (hNative : ∀ k : Slots, A.NativeDetection (slotDegree k)
      ((preparedFiniteForwardParameter exponent countConstants (slotStage k).val (slotSeed k) + Cslice) ^ Cslice)
      ((preparedFiniteForwardDetectorPolynomial cutoff).eval₂ (Nat.castRingHom ℝ)
        (allocatedModelTestLog
          (preparedFiniteForwardPairedSourcePrecision exponent Cdirect countConstants
            (slotStage k).val (preparedFiniteNestedForwardAllDegreeIsDirect k)
            (slotSeed k) gainLog stageLog)
          (preparedFiniteForwardWork exponent countConstants (slotStage k).val (slotSeed k))))
      (native k)
      (preparedFiniteNestedForwardFixedCenterThreshold exponent countConstants Bstruct gainLog stageLog k))
    (hsize : ∀ i, Real.exp (preparedFiniteForwardCumulative exponent countConstants degree
      (seed outerInner.val Bstruct)) ≤ (N i : ℝ)) :
    ∃ P : A.DegreeSourceProfile degree p e,
      P.inner.x = seed outerInner.val Bstruct ∧
      P.inner.gainLog = seed outerInner.val Bstruct ∧
      P.front.u = preparedFiniteForwardModelPrecision exponent countConstants 0
        (seed outerFront.val Bstruct) gainLog stageLog ∧
      P.front.pModel = preparedFiniteForwardWork exponent countConstants 0
        (seed outerFront.val Bstruct) ∧
      P.front.nativeBudget = native
        ((outerFront, 0, ⟨degree, Nat.lt_succ_of_le hdegree⟩, false) : Slots) := by
  let P := A.zeroLayerNestedDegreeSourceProfile q outerDepth innerDepth cutoff exponent Cprimitive
    Cslice Cdirect Bstruct gainLog stageLog Qstride Plate outerFront outerInner
    hdegree hcutoff hdepth hFrontExponent hInnerExponent hCslice hSliceExponent hInnerSlice
    hprimitive hBstruct hg hs hQstride hG hX hpFront hpInner hξ hsurplus hsurplus1 htrim hN
    hNative hsize
  refine ⟨P, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [P, zeroLayerNestedDegreeSourceProfile, zeroLayerDegreeSourceProfile,
    zeroLayerForwardFrontSourceProfile, preparedFiniteForwardFrontSourceProfile,
    preparedFixedCenterFrontSourceProfile, InnerSourceProfile.with_gain_detection,
    InnerSourceProfile.raise_gain, preparedFiniteForwardActualResourceLayerInnerSourceProfile,
    preparedFiniteForwardResourceLayerInnerSourceProfile,
    preparedFiniteNestedSourceNative, preparedFiniteNestedForwardAllDegreeDegree_slot,
    preparedFiniteNestedSourceMaster_front]

theorem exists_zeroLayerNestedDegreeSourceProfile_of_exponent_scalars
    (extra : ℕ) (outerFront outerInner : Fin (outerDepth + 1)) {degree e : ℕ} {p : ℝ}
    (hdegree : degree ≤ cutoff) (hcutoff : cutoff ≤ q) (hdepth : degree ≤ innerDepth)
    (hExponent : preparedFiniteNestedResourceLayerSourceExponent 0 q cutoff e
      Cprimitive Cdirect extra ≤ exponent)
    (hprimitive : 1 ≤ Cprimitive)
    (hBstruct : 0 ≤ Bstruct) (hg : gainLog ∈ Set.Icc 0 Bstruct)
    (hs : stageLog ∈ Set.Icc 0 Bstruct) (hQstride : Qstride ∈ Set.Icc 0 Bstruct)
    (hG : (Fintype.card G : ℝ) ≤ Bstruct)
    (hX : (Fintype.card X : ℝ) ≤ Bstruct)
    (hpFront : p ∈ Set.Icc 0 (seed outerFront.val Bstruct))
    (hpInner : p ≤ seed outerInner.val Bstruct)
    (hξ : ξ ≤ 1)
    {surplus L : ℝ} (hsurplus : 0 < surplus) (hsurplus1 : surplus ≤ 1)
    (htrim : τ = unconditionedSpatialTrimFraction (Fintype.card X) surplus)
    (hN : ∀ i, unconditionedSpatialWidthCutoff
      (allocatedExternalCandidateRootBudget B U b S) τ L ≤ (N i : ℝ))
    (hNative : ∀ k : Slots, A.NativeDetection (slotDegree k)
      ((preparedFiniteForwardParameter exponent countConstants (slotStage k).val (slotSeed k) + (preparedFiniteNestedSourceSliceExponent 0 cutoff Cprimitive)) ^
        (preparedFiniteNestedSourceSliceExponent 0 cutoff Cprimitive))
      ((preparedFiniteForwardDetectorPolynomial cutoff).eval₂ (Nat.castRingHom ℝ)
        (allocatedModelTestLog
          (preparedFiniteForwardPairedSourcePrecision exponent Cdirect countConstants
            (slotStage k).val (preparedFiniteNestedForwardAllDegreeIsDirect k)
            (slotSeed k) gainLog stageLog)
          (preparedFiniteForwardWork exponent countConstants (slotStage k).val (slotSeed k))))
      (native k)
      (preparedFiniteNestedForwardFixedCenterThreshold exponent countConstants Bstruct gainLog stageLog k))
    (hsize : ∀ i, Real.exp (preparedFiniteForwardCumulative exponent countConstants degree
      (seed outerInner.val Bstruct)) ≤ (N i : ℝ)) :
    ∃ P : A.DegreeSourceProfile degree p e,
      P.inner.x = seed outerInner.val Bstruct ∧
      P.inner.gainLog = seed outerInner.val Bstruct ∧
      P.front.u = preparedFiniteForwardModelPrecision exponent countConstants 0
        (seed outerFront.val Bstruct) gainLog stageLog ∧
      P.front.pModel = preparedFiniteForwardWork exponent countConstants 0
        (seed outerFront.val Bstruct) ∧
      P.front.nativeBudget = native
        ((outerFront, 0, ⟨degree, Nat.lt_succ_of_le hdegree⟩, false) : Slots) := by
  have he := preparedFiniteNestedResourceLayerSourceExponent_bounds 0 q cutoff e
    Cprimitive Cdirect extra exponent hExponent
  have hc := preparedFiniteNestedResourceLayerSourceSliceExponent_bounds 0 cutoff Cprimitive
  exact A.exists_zeroLayerNestedDegreeSourceProfile_scalars q outerDepth innerDepth cutoff exponent
    Cprimitive (preparedFiniteNestedSourceSliceExponent 0 cutoff Cprimitive) Cdirect
    Bstruct gainLog stageLog Qstride Plate outerFront outerInner
    hdegree hcutoff hdepth he.2.2.1 (he.2.2.2.2 degree hdegree)
    hc.1 he.2.2.2.1 (hc.2 degree hdegree)
    hprimitive hBstruct hg hs hQstride hG hX hpFront hpInner hξ hsurplus hsurplus1 htrim hN
    hNative hsize

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin 0 → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin 0 → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin 0 → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

namespace AllocatedExternalCandidateSampler

variable (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

local instance zeroLayerNestedDegreeFullScalarsSiteNonempty : Nonempty A.Site := A.site_nonempty
local notation "countConstants" => degreeSourceCountConstants

variable (q outerDepth innerDepth cutoff exponent Cprimitive Cslice Cdirect : ℕ)
    (Bstruct gainLog stageLog Qstride Plate : ℝ)
local notation "Slots" => PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff
local notation "count" => Fintype.card (LayerSamplerVariables G I n B)
local notation "pnum" => (Fintype.card G : ℝ)
local notation "seed" => candidateNestedForwardSeed exponent countConstants innerDepth
local notation "native" => preparedFiniteNestedSourceNative q G count (Fintype.card X)
    (preparedFiniteForwardDetectorPolynomial cutoff) exponent Cdirect countConstants
    Bstruct pnum Qstride gainLog stageLog Plate
local notation "slotSeed" => preparedFiniteNestedForwardAllDegreeSeed exponent countConstants Bstruct
local notation "slotStage" => preparedFiniteNestedForwardAllDegreeStage
local notation "slotDegree" => preparedFiniteNestedForwardAllDegreeDegree
attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection

theorem exists_zeroLayerNestedDegreeSourceProfile_full_scalars
    (outerFront outerInner : Fin (outerDepth + 1)) {degree e : ℕ} {p : ℝ}
    (hdegree : degree ≤ cutoff) (hcutoff : cutoff ≤ q) (hdepth : degree ≤ innerDepth)
    (hFrontExponent : preparedFiniteForwardFrontProfileExponent e ≤ exponent)
    (hInnerExponent : allocatedCandidateForwardScheduleExponent degree 0 Cprimitive
      (preparedFiniteForwardInnerSourceExponent Cdirect
        (preparedFiniteForwardActualNativeBudgetExponent q
          (preparedFiniteForwardDetectorPolynomial cutoff))) 2 ≤ exponent)
    (hCslice : 1 ≤ Cslice) (hSliceExponent : Cslice + 1 ≤ exponent)
    (hInnerSlice : allocatedCandidateStageSliceExponent degree 0 Cprimitive ≤ Cslice)
    (hprimitive : 1 ≤ Cprimitive)
    (hBstruct : 0 ≤ Bstruct) (hg : gainLog ∈ Set.Icc 0 Bstruct)
    (hs : stageLog ∈ Set.Icc 0 Bstruct) (hQstride : Qstride ∈ Set.Icc 0 Bstruct)
    (hG : (Fintype.card G : ℝ) ≤ Bstruct)
    (hX : (Fintype.card X : ℝ) ≤ Bstruct)
    (hpFront : p ∈ Set.Icc 0 (seed outerFront.val Bstruct))
    (hpInner : p ≤ seed outerInner.val Bstruct)
    (hξ : ξ ≤ 1)
    {surplus L : ℝ} (hsurplus : 0 < surplus) (hsurplus1 : surplus ≤ 1)
    (htrim : τ = unconditionedSpatialTrimFraction (Fintype.card X) surplus)
    (hN : ∀ i, unconditionedSpatialWidthCutoff
      (allocatedExternalCandidateRootBudget B U b S) τ L ≤ (N i : ℝ))
    (hNative : ∀ k : Slots, A.NativeDetection (slotDegree k)
      ((preparedFiniteForwardParameter exponent countConstants (slotStage k).val (slotSeed k) + Cslice) ^ Cslice)
      ((preparedFiniteForwardDetectorPolynomial cutoff).eval₂ (Nat.castRingHom ℝ)
        (allocatedModelTestLog
          (preparedFiniteForwardPairedSourcePrecision exponent Cdirect countConstants
            (slotStage k).val (preparedFiniteNestedForwardAllDegreeIsDirect k)
            (slotSeed k) gainLog stageLog)
          (preparedFiniteForwardWork exponent countConstants (slotStage k).val (slotSeed k))))
      (native k)
      (preparedFiniteNestedForwardFixedCenterThreshold exponent countConstants Bstruct gainLog stageLog k))
    (hsize : ∀ i, Real.exp (preparedFiniteForwardCumulative exponent countConstants degree
      (seed outerInner.val Bstruct)) ≤ (N i : ℝ)) :
    ∃ P : A.DegreeSourceProfile degree p e,
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
      P.inner.Csource = preparedFiniteForwardInnerSourceExponent Cdirect
        (preparedFiniteForwardActualNativeBudgetExponent q
          (preparedFiniteForwardDetectorPolynomial cutoff)) := by
  let P := A.zeroLayerNestedDegreeSourceProfile q outerDepth innerDepth cutoff exponent Cprimitive
    Cslice Cdirect Bstruct gainLog stageLog Qstride Plate outerFront outerInner
    hdegree hcutoff hdepth hFrontExponent hInnerExponent hCslice hSliceExponent hInnerSlice
    hprimitive hBstruct hg hs hQstride hG hX hpFront hpInner hξ hsurplus hsurplus1 htrim hN
    hNative hsize
  refine ⟨P, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [P, zeroLayerNestedDegreeSourceProfile, zeroLayerDegreeSourceProfile,
    zeroLayerForwardFrontSourceProfile, preparedFiniteForwardFrontSourceProfile,
    preparedFixedCenterFrontSourceProfile, InnerSourceProfile.with_gain_detection,
    InnerSourceProfile.raise_gain, preparedFiniteForwardActualResourceLayerInnerSourceProfile,
    preparedFiniteForwardResourceLayerInnerSourceProfile,
    preparedFiniteNestedSourceNative, preparedFiniteNestedForwardAllDegreeDegree_slot,
    preparedFiniteNestedSourceMaster_front]

theorem exists_zeroLayerNestedDegreeSourceProfile_of_exponent_full_scalars
    (extra : ℕ) (outerFront outerInner : Fin (outerDepth + 1)) {degree e : ℕ} {p : ℝ}
    (hdegree : degree ≤ cutoff) (hcutoff : cutoff ≤ q) (hdepth : degree ≤ innerDepth)
    (hExponent : preparedFiniteNestedResourceLayerSourceExponent 0 q cutoff e
      Cprimitive Cdirect extra ≤ exponent)
    (hprimitive : 1 ≤ Cprimitive)
    (hBstruct : 0 ≤ Bstruct) (hg : gainLog ∈ Set.Icc 0 Bstruct)
    (hs : stageLog ∈ Set.Icc 0 Bstruct) (hQstride : Qstride ∈ Set.Icc 0 Bstruct)
    (hG : (Fintype.card G : ℝ) ≤ Bstruct)
    (hX : (Fintype.card X : ℝ) ≤ Bstruct)
    (hpFront : p ∈ Set.Icc 0 (seed outerFront.val Bstruct))
    (hpInner : p ≤ seed outerInner.val Bstruct)
    (hξ : ξ ≤ 1)
    {surplus L : ℝ} (hsurplus : 0 < surplus) (hsurplus1 : surplus ≤ 1)
    (htrim : τ = unconditionedSpatialTrimFraction (Fintype.card X) surplus)
    (hN : ∀ i, unconditionedSpatialWidthCutoff
      (allocatedExternalCandidateRootBudget B U b S) τ L ≤ (N i : ℝ))
    (hNative : ∀ k : Slots, A.NativeDetection (slotDegree k)
      ((preparedFiniteForwardParameter exponent countConstants (slotStage k).val (slotSeed k) + (preparedFiniteNestedSourceSliceExponent 0 cutoff Cprimitive)) ^
        (preparedFiniteNestedSourceSliceExponent 0 cutoff Cprimitive))
      ((preparedFiniteForwardDetectorPolynomial cutoff).eval₂ (Nat.castRingHom ℝ)
        (allocatedModelTestLog
          (preparedFiniteForwardPairedSourcePrecision exponent Cdirect countConstants
            (slotStage k).val (preparedFiniteNestedForwardAllDegreeIsDirect k)
            (slotSeed k) gainLog stageLog)
          (preparedFiniteForwardWork exponent countConstants (slotStage k).val (slotSeed k))))
      (native k)
      (preparedFiniteNestedForwardFixedCenterThreshold exponent countConstants Bstruct gainLog stageLog k))
    (hsize : ∀ i, Real.exp (preparedFiniteForwardCumulative exponent countConstants degree
      (seed outerInner.val Bstruct)) ≤ (N i : ℝ)) :
    ∃ P : A.DegreeSourceProfile degree p e,
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
      P.inner.Csource = preparedFiniteForwardInnerSourceExponent Cdirect
        (preparedFiniteForwardActualNativeBudgetExponent q
          (preparedFiniteForwardDetectorPolynomial cutoff)) := by
  have he := preparedFiniteNestedResourceLayerSourceExponent_bounds 0 q cutoff e
    Cprimitive Cdirect extra exponent hExponent
  have hc := preparedFiniteNestedResourceLayerSourceSliceExponent_bounds 0 cutoff Cprimitive
  exact A.exists_zeroLayerNestedDegreeSourceProfile_full_scalars q outerDepth innerDepth cutoff exponent
    Cprimitive (preparedFiniteNestedSourceSliceExponent 0 cutoff Cprimitive) Cdirect
    Bstruct gainLog stageLog Qstride Plate outerFront outerInner
    hdegree hcutoff hdepth he.2.2.1 (he.2.2.2.2 degree hdegree)
    hc.1 he.2.2.2.1 (hc.2 degree hdegree)
    hprimitive hBstruct hg hs hQstride hG hX hpFront hpInner hξ hsurplus hsurplus1 htrim hN
    hNative hsize

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel AllocatedExternalCandidateSampler
open scoped Classical BigOperators NNReal TensorProduct

def PreparedScalarNestedPowerDegreeProfiles
    (s outerDepth innerDepth exponent Cprimitive Cdirect : ℕ)
    (entropies : Fin (s + 1) → ℕ)
    (basePower earlyExponent latePower sizeExponent : ℕ) : Prop :=
  ∀ {nX : ℕ} {p : ℝ}, 2 ≤ p → (nX : ℝ) ≤ p →
    ∀ {I₀ J₀ : Fin 0 → Type} [∀ j, Fintype (I₀ j)] [∀ j, Fintype (J₀ j)]
      {n₀ : Fin 0 → ℕ} {B₀ : LayerSamplerAxis I₀ n₀ → Type} [∀ a, Fintype (B₀ a)]
      {U₀ : ∀ j, Submodule ℝ (J₀ j → ℝ)}
      {b₀ : ∀ j, Basis (Fin (n₀ j)) ℝ (euclideanSubspace (U₀ j))ᗮ}
      {R₀ σ₀ : Fin 0 → ℝ}
      {S₀ : LayerSamplerScale (G := Fin (scalarNativeDimension s)) B₀ U₀ b₀ R₀ σ₀}
      {hb₀ : ∀ j, span ℤ (Set.range (b₀ j)) = projectedIntegerLattice (euclideanSubspace (U₀ j))}
      {o₀ : ∀ j, OrthonormalBasis (I₀ j) ℝ (euclideanSubspace (U₀ j))}
      {hR₀ : ∀ j, 0 < R₀ j} {hσ₀ : ∀ j, 0 < σ₀ j}
      {N : Fin nX → ℕ} {poly₀ : ∀ j, VectorPolynomial (Fin nX) ℝ (J₀ j → ℝ)}
      {hmem₀ : ∀ j e, coefficients (poly₀ j) e ∈ U₀ j}
      {τ ξ₀ : ℝ}
      {center₀ : CoefficientTorus
        (K := LayerSamplerVariables (Fin (scalarNativeDimension s)) I₀ n₀ B₀) U₀}
      [∀ j, IsZLattice ℝ
        (latticeSection (standardEuclideanLattice (J₀ j)) (euclideanSubspace (U₀ j)))]
      (A₀ : AllocatedExternalCandidateSampler B₀ U₀ b₀ S₀ hb₀ o₀ hR₀ hσ₀
        N poly₀ hmem₀ τ ξ₀ (fun _ : Fin nX => 1) {0} center₀),
      ξ₀ ≤ 1 →
      τ = unconditionedSpatialTrimFraction nX (Real.exp (-p)) →
      Real.exp ((p + 2) ^ earlyExponent) ≤ S₀.value →
      (S₀.value : ℝ) ≤ Real.exp ((p + 2) ^ latePower) →
      (∀ i, Real.exp ((p + 2) ^ sizeExponent) ≤ (N i : ℝ)) →
      let Bstruct := (p + 2) ^ basePower
      let K := PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth s
      let degree : K → ℕ := preparedFiniteNestedForwardAllDegreeDegree
      let stage : K → ℕ := fun k => (preparedFiniteNestedForwardAllDegreeStage k).val
      let seed : K → ℝ := preparedFiniteNestedForwardAllDegreeSeed exponent degreeSourceCountConstants Bstruct
      let sourceU := fun k : K => preparedFiniteForwardPairedSourcePrecision exponent Cdirect
        degreeSourceCountConstants (stage k) (preparedFiniteNestedForwardAllDegreeIsDirect k)
        (seed k) Bstruct Bstruct
      let modelLog := fun k : K => preparedFiniteForwardWork exponent degreeSourceCountConstants
        (stage k) (seed k)
      let Cslice := preparedFiniteNestedSourceSliceExponent 0 s Cprimitive
      let sliceLog := fun k : K =>
        (preparedFiniteForwardParameter exponent degreeSourceCountConstants (stage k) (seed k) + Cslice) ^ Cslice
      let α := preparedFiniteNestedForwardFixedCenterThreshold exponent degreeSourceCountConstants
        Bstruct Bstruct Bstruct
      let Pdetect := preparedFiniteForwardDetectorPolynomial s
      let outerSeed := candidateNestedForwardSeed exponent degreeSourceCountConstants innerDepth
      ∃ Plate : ℝ, 0 ≤ Plate ∧
        (∀ k : K, A₀.NativeDetection (degree k) (sliceLog k)
          (Pdetect.eval₂ (Nat.castRingHom ℝ) (allocatedModelTestLog (sourceU k) (modelLog k)))
          (preparedFiniteNestedSourceNative (max s 1) (Fin (scalarNativeDimension s))
            (scalarNativeDimension s) nX Pdetect exponent Cdirect degreeSourceCountConstants
            Bstruct (scalarNativeDimension s) 0 Bstruct Bstruct Plate k) (α k)) ∧
        (∀ (outer : Fin (outerDepth + 1)) (degree : Fin (s + 1)) (i : Fin nX),
          Real.exp (preparedFiniteForwardCumulative exponent degreeSourceCountConstants degree.val
            (outerSeed outer.val Bstruct)) ≤ (N i : ℝ)) ∧
        ∀ (entropySlot : Fin (s + 1)) (outerFront outerInner : Fin (outerDepth + 1)),
          outerFront ≤ outerInner → ∀ (d : ℕ) (hd : d ≤ s) (pNorm : ℝ),
          pNorm ∈ Set.Icc 0 (outerSeed outerFront.val Bstruct) →
          ∃ P : A₀.DegreeSourceProfile d pNorm (entropies entropySlot),
            P.inner.x = outerSeed outerInner.val Bstruct ∧
            P.inner.gainLog = outerSeed outerInner.val Bstruct ∧
            P.front.u = preparedFiniteForwardModelPrecision exponent degreeSourceCountConstants 0
              (outerSeed outerFront.val Bstruct) Bstruct Bstruct ∧
            P.front.pModel = preparedFiniteForwardWork exponent degreeSourceCountConstants 0
              (outerSeed outerFront.val Bstruct) ∧
            P.front.nativeBudget = preparedFiniteNestedSourceNative (max s 1)
              (Fin (scalarNativeDimension s)) (scalarNativeDimension s) nX Pdetect
              exponent Cdirect degreeSourceCountConstants Bstruct (scalarNativeDimension s) 0
              Bstruct Bstruct Plate
              ((outerFront, 0, ⟨d, Nat.lt_succ_of_le hd⟩, false) : K)

theorem exists_preparedScalarNestedPowerDegreeProfiles_of_exponent
    (s outerDepth innerDepth exponent Cprimitive Cdirect extra baseFloor : ℕ)
    (entropies : Fin (s + 1) → ℕ)
    (hA : 3 ≤ exponent) (hprimitive : 1 ≤ Cprimitive) (hdepth : s ≤ innerDepth)
    (hExponent : ∀ j, preparedFiniteNestedResourceLayerSourceExponent 0 (max s 1) s
      (entropies j) Cprimitive Cdirect extra ≤ exponent) :
    ∃ baseMin : ℕ, baseFloor ≤ baseMin ∧ 1 ≤ baseMin ∧
      ∀ basePower : ℕ, baseMin ≤ basePower →
      ∃ earlyExponent : ℕ, 2 ≤ earlyExponent ∧ ∀ latePower : ℕ,
        ∃ sizeExponent : ℕ, 2 ≤ sizeExponent ∧
          PreparedScalarNestedPowerDegreeProfiles s outerDepth innerDepth exponent Cprimitive Cdirect
            entropies basePower earlyExponent latePower sizeExponent := by
  let Cslice := preparedFiniteNestedSourceSliceExponent 0 s Cprimitive
  have he := preparedFiniteNestedResourceLayerSourceExponent_bounds
    0 (max s 1) s (entropies 0) Cprimitive Cdirect extra exponent (hExponent 0)
  obtain ⟨baseMin, hBaseMin, hPower⟩ := exists_preparedScalarNestedSchedule_power_detection
    s outerDepth innerDepth exponent Cslice Cdirect degreeSourceCountConstants hA he.2.2.2.1 hdepth
  obtain ⟨structMin, hStructMin, hstruct⟩ := exists_preparedScalarStructuralBasePower s
  let fullMin := max baseFloor (max baseMin structMin)
  refine ⟨fullMin, le_max_left _ _, hBaseMin.trans ((le_max_left _ _).trans (le_max_right _ _)), ?_⟩
  intro basePower hBasePower
  have hBase : baseMin ≤ basePower :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hBasePower
  have hStruct : structMin ≤ basePower :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hBasePower
  obtain ⟨earlyExponent, hEarly, hLate⟩ := hPower basePower hBase
  refine ⟨earlyExponent, hEarly, ?_⟩
  intro latePower
  obtain ⟨detectSize, hDetectSize, hDetection⟩ := hLate latePower
  obtain ⟨widthSize, _, hWidth⟩ := exists_preparedScalarSpatialWidthPower s latePower
  let sizeExponent := max detectSize widthSize
  refine ⟨sizeExponent, hDetectSize.trans (le_max_left _ _), ?_⟩
  intro nX p hp hX I₀ J₀ _ _ n₀ B₀ _ U₀ b₀ R₀ σ₀ S₀ hb₀ o₀ hR₀ hσ₀
    N poly₀ hmem₀ τ ξ₀ center₀ _ A₀ hξ htrim hscale hSupper hsize
  let Bstruct : ℝ := (p + 2) ^ basePower
  have hp0 : 0 ≤ p := by linarith
  have hB : 0 ≤ Bstruct := by dsimp [Bstruct]; positivity
  have hbase : 1 ≤ p + 2 := by linarith
  have hsizeDetect (i : Fin nX) : Real.exp ((p + 2) ^ detectSize) ≤ (N i : ℝ) :=
    (Real.exp_le_exp.mpr (pow_le_pow_right₀ hbase (le_max_left _ _))).trans (hsize i)
  obtain ⟨Plate, hPlate, hNative, hCumulative⟩ :=
    hDetection hp hX A₀ htrim hscale hSupper hsizeDetect
  have hN (i : Fin nX) : unconditionedSpatialWidthCutoff
      (allocatedExternalCandidateRootBudget B₀ U₀ b₀ S₀) τ 1 ≤ (N i : ℝ) := by
    rw [allocatedExternalCandidateRootBudget_zero_layers, Fintype.card_fin, htrim]
    exact (hWidth p hp nX hX S₀.value hSupper).trans
      ((Real.exp_le_exp.mpr (pow_le_pow_right₀ hbase (le_max_right _ _))).trans (hsize i))
  have hstructData := hstruct basePower hStruct p hp
  refine ⟨Plate, hPlate, hNative, hCumulative, ?_⟩
  intro entropySlot outerFront outerInner horder d hd pNorm hpNorm
  have hA2 : 2 ≤ exponent := by omega
  have hpInner : pNorm ≤ candidateNestedForwardSeed exponent degreeSourceCountConstants
      innerDepth outerInner.val Bstruct :=
    hpNorm.2.trans (candidateNestedForwardSeed_monotone exponent degreeSourceCountConstants
      innerDepth hA2 hB horder)
  have hG : (Fintype.card (Fin (scalarNativeDimension s)) : ℝ) ≤ Bstruct := by
    simpa only [Fintype.card_fin] using hstructData.1
  have hXstruct : (Fintype.card (Fin nX) : ℝ) ≤ Bstruct := by
    simpa only [Fintype.card_fin] using hX.trans hstructData.2.2.2
  have hsurplus1 : Real.exp (-p) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have htrim' : τ = unconditionedSpatialTrimFraction (Fintype.card (Fin nX)) (Real.exp (-p)) := by
    simpa only [Fintype.card_fin] using htrim
  have hdec : instDecidableEqFin nX = (fun a b : Fin nX => Classical.propDecidable (a = b)) :=
    Subsingleton.elim _ _
  rw [hdec] at hNative
  have hprofile := A₀.exists_zeroLayerNestedDegreeSourceProfile_of_exponent_scalars
    (max s 1) outerDepth innerDepth s exponent Cprimitive Cdirect Bstruct Bstruct Bstruct 0 Plate
    extra outerFront outerInner hd (le_max_left s 1) (hd.trans hdepth) (hExponent entropySlot)
    hprimitive hB ⟨hB, le_rfl⟩ ⟨hB, le_rfl⟩ ⟨le_rfl, hB⟩ hG hXstruct hpNorm hpInner
    hξ (Real.exp_pos (-p)) hsurplus1 htrim' hN
    (by simpa only [zeroLayerVariables_card, Fintype.card_fin] using hNative)
    (hCumulative outerInner ⟨d, Nat.lt_succ_of_le hd⟩)
  simpa only [zeroLayerVariables_card, Fintype.card_fin] using hprofile

noncomputable def preparedScalarNestedFamilyProfileExponent
    (s Cprimitive Cdirect extra : ℕ) (entropies : Fin (s + 1) → ℕ) : ℕ :=
  3 + extra + ∑ j, preparedFiniteNestedResourceLayerSourceExponent 0 (max s 1) s
    (entropies j) Cprimitive Cdirect extra

theorem preparedScalarNestedFamilyProfileExponent_bounds
    (s Cprimitive Cdirect extra : ℕ) (entropies : Fin (s + 1) → ℕ) :
    3 ≤ preparedScalarNestedFamilyProfileExponent s Cprimitive Cdirect extra entropies ∧
    extra ≤ preparedScalarNestedFamilyProfileExponent s Cprimitive Cdirect extra entropies ∧
    ∀ j, preparedFiniteNestedResourceLayerSourceExponent 0 (max s 1) s
      (entropies j) Cprimitive Cdirect extra ≤
        preparedScalarNestedFamilyProfileExponent s Cprimitive Cdirect extra entropies := by
  unfold preparedScalarNestedFamilyProfileExponent
  refine ⟨by omega, by omega, ?_⟩
  intro j
  have h := Finset.single_le_sum
    (f := fun j : Fin (s + 1) => preparedFiniteNestedResourceLayerSourceExponent 0 (max s 1) s
      (entropies j) Cprimitive Cdirect extra)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  omega

theorem exists_preparedScalarNestedPowerDegreeProfiles
    (s outerDepth innerDepth Cprimitive Cdirect extra baseFloor : ℕ)
    (entropies : Fin (s + 1) → ℕ) (hprimitive : 1 ≤ Cprimitive) (hdepth : s ≤ innerDepth) :
    let exponent := preparedScalarNestedFamilyProfileExponent s Cprimitive Cdirect extra entropies
    ∃ baseMin : ℕ, baseFloor ≤ baseMin ∧ 1 ≤ baseMin ∧
      ∀ basePower : ℕ, baseMin ≤ basePower →
      ∃ earlyExponent : ℕ, 2 ≤ earlyExponent ∧ ∀ latePower : ℕ,
        ∃ sizeExponent : ℕ, 2 ≤ sizeExponent ∧
          PreparedScalarNestedPowerDegreeProfiles s outerDepth innerDepth exponent Cprimitive Cdirect
            entropies basePower earlyExponent latePower sizeExponent := by
  intro exponent
  have h := preparedScalarNestedFamilyProfileExponent_bounds s Cprimitive Cdirect extra entropies
  exact exists_preparedScalarNestedPowerDegreeProfiles_of_exponent s outerDepth innerDepth exponent
    Cprimitive Cdirect extra baseFloor entropies h.1 hprimitive hdepth h.2.2

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel AllocatedExternalCandidateSampler
open scoped Classical BigOperators NNReal TensorProduct

def PreparedScalarNestedPowerDegreeProfilesFull
    (s outerDepth innerDepth exponent Cprimitive Cdirect : ℕ)
    (entropies : Fin (s + 1) → ℕ)
    (basePower earlyExponent latePower sizeExponent : ℕ) : Prop :=
  ∀ {nX : ℕ} {p : ℝ}, 2 ≤ p → (nX : ℝ) ≤ p →
    ∀ {I₀ J₀ : Fin 0 → Type} [∀ j, Fintype (I₀ j)] [∀ j, Fintype (J₀ j)]
      {n₀ : Fin 0 → ℕ} {B₀ : LayerSamplerAxis I₀ n₀ → Type} [∀ a, Fintype (B₀ a)]
      {U₀ : ∀ j, Submodule ℝ (J₀ j → ℝ)}
      {b₀ : ∀ j, Basis (Fin (n₀ j)) ℝ (euclideanSubspace (U₀ j))ᗮ}
      {R₀ σ₀ : Fin 0 → ℝ}
      {S₀ : LayerSamplerScale (G := Fin (scalarNativeDimension s)) B₀ U₀ b₀ R₀ σ₀}
      {hb₀ : ∀ j, span ℤ (Set.range (b₀ j)) = projectedIntegerLattice (euclideanSubspace (U₀ j))}
      {o₀ : ∀ j, OrthonormalBasis (I₀ j) ℝ (euclideanSubspace (U₀ j))}
      {hR₀ : ∀ j, 0 < R₀ j} {hσ₀ : ∀ j, 0 < σ₀ j}
      {N : Fin nX → ℕ} {poly₀ : ∀ j, VectorPolynomial (Fin nX) ℝ (J₀ j → ℝ)}
      {hmem₀ : ∀ j e, coefficients (poly₀ j) e ∈ U₀ j}
      {τ ξ₀ : ℝ}
      {center₀ : CoefficientTorus
        (K := LayerSamplerVariables (Fin (scalarNativeDimension s)) I₀ n₀ B₀) U₀}
      [∀ j, IsZLattice ℝ
        (latticeSection (standardEuclideanLattice (J₀ j)) (euclideanSubspace (U₀ j)))]
      (A₀ : AllocatedExternalCandidateSampler B₀ U₀ b₀ S₀ hb₀ o₀ hR₀ hσ₀
        N poly₀ hmem₀ τ ξ₀ (fun _ : Fin nX => 1) {0} center₀),
      ξ₀ ≤ 1 →
      τ = unconditionedSpatialTrimFraction nX (Real.exp (-p)) →
      Real.exp ((p + 2) ^ earlyExponent) ≤ S₀.value →
      (S₀.value : ℝ) ≤ Real.exp ((p + 2) ^ latePower) →
      (∀ i, Real.exp ((p + 2) ^ sizeExponent) ≤ (N i : ℝ)) →
      let Bstruct := (p + 2) ^ basePower
      let K := PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth s
      let degree : K → ℕ := preparedFiniteNestedForwardAllDegreeDegree
      let stage : K → ℕ := fun k => (preparedFiniteNestedForwardAllDegreeStage k).val
      let seed : K → ℝ := preparedFiniteNestedForwardAllDegreeSeed exponent degreeSourceCountConstants Bstruct
      let sourceU := fun k : K => preparedFiniteForwardPairedSourcePrecision exponent Cdirect
        degreeSourceCountConstants (stage k) (preparedFiniteNestedForwardAllDegreeIsDirect k)
        (seed k) Bstruct Bstruct
      let modelLog := fun k : K => preparedFiniteForwardWork exponent degreeSourceCountConstants
        (stage k) (seed k)
      let Cslice := preparedFiniteNestedSourceSliceExponent 0 s Cprimitive
      let sliceLog := fun k : K =>
        (preparedFiniteForwardParameter exponent degreeSourceCountConstants (stage k) (seed k) + Cslice) ^ Cslice
      let α := preparedFiniteNestedForwardFixedCenterThreshold exponent degreeSourceCountConstants
        Bstruct Bstruct Bstruct
      let Pdetect := preparedFiniteForwardDetectorPolynomial s
      let outerSeed := candidateNestedForwardSeed exponent degreeSourceCountConstants innerDepth
      ∃ Plate : ℝ, 0 ≤ Plate ∧
        (∀ k : K, A₀.NativeDetection (degree k) (sliceLog k)
          (Pdetect.eval₂ (Nat.castRingHom ℝ) (allocatedModelTestLog (sourceU k) (modelLog k)))
          (preparedFiniteNestedSourceNative (max s 1) (Fin (scalarNativeDimension s))
            (scalarNativeDimension s) nX Pdetect exponent Cdirect degreeSourceCountConstants
            Bstruct (scalarNativeDimension s) 0 Bstruct Bstruct Plate k) (α k)) ∧
        (∀ (outer : Fin (outerDepth + 1)) (degree : Fin (s + 1)) (i : Fin nX),
          Real.exp (preparedFiniteForwardCumulative exponent degreeSourceCountConstants degree.val
            (outerSeed outer.val Bstruct)) ≤ (N i : ℝ)) ∧
        ∀ (entropySlot : Fin (s + 1)) (outerFront outerInner : Fin (outerDepth + 1)),
          outerFront ≤ outerInner → ∀ (d : ℕ) (hd : d ≤ s) (pNorm : ℝ),
          pNorm ∈ Set.Icc 0 (outerSeed outerFront.val Bstruct) →
          ∃ P : A₀.DegreeSourceProfile d pNorm (entropies entropySlot),
            P.inner.x = outerSeed outerInner.val Bstruct ∧
            P.inner.gainLog = outerSeed outerInner.val Bstruct ∧
            P.front.u = preparedFiniteForwardModelPrecision exponent degreeSourceCountConstants 0
              (outerSeed outerFront.val Bstruct) Bstruct Bstruct ∧
            P.front.pModel = preparedFiniteForwardWork exponent degreeSourceCountConstants 0
              (outerSeed outerFront.val Bstruct) ∧
            P.front.nativeBudget = preparedFiniteNestedSourceNative (max s 1)
              (Fin (scalarNativeDimension s)) (scalarNativeDimension s) nX Pdetect
              exponent Cdirect degreeSourceCountConstants Bstruct (scalarNativeDimension s) 0
              Bstruct Bstruct Plate
              ((outerFront, 0, ⟨d, Nat.lt_succ_of_le hd⟩, false) : K) ∧
            P.inner.Cprimitive = Cprimitive ∧
            P.inner.scheduleExponent = exponent ∧
            P.inner.Csource = preparedFiniteForwardInnerSourceExponent Cdirect
              (preparedFiniteForwardActualNativeBudgetExponent (max s 1) Pdetect)

theorem exists_preparedScalarNestedPowerDegreeProfiles_full_of_exponent
    (s outerDepth innerDepth exponent Cprimitive Cdirect extra baseFloor : ℕ)
    (entropies : Fin (s + 1) → ℕ)
    (hA : 3 ≤ exponent) (hprimitive : 1 ≤ Cprimitive) (hdepth : s ≤ innerDepth)
    (hExponent : ∀ j, preparedFiniteNestedResourceLayerSourceExponent 0 (max s 1) s
      (entropies j) Cprimitive Cdirect extra ≤ exponent) :
    ∃ baseMin : ℕ, baseFloor ≤ baseMin ∧ 1 ≤ baseMin ∧
      ∀ basePower : ℕ, baseMin ≤ basePower →
      ∃ earlyExponent : ℕ, 2 ≤ earlyExponent ∧ ∀ latePower : ℕ,
        ∃ sizeExponent : ℕ, 2 ≤ sizeExponent ∧
          PreparedScalarNestedPowerDegreeProfilesFull s outerDepth innerDepth exponent Cprimitive Cdirect
            entropies basePower earlyExponent latePower sizeExponent := by
  obtain ⟨baseMin, _, hBaseMin, hPower⟩ := exists_preparedScalarNestedPowerDegreeProfiles_of_exponent
    s outerDepth innerDepth exponent Cprimitive Cdirect extra baseFloor entropies
    hA hprimitive hdepth hExponent
  obtain ⟨structMin, hStructMin, hstruct⟩ := exists_preparedScalarStructuralBasePower s
  let fullMin := max baseFloor (max baseMin structMin)
  refine ⟨fullMin, le_max_left _ _, hBaseMin.trans ((le_max_left _ _).trans (le_max_right _ _)), ?_⟩
  intro basePower hBasePower
  have hBase : baseMin ≤ basePower :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hBasePower
  have hStruct : structMin ≤ basePower :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hBasePower
  obtain ⟨earlyExponent, hEarly, hLate⟩ := hPower basePower hBase
  refine ⟨earlyExponent, hEarly, ?_⟩
  intro latePower
  obtain ⟨detectSize, hDetectSize, hDetection⟩ := hLate latePower
  obtain ⟨widthSize, _, hWidth⟩ := exists_preparedScalarSpatialWidthPower s latePower
  let sizeExponent := max detectSize widthSize
  refine ⟨sizeExponent, hDetectSize.trans (le_max_left _ _), ?_⟩
  intro nX p hp hX I₀ J₀ _ _ n₀ B₀ _ U₀ b₀ R₀ σ₀ S₀ hb₀ o₀ hR₀ hσ₀
    N poly₀ hmem₀ τ ξ₀ center₀ _ A₀ hξ htrim hscale hSupper hsize
  let Bstruct : ℝ := (p + 2) ^ basePower
  have hp0 : 0 ≤ p := by linarith
  have hB : 0 ≤ Bstruct := by dsimp [Bstruct]; positivity
  have hbase : 1 ≤ p + 2 := by linarith
  have hsizeDetect (i : Fin nX) : Real.exp ((p + 2) ^ detectSize) ≤ (N i : ℝ) :=
    (Real.exp_le_exp.mpr (pow_le_pow_right₀ hbase (le_max_left _ _))).trans (hsize i)
  obtain ⟨Plate, hPlate, hNative, hCumulative, _⟩ :=
    hDetection hp hX A₀ hξ htrim hscale hSupper hsizeDetect
  have hN (i : Fin nX) : unconditionedSpatialWidthCutoff
      (allocatedExternalCandidateRootBudget B₀ U₀ b₀ S₀) τ 1 ≤ (N i : ℝ) := by
    rw [allocatedExternalCandidateRootBudget_zero_layers, Fintype.card_fin, htrim]
    exact (hWidth p hp nX hX S₀.value hSupper).trans
      ((Real.exp_le_exp.mpr (pow_le_pow_right₀ hbase (le_max_right _ _))).trans (hsize i))
  have hstructData := hstruct basePower hStruct p hp
  refine ⟨Plate, hPlate, hNative, hCumulative, ?_⟩
  intro entropySlot outerFront outerInner horder d hd pNorm hpNorm
  have hA2 : 2 ≤ exponent := by omega
  have hpInner : pNorm ≤ candidateNestedForwardSeed exponent degreeSourceCountConstants
      innerDepth outerInner.val Bstruct :=
    hpNorm.2.trans (candidateNestedForwardSeed_monotone exponent degreeSourceCountConstants
      innerDepth hA2 hB horder)
  have hG : (Fintype.card (Fin (scalarNativeDimension s)) : ℝ) ≤ Bstruct := by
    simpa only [Fintype.card_fin] using hstructData.1
  have hXstruct : (Fintype.card (Fin nX) : ℝ) ≤ Bstruct := by
    simpa only [Fintype.card_fin] using hX.trans hstructData.2.2.2
  have hsurplus1 : Real.exp (-p) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have htrim' : τ = unconditionedSpatialTrimFraction (Fintype.card (Fin nX)) (Real.exp (-p)) := by
    simpa only [Fintype.card_fin] using htrim
  have hdec : instDecidableEqFin nX = (fun a b : Fin nX => Classical.propDecidable (a = b)) :=
    Subsingleton.elim _ _
  rw [hdec] at hNative
  have hprofile := A₀.exists_zeroLayerNestedDegreeSourceProfile_of_exponent_full_scalars
    (max s 1) outerDepth innerDepth s exponent Cprimitive Cdirect Bstruct Bstruct Bstruct 0 Plate
    extra outerFront outerInner hd (le_max_left s 1) (hd.trans hdepth) (hExponent entropySlot)
    hprimitive hB ⟨hB, le_rfl⟩ ⟨hB, le_rfl⟩ ⟨le_rfl, hB⟩ hG hXstruct hpNorm hpInner
    hξ (Real.exp_pos (-p)) hsurplus1 htrim' hN
    (by simpa only [zeroLayerVariables_card, Fintype.card_fin] using hNative)
    (hCumulative outerInner ⟨d, Nat.lt_succ_of_le hd⟩)
  simpa only [zeroLayerVariables_card, Fintype.card_fin] using hprofile

theorem exists_preparedScalarNestedPowerDegreeProfiles_full
    (s outerDepth innerDepth Cprimitive Cdirect extra baseFloor : ℕ)
    (entropies : Fin (s + 1) → ℕ) (hprimitive : 1 ≤ Cprimitive) (hdepth : s ≤ innerDepth) :
    let exponent := preparedScalarNestedFamilyProfileExponent s Cprimitive Cdirect extra entropies
    ∃ baseMin : ℕ, baseFloor ≤ baseMin ∧ 1 ≤ baseMin ∧
      ∀ basePower : ℕ, baseMin ≤ basePower →
      ∃ earlyExponent : ℕ, 2 ≤ earlyExponent ∧ ∀ latePower : ℕ,
        ∃ sizeExponent : ℕ, 2 ≤ sizeExponent ∧
          PreparedScalarNestedPowerDegreeProfilesFull s outerDepth innerDepth exponent Cprimitive Cdirect
            entropies basePower earlyExponent latePower sizeExponent := by
  intro exponent
  have h := preparedScalarNestedFamilyProfileExponent_bounds s Cprimitive Cdirect extra entropies
  exact exists_preparedScalarNestedPowerDegreeProfiles_full_of_exponent s outerDepth innerDepth exponent
    Cprimitive Cdirect extra baseFloor entropies h.1 hprimitive hdepth h.2.2

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel AllocatedExternalCandidateSampler
open scoped Classical BigOperators NNReal TensorProduct
attribute [local irreducible] AllocatedExternalCandidateSampler.DegreeGlobalizationAt

def ScalarNestedSourceDegreeGlobalization
    (s initial exponent basePower earlyExponent latePower sizeExponent : ℕ) : Prop :=
  ∀ {nX : ℕ} {p : ℝ}, 2 ≤ p → (nX : ℝ) ≤ p →
    ∀ {I₀ E₀ J₀ : Fin 0 → Type} [∀ j, Fintype (I₀ j)] [∀ j, Fintype (J₀ j)]
      {n₀ : Fin 0 → ℕ} {B₀ : LayerSamplerAxis I₀ n₀ → Type} [∀ a, Fintype (B₀ a)]
      {U₀ : ∀ j, Submodule ℝ (J₀ j → ℝ)}
      {b₀ : ∀ j, Basis (Fin (n₀ j)) ℝ (euclideanSubspace (U₀ j))ᗮ}
      {R₀ σ₀ : Fin 0 → ℝ}
      {S₀ : LayerSamplerScale (G := Fin (scalarNativeDimension s)) B₀ U₀ b₀ R₀ σ₀}
      {hb₀ : ∀ j, span ℤ (Set.range (b₀ j)) = projectedIntegerLattice (euclideanSubspace (U₀ j))}
      {o₀ : ∀ j, OrthonormalBasis (I₀ j) ℝ (euclideanSubspace (U₀ j))}
      {hR₀ : ∀ j, 0 < R₀ j} {hσ₀ : ∀ j, 0 < σ₀ j}
      {N : Fin nX → ℕ} {poly₀ : ∀ j, VectorPolynomial (Fin nX) ℝ (J₀ j → ℝ)}
      {hmem₀ : ∀ j e, coefficients (poly₀ j) e ∈ U₀ j}
      {τ ξ₀ : ℝ}
      {center₀ : CoefficientTorus
        (K := LayerSamplerVariables (Fin (scalarNativeDimension s)) I₀ n₀ B₀) U₀}
      [∀ j, IsZLattice ℝ
        (latticeSection (standardEuclideanLattice (J₀ j)) (euclideanSubspace (U₀ j)))]
      (A₀ : AllocatedExternalCandidateSampler B₀ U₀ b₀ S₀ hb₀ o₀ hR₀ hσ₀
        N poly₀ hmem₀ τ ξ₀ (fun _ : Fin nX => 1) {0} center₀),
      ξ₀ ≤ 1 →
      τ = unconditionedSpatialTrimFraction nX (Real.exp (-p)) →
      Real.exp ((p + 2) ^ earlyExponent) ≤ S₀.value →
      (S₀.value : ℝ) ≤ Real.exp ((p + 2) ^ latePower) →
      (∀ i, Real.exp ((p + 2) ^ sizeExponent) ≤ (N i : ℝ)) →
      let Bstruct := (p + 2) ^ basePower
      let finalSeed := candidateNestedForwardSeed exponent degreeSourceCountConstants (s + 1)
        (2 * s) Bstruct
      Real.exp finalSeed ≤ (S₀.value : ℝ) →
      ∀ weight : (Fin nX → ℤ) → ℂ,
        A₀.DegreeGlobalizationAt (E := E₀) weight s initial Bstruct
          (candidateDegreeReturnBudget s finalSeed)

theorem exists_scalarNestedSourceDegreeGlobalization
    (s initial extra baseFloor : ℕ) :
    ∃ exponent : ℕ, 3 ≤ exponent ∧
      ∃ baseMin : ℕ, baseFloor ≤ baseMin ∧ 1 ≤ baseMin ∧
        ∀ basePower : ℕ, baseMin ≤ basePower →
        ∃ earlyExponent : ℕ, 2 ≤ earlyExponent ∧ ∀ latePower : ℕ,
          ∃ sizeExponent : ℕ, 2 ≤ sizeExponent ∧
            ScalarNestedSourceDegreeGlobalization s initial exponent basePower
              earlyExponent latePower sizeExponent := by
  classical
  obtain ⟨Cstep, hCstep, hglobal⟩ := exists_degreeGlobalizationAt_of_nested_source_profiles s
  let eMax := candidateNestedDegreeNetBound s initial
  let Pdetect := preparedFiniteForwardDetectorPolynomial s
  let Csource := preparedFiniteNestedResourceLayerSourceExponent 0 (max s 1) s eMax 1 1 extra
  let Cfront := preparedFiniteNestedFrontFitExponent (max s 1) Pdetect Cstep
  let Crec := candidateSourceRecursiveUniformExponent s 1
  let exponent := 3 + Csource + Cfront + Crec
  have hA : 3 ≤ exponent := by dsimp [exponent]; omega
  have hsource : Csource ≤ exponent := by dsimp [exponent]; omega
  have hfront : Cfront ≤ exponent := by dsimp [exponent]; omega
  have hrec : Crec ≤ exponent := by dsimp [exponent]; omega
  obtain ⟨sourceMin, hSourceFloor, hSourceMin, hSources⟩ :=
    exists_preparedScalarNestedPowerDegreeProfiles_full_of_exponent
      s (2 * s) (s + 1) exponent 1 1 extra baseFloor (fun _ => eMax)
      hA (by omega) (by omega) (fun _ => hsource)
  obtain ⟨structMin, hStructMin, hstruct⟩ := exists_preparedScalarStructuralBasePower s
  refine ⟨exponent, hA, max sourceMin structMin,
    hSourceFloor.trans (le_max_left _ _), hSourceMin.trans (le_max_left _ _), ?_⟩
  intro basePower hBase
  have hBaseSource := (le_max_left sourceMin structMin).trans hBase
  have hBaseStruct := (le_max_right sourceMin structMin).trans hBase
  obtain ⟨earlyExponent, hEarly, hLate⟩ := hSources basePower hBaseSource
  refine ⟨earlyExponent, hEarly, ?_⟩
  intro latePower
  obtain ⟨sizeExponent, hSize, hFull⟩ := hLate latePower
  refine ⟨sizeExponent, hSize, ?_⟩
  intro nX p hp hnX I₀ E₀ J₀ _ _ n₀ B₀ _ U₀ b₀ R₀ σ₀ S₀ hb₀ o₀ hR₀ hσ₀
    N poly₀ hmem₀ τ ξ₀ center₀ _ A₀ hξ htrim hS hSupper hN Bstruct finalSeed hFinal weight
  let : Nonempty (Fin (scalarNativeDimension s)) :=
    ⟨⟨0, scalarNativeDimension_pos s⟩⟩
  have hB : 0 ≤ Bstruct := by dsimp [Bstruct]; positivity
  have hA2 : 2 ≤ exponent := by omega
  have hstructData := hstruct basePower hBaseStruct p hp
  have hG : (Fintype.card (Fin (scalarNativeDimension s)) : ℝ) ≤ Bstruct := by
    simpa only [Fintype.card_fin] using hstructData.1
  have hX : (Fintype.card (Fin nX) : ℝ) ≤ Bstruct := by
    simpa only [Fintype.card_fin] using hnX.trans hstructData.2.2.2
  have hVars : (Fintype.card (LayerSamplerVariables
      (Fin (scalarNativeDimension s)) I₀ n₀ B₀) : ℝ) ≤ Bstruct := by
    simpa only [zeroLayerVariables_card] using hG
  obtain ⟨Plate, hPlate, hNative, hCumulative, hProfiles⟩ :=
    hFull hp hnX A₀ hξ htrim hS hSupper hN
  let seed := candidateNestedForwardSeed exponent degreeSourceCountConstants (s + 1)
  have hSeed (r : ℕ) : 0 ≤ seed r Bstruct :=
    candidateNestedForwardSeed_nonneg exponent degreeSourceCountConstants (s + 1) r hB
  have profiles (j : Fin s) := hProfiles (0 : Fin (s + 1))
    ⟨2 * j.val, by omega⟩ ⟨2 * j.val + 1, by omega⟩ (by simp only [Fin.le_def]; omega)
    (s - (j.val + 1) + 1) (by omega) (seed (2 * j.val) Bstruct) ⟨hSeed _, le_rfl⟩
  choose P hP using profiles
  let source (j : Fin s) := (P j).mono_netExponent (hSeed _)
    (candidateNestedDegreeNetExponent_le_bound s initial (Nat.le_of_lt j.isLt))
  have hinner (j : Fin s) : (source j).inner.x = seed (2 * j.val + 1) Bstruct :=
    (hP j).1
  have hgain (j : Fin s) : (source j).inner.x ≤ (source j).inner.gainLog := by
    change (P j).inner.x ≤ (P j).inner.gainLog
    rw [(hP j).1, (hP j).2.1]
  have hfit (j : Fin s) : ((source j).front.familyParameter + 2) ^ Cstep ≤
      (source j).inner.x := by
    rw [hinner j]
    exact (source j).front.familyParameter_pow_le_next_seed (max s 1) Pdetect Cstep
      exponent 1 degreeSourceCountConstants (2 * s) (s + 1) s
      ⟨2 * j.val, by omega⟩ Bstruct (scalarNativeDimension s) 0 Bstruct Bstruct Plate
      hfront (by omega) hB (by omega) (by omega)
      ⟨Nat.cast_nonneg _, by simpa only [Fintype.card_fin] using hG⟩
      ⟨le_rfl, hB⟩ ⟨hB, le_rfl⟩ ⟨hB, le_rfl⟩ (by simpa only [Nat.cast_zero] using hB)
      hVars hX hG ⟨hSeed _, le_rfl⟩ (hP j).2.2.1 (hP j).2.2.2.1
      (by simpa only [zeroLayerVariables_card, Fintype.card_fin, source,
        DegreeSourceProfile.mono_netExponent, FrontSourceProfile.mono_netExponent,
        Pdetect, Bstruct] using (hP j).2.2.2.2.1)
  have hrecursive (j : Fin s) : (source j).inner.recursiveParameter ≤
      seed (2 * (j.val + 1)) Bstruct :=
    (source j).inner.recursiveParameter_le_next_degree_seed_of_uniform
      1 exponent (s + 1) s j.val (by omega) hrec le_rfl hB
      (hP j).2.2.2.2.2.1 (hP j).2.2.2.2.2.2.1 (hinner j)
  exact hglobal (E := E₀) A₀ weight initial exponent (s + 1) Bstruct source
    hA2 hB hVars hinner hfit hgain hFinal hrecursive

end Erdos3.VectorPolynomial

end

end OAI
