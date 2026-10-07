import OAI.Combinatorics.Progressions.Dynamics.PreparedFiniteForwardPairedResourceBudget
import OAI.Combinatorics.Progressions.Estimates.AllocatedZeroLayerForwardFrontSourceProfile
import OAI.Combinatorics.Progressions.Polynomial.PreparedFiniteNestedForwardAllDegreePaddedSource
import OAI.Combinatorics.Progressions.Probability.PreparedCommonRadiusDensityCapNested

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

noncomputable def preparedFiniteForwardInnerSourceExponent (Cdirect Cresource : ℕ) : ℕ :=
  Classical.choose (exists_preparedFiniteForwardPairedResource_budget Cdirect Cresource)

theorem preparedFiniteForwardInnerSourceExponent_pos (Cdirect Cresource : ℕ) :
    2 ≤ preparedFiniteForwardInnerSourceExponent Cdirect Cresource :=
  (Classical.choose_spec (exists_preparedFiniteForwardPairedResource_budget Cdirect Cresource)).1

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (sampler : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

local notation "countConstants" => AllocatedExternalCandidateSampler.degreeSourceCountConstants
attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection

noncomputable def preparedFiniteForwardInnerSourceProfile
    (degree cutoff exponent Cprimitive Cslice Cdirect Cresource : ℕ)
    (x gainLog stageLog : ℝ) (Pmaster : ℕ → ℝ) (Plate rankThreshold : ℝ)
    (hx : 0 ≤ x) (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x)
    (hprimitive : 1 ≤ Cprimitive) (hdegree : degree ≤ cutoff)
    (hExponent : allocatedCandidateForwardScheduleExponent degree m Cprimitive
      (preparedFiniteForwardInnerSourceExponent Cdirect Cresource) 2 ≤ exponent)
    (hCslice : allocatedCandidateStageSliceExponent degree m Cprimitive ≤ Cslice)
    (hresource : ∀ r < degree,
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m r)
        (r + 1) (Pmaster r) Plate).nativeBudget ∈ Set.Icc 0
        ((preparedFiniteForwardPairedSourcePrecision exponent Cdirect countConstants r true
            x gainLog stageLog + preparedFiniteForwardWork exponent countConstants r x + Cresource) ^ Cresource))
    (hNative : ∀ r < degree, sampler.NativeDetection r
      ((preparedFiniteForwardParameter exponent countConstants r x + Cslice) ^ Cslice)
      ((preparedFiniteForwardDetectorPolynomial cutoff).eval₂ (Nat.castRingHom ℝ)
        (allocatedModelTestLog
          (preparedFiniteForwardPairedSourcePrecision exponent Cdirect countConstants r true x gainLog stageLog)
          (preparedFiniteForwardWork exponent countConstants r x)))
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m r)
        (r + 1) (Pmaster r) Plate).nativeBudget
      (Real.exp (-(2 * preparedFiniteForwardModelPrecision exponent countConstants r x gainLog stageLog +
        4 * preparedFiniteForwardWork exponent countConstants r x + 8))))
    (htags : (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ x)
    (hlayers : (m : ℝ) ≤ x)
    (hvariables : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ x)
    (hsize : ∀ i, Real.exp (preparedFiniteForwardCumulative exponent countConstants degree x) ≤ (N i : ℝ))
    (hrank : Real.exp (preparedFiniteForwardCumulative exponent countConstants degree x) ≤ rankThreshold)
    (hsampling : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) rankThreshold (U j) (poly j)) :
    sampler.InnerSourceProfile degree := by
  have hschedule := allocatedCandidateForwardScheduleExponent_bounds degree m Cprimitive
    (preparedFiniteForwardInnerSourceExponent Cdirect Cresource) 2
  refine {
    x := x
    scheduleExponent := exponent
    Cprimitive := Cprimitive
    Csource := preparedFiniteForwardInnerSourceExponent Cdirect Cresource
    gainLog := gainLog
    stageLog := stageLog
    sourceNative := fun r =>
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m r)
        (r + 1) (Pmaster r) Plate).nativeBudget
    pTest := fun r => (preparedFiniteForwardDetectorPolynomial cutoff).eval₂ (Nat.castRingHom ℝ)
      (allocatedModelTestLog
        (preparedFiniteForwardPairedSourcePrecision exponent Cdirect countConstants r true x gainLog stageLog)
        (preparedFiniteForwardWork exponent countConstants r x))
    detectionLoss := fun _ => Real.exp (-gainLog) / 2
    rankThreshold := rankThreshold
    x_nonneg := hx
    gain_range := hg
    stage_range := hs
    primitive_pos := hprimitive
    base_exponent := hschedule.2.1.trans hExponent
    slice_exponent := hschedule.2.2.1.trans hExponent
    phase_exponent := fun r hr => (hschedule.2.2.2 r hr).trans hExponent
    source_nonneg := fun r hr => (hresource r hr).1
    source_bound := ?_
    test_floor := ?_
    loss_nonneg := fun _ _ => div_nonneg (Real.exp_nonneg _) (by norm_num)
    loss_bound := fun _ _ => le_rfl
    detection := ?_
    tags_input := htags
    layers_input := hlayers
    variables_input := hvariables
    size_floor := hsize
    rank_floor := hrank
    sampling_rank := hsampling }
  · intro r hr
    exact (hresource r hr).2.trans
      ((Classical.choose_spec (exists_preparedFiniteForwardPairedResource_budget Cdirect Cresource)).2
        exponent countConstants r hx hg hs)
  · intro r hr
    exact (preparedFiniteForwardDetectorPolynomial_stage_bounds cutoff exponent Cdirect
      countConstants r true hx hg hs).2 r (hr.le.trans hdegree)
  · intro r hr
    have hb : 0 ≤ preparedFiniteForwardParameter exponent countConstants r x :=
      preparedFiniteForwardParameter_nonneg exponent countConstants r hx
    have hCtwo : 2 ≤ Cslice :=
      (allocatedCandidateStageSlice_bounds degree m Cprimitive hb).1.trans hCslice
    have hslice : allocatedCandidateStageSlice degree m Cprimitive
        (preparedFiniteForwardParameter exponent countConstants r x) ≤
        (preparedFiniteForwardParameter exponent countConstants r x + Cslice) ^ Cslice := by
      unfold allocatedCandidateStageSlice
      apply (pow_le_pow_left₀ (add_nonneg hb (Nat.cast_nonneg _))
        (add_le_add le_rfl (Nat.cast_le.mpr hCslice)) _).trans
      exact pow_le_pow_right₀ (by
        have hC : (2 : ℝ) ≤ Cslice := Nat.cast_le.mpr hCtwo
        linarith only [hb, hC]) hCslice
    exact AllocatedExternalCandidateSampler.NativeDetection.mono_tests sampler
      (hNative r hr) hslice le_rfl
      (preparedFiniteForwardInnerDetectionThreshold_bound exponent countConstants r hx hg hs)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (sampler : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

local notation "countConstants" => AllocatedExternalCandidateSampler.degreeSourceCountConstants
attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection

noncomputable def preparedFiniteForwardResourceLayerInnerSourceProfile
    (q degree cutoff exponent Cprimitive Cslice Cdirect Cresource : ℕ)
    (x gainLog stageLog : ℝ) (Pmaster : ℕ → ℝ) (Plate rankThreshold : ℝ)
    (hx : 0 ≤ x) (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x)
    (hprimitive : 1 ≤ Cprimitive) (hdegree : degree ≤ cutoff)
    (hExponent : allocatedCandidateForwardScheduleExponent degree m Cprimitive
      (preparedFiniteForwardInnerSourceExponent Cdirect Cresource) 2 ≤ exponent)
    (hCslice : allocatedCandidateStageSliceExponent degree m Cprimitive ≤ Cslice)
    (hresource : ∀ r < degree,
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants q r)
        (r + 1) (Pmaster r) Plate).nativeBudget ∈ Set.Icc 0
        ((preparedFiniteForwardPairedSourcePrecision exponent Cdirect countConstants r true
            x gainLog stageLog + preparedFiniteForwardWork exponent countConstants r x + Cresource) ^ Cresource))
    (hNative : ∀ r < degree, sampler.NativeDetection r
      ((preparedFiniteForwardParameter exponent countConstants r x + Cslice) ^ Cslice)
      ((preparedFiniteForwardDetectorPolynomial cutoff).eval₂ (Nat.castRingHom ℝ)
        (allocatedModelTestLog
          (preparedFiniteForwardPairedSourcePrecision exponent Cdirect countConstants r true x gainLog stageLog)
          (preparedFiniteForwardWork exponent countConstants r x)))
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants q r)
        (r + 1) (Pmaster r) Plate).nativeBudget
      (Real.exp (-(2 * preparedFiniteForwardModelPrecision exponent countConstants r x gainLog stageLog +
        4 * preparedFiniteForwardWork exponent countConstants r x + 8))))
    (htags : (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ x)
    (hlayers : (m : ℝ) ≤ x)
    (hvariables : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ x)
    (hsize : ∀ i, Real.exp (preparedFiniteForwardCumulative exponent countConstants degree x) ≤ (N i : ℝ))
    (hrank : Real.exp (preparedFiniteForwardCumulative exponent countConstants degree x) ≤ rankThreshold)
    (hsampling : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) rankThreshold (U j) (poly j)) :
    sampler.InnerSourceProfile degree := by
  have hschedule := allocatedCandidateForwardScheduleExponent_bounds degree m Cprimitive
    (preparedFiniteForwardInnerSourceExponent Cdirect Cresource) 2
  refine {
    x := x
    scheduleExponent := exponent
    Cprimitive := Cprimitive
    Csource := preparedFiniteForwardInnerSourceExponent Cdirect Cresource
    gainLog := gainLog
    stageLog := stageLog
    sourceNative := fun r =>
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants q r)
        (r + 1) (Pmaster r) Plate).nativeBudget
    pTest := fun r => (preparedFiniteForwardDetectorPolynomial cutoff).eval₂ (Nat.castRingHom ℝ)
      (allocatedModelTestLog
        (preparedFiniteForwardPairedSourcePrecision exponent Cdirect countConstants r true x gainLog stageLog)
        (preparedFiniteForwardWork exponent countConstants r x))
    detectionLoss := fun _ => Real.exp (-gainLog) / 2
    rankThreshold := rankThreshold
    x_nonneg := hx
    gain_range := hg
    stage_range := hs
    primitive_pos := hprimitive
    base_exponent := hschedule.2.1.trans hExponent
    slice_exponent := hschedule.2.2.1.trans hExponent
    phase_exponent := fun r hr => (hschedule.2.2.2 r hr).trans hExponent
    source_nonneg := fun r hr => (hresource r hr).1
    source_bound := ?_
    test_floor := ?_
    loss_nonneg := fun _ _ => div_nonneg (Real.exp_nonneg _) (by norm_num)
    loss_bound := fun _ _ => le_rfl
    detection := ?_
    tags_input := htags
    layers_input := hlayers
    variables_input := hvariables
    size_floor := hsize
    rank_floor := hrank
    sampling_rank := hsampling }
  · intro r hr
    exact (hresource r hr).2.trans
      ((Classical.choose_spec (exists_preparedFiniteForwardPairedResource_budget Cdirect Cresource)).2
        exponent countConstants r hx hg hs)
  · intro r hr
    exact (preparedFiniteForwardDetectorPolynomial_stage_bounds cutoff exponent Cdirect
      countConstants r true hx hg hs).2 r (hr.le.trans hdegree)
  · intro r hr
    have hb : 0 ≤ preparedFiniteForwardParameter exponent countConstants r x :=
      preparedFiniteForwardParameter_nonneg exponent countConstants r hx
    have hCtwo : 2 ≤ Cslice :=
      (allocatedCandidateStageSlice_bounds degree m Cprimitive hb).1.trans hCslice
    have hslice : allocatedCandidateStageSlice degree m Cprimitive
        (preparedFiniteForwardParameter exponent countConstants r x) ≤
        (preparedFiniteForwardParameter exponent countConstants r x + Cslice) ^ Cslice := by
      unfold allocatedCandidateStageSlice
      apply (pow_le_pow_left₀ (add_nonneg hb (Nat.cast_nonneg _))
        (add_le_add le_rfl (Nat.cast_le.mpr hCslice)) _).trans
      exact pow_le_pow_right₀ (by
        have hC : (2 : ℝ) ≤ Cslice := Nat.cast_le.mpr hCtwo
        linarith only [hb, hC]) hCslice
    exact AllocatedExternalCandidateSampler.NativeDetection.mono_tests sampler
      (hNative r hr) hslice le_rfl
      (preparedFiniteForwardInnerDetectionThreshold_bound exponent countConstants r hx hg hs)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

noncomputable def preparedFiniteForwardActualLocalMaster
    (m : ℕ) (G : Type) [Fintype G] (count nX : ℕ) (Pdetect : Polynomial ℕ)
    (exponent Cdirect : ℕ) (stageCountConstant : ℕ → ℕ) (r : ℕ)
    (x gainLog stageLog Bstruct pnum Pchart Qstride : ℝ) : ℝ :=
  let u := preparedFiniteForwardPairedSourcePrecision exponent Cdirect stageCountConstant r
    true x gainLog stageLog
  let pModel := preparedFiniteForwardWork exponent stageCountConstant r x
  let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
  let D := allocatedComparisonDimension m pnum
  let pDetect := allocatedModelTestLog u pModel
  let gain := slicedDetectionGainLog r (sampledSupportedSlicedDetectionConstant r Pdetect) count
    pDetect pDetect (2 * u + 4 * pModel + 7)
  let Pk := scalarKernelLogarithmicBudget (Fin (r + 1)) G (gain + pDetect + 4)
  let Pphysical := preparedFiniteScheduleLocalPhysical m nX count Qstride Pk
  let target := gain + 40 + coefficientErrorSpatialLog Pphysical
  let Eprofile := target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5
  let Prho := 2 * affineProfileInputEnvelope D
    (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ)
    Eprofile (pDetect + 2) + 2
  preparedFiniteScheduleLocalMaster Pchart D pRadius Qstride Pphysical u pModel Prho target gain

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (sampler : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

local notation "countConstants" => AllocatedExternalCandidateSampler.degreeSourceCountConstants
attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection

noncomputable def preparedFiniteForwardActualInnerSourceProfile
    (degree cutoff exponent Cprimitive Cslice Cdirect : ℕ)
    (x gainLog stageLog Bstruct pnum Pchart Qstride Plate rankThreshold : ℝ)
    (hx : 0 ≤ x) (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x)
    (hprimitive : 1 ≤ Cprimitive) (hdegree : degree ≤ cutoff) (hcutoff : cutoff ≤ m)
    (hBstruct : Bstruct ∈ Set.Icc 0 x) (hpnum : pnum ∈ Set.Icc 0 x)
    (hPchart : Pchart ∈ Set.Icc 0 x) (hQstride : Qstride ∈ Set.Icc 0 x)
    (hG : (Fintype.card G : ℝ) ≤ x)
    (hExponent : allocatedCandidateForwardScheduleExponent degree m Cprimitive
      (preparedFiniteForwardInnerSourceExponent Cdirect
        (preparedFiniteForwardActualNativeBudgetExponent m
          (preparedFiniteForwardDetectorPolynomial cutoff))) 2 ≤ exponent)
    (hCslice : allocatedCandidateStageSliceExponent degree m Cprimitive ≤ Cslice)
    (hNative : ∀ r < degree, sampler.NativeDetection r
      ((preparedFiniteForwardParameter exponent countConstants r x + Cslice) ^ Cslice)
      ((preparedFiniteForwardDetectorPolynomial cutoff).eval₂ (Nat.castRingHom ℝ)
        (allocatedModelTestLog
          (preparedFiniteForwardPairedSourcePrecision exponent Cdirect countConstants r true x gainLog stageLog)
          (preparedFiniteForwardWork exponent countConstants r x)))
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m r)
        (r + 1)
        (preparedFiniteForwardActualLocalMaster m G
          (Fintype.card (LayerSamplerVariables G I n B)) (Fintype.card X)
          (preparedFiniteForwardDetectorPolynomial cutoff) exponent Cdirect countConstants r
          x gainLog stageLog Bstruct pnum Pchart Qstride) Plate).nativeBudget
      (Real.exp (-(2 * preparedFiniteForwardModelPrecision exponent countConstants r x gainLog stageLog +
        4 * preparedFiniteForwardWork exponent countConstants r x + 8))))
    (htags : (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ x)
    (hlayers : (m : ℝ) ≤ x)
    (hvariables : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ x)
    (hsize : ∀ i, Real.exp (preparedFiniteForwardCumulative exponent countConstants degree x) ≤ (N i : ℝ))
    (hrank : Real.exp (preparedFiniteForwardCumulative exponent countConstants degree x) ≤ rankThreshold)
    (hsampling : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) rankThreshold (U j) (poly j)) :
    sampler.InnerSourceProfile degree := by
  let Pdetect := preparedFiniteForwardDetectorPolynomial cutoff
  let Cresource := preparedFiniteForwardActualNativeBudgetExponent m Pdetect
  let Pmaster := fun r => preparedFiniteForwardActualLocalMaster m G
    (Fintype.card (LayerSamplerVariables G I n B)) (Fintype.card X)
    Pdetect exponent Cdirect countConstants r x gainLog stageLog Bstruct pnum Pchart Qstride
  have hExponentTwo : 2 ≤ exponent :=
    (allocatedCandidateForwardScheduleExponent_bounds degree m Cprimitive
      (preparedFiniteForwardInnerSourceExponent Cdirect Cresource) 2).1.trans hExponent
  have hX : (Fintype.card X : ℝ) ≤ x := by
    have hXtags : Fintype.card X ≤ Fintype.card (X ⊕ (Σ j, J j)) := by
      rw [Fintype.card_sum]
      exact Nat.le_add_right _ _
    exact (Nat.cast_le.mpr hXtags).trans htags
  have hresource (r : ℕ) (hr : r < degree) :
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m r)
        (r + 1) (Pmaster r) Plate).nativeBudget ∈ Set.Icc 0
        ((preparedFiniteForwardPairedSourcePrecision exponent Cdirect countConstants r true
            x gainLog stageLog + preparedFiniteForwardWork exponent countConstants r x + Cresource) ^ Cresource) := by
    have hrm : r < m + 1 := Nat.lt_succ_of_le ((Nat.le_of_lt hr).trans (hdegree.trans hcutoff))
    have h := (Classical.choose_spec (exists_preparedFiniteForwardActualNativeBudget m Pdetect)).2
      ⟨r, hrm⟩ exponent Cdirect countConstants r true
      (G := G) hExponentTwo hx hg hs hBstruct hpnum hPchart hQstride
      hvariables hX hG Plate
    exact h.2.2.1
  exact preparedFiniteForwardInnerSourceProfile sampler degree cutoff exponent Cprimitive Cslice
    Cdirect Cresource x gainLog stageLog Pmaster Plate rankThreshold
    hx hg hs hprimitive hdegree hExponent hCslice hresource hNative htags hlayers
    hvariables hsize hrank hsampling

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (sampler : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

local notation "countConstants" => AllocatedExternalCandidateSampler.degreeSourceCountConstants
attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection

noncomputable def preparedFiniteForwardActualResourceLayerInnerSourceProfile
    (q degree cutoff exponent Cprimitive Cslice Cdirect : ℕ)
    (x gainLog stageLog Bstruct pnum Pchart Qstride Plate rankThreshold : ℝ)
    (hx : 0 ≤ x) (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x)
    (hprimitive : 1 ≤ Cprimitive) (hdegree : degree ≤ cutoff) (hcutoff : cutoff ≤ q)
    (hBstruct : Bstruct ∈ Set.Icc 0 x) (hpnum : pnum ∈ Set.Icc 0 x)
    (hPchart : Pchart ∈ Set.Icc 0 x) (hQstride : Qstride ∈ Set.Icc 0 x)
    (hG : (Fintype.card G : ℝ) ≤ x)
    (hExponent : allocatedCandidateForwardScheduleExponent degree m Cprimitive
      (preparedFiniteForwardInnerSourceExponent Cdirect
        (preparedFiniteForwardActualNativeBudgetExponent q
          (preparedFiniteForwardDetectorPolynomial cutoff))) 2 ≤ exponent)
    (hCslice : allocatedCandidateStageSliceExponent degree m Cprimitive ≤ Cslice)
    (hNative : ∀ r < degree, sampler.NativeDetection r
      ((preparedFiniteForwardParameter exponent countConstants r x + Cslice) ^ Cslice)
      ((preparedFiniteForwardDetectorPolynomial cutoff).eval₂ (Nat.castRingHom ℝ)
        (allocatedModelTestLog
          (preparedFiniteForwardPairedSourcePrecision exponent Cdirect countConstants r true x gainLog stageLog)
          (preparedFiniteForwardWork exponent countConstants r x)))
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants q r)
        (r + 1)
        (preparedFiniteForwardActualLocalMaster q G
          (Fintype.card (LayerSamplerVariables G I n B)) (Fintype.card X)
          (preparedFiniteForwardDetectorPolynomial cutoff) exponent Cdirect countConstants r
          x gainLog stageLog Bstruct pnum Pchart Qstride) Plate).nativeBudget
      (Real.exp (-(2 * preparedFiniteForwardModelPrecision exponent countConstants r x gainLog stageLog +
        4 * preparedFiniteForwardWork exponent countConstants r x + 8))))
    (htags : (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ x)
    (hlayers : (m : ℝ) ≤ x)
    (hvariables : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ x)
    (hsize : ∀ i, Real.exp (preparedFiniteForwardCumulative exponent countConstants degree x) ≤ (N i : ℝ))
    (hrank : Real.exp (preparedFiniteForwardCumulative exponent countConstants degree x) ≤ rankThreshold)
    (hsampling : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) rankThreshold (U j) (poly j)) :
    sampler.InnerSourceProfile degree := by
  let Pdetect := preparedFiniteForwardDetectorPolynomial cutoff
  let Cresource := preparedFiniteForwardActualNativeBudgetExponent q Pdetect
  let Pmaster := fun r => preparedFiniteForwardActualLocalMaster q G
    (Fintype.card (LayerSamplerVariables G I n B)) (Fintype.card X)
    Pdetect exponent Cdirect countConstants r x gainLog stageLog Bstruct pnum Pchart Qstride
  have hExponentTwo : 2 ≤ exponent :=
    (allocatedCandidateForwardScheduleExponent_bounds degree m Cprimitive
      (preparedFiniteForwardInnerSourceExponent Cdirect Cresource) 2).1.trans hExponent
  have hX : (Fintype.card X : ℝ) ≤ x := by
    have hXtags : Fintype.card X ≤ Fintype.card (X ⊕ (Σ j, J j)) := by
      rw [Fintype.card_sum]
      exact Nat.le_add_right _ _
    exact (Nat.cast_le.mpr hXtags).trans htags
  have hresource (r : ℕ) (hr : r < degree) :
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants q r)
        (r + 1) (Pmaster r) Plate).nativeBudget ∈ Set.Icc 0
        ((preparedFiniteForwardPairedSourcePrecision exponent Cdirect countConstants r true
            x gainLog stageLog + preparedFiniteForwardWork exponent countConstants r x + Cresource) ^ Cresource) := by
    have hrq : r < q + 1 := Nat.lt_succ_of_le ((Nat.le_of_lt hr).trans (hdegree.trans hcutoff))
    have h := (Classical.choose_spec (exists_preparedFiniteForwardActualNativeBudget q Pdetect)).2
      ⟨r, hrq⟩ exponent Cdirect countConstants r true
      (G := G) hExponentTwo hx hg hs hBstruct hpnum hPchart hQstride
      hvariables hX hG Plate
    exact h.2.2.1
  exact preparedFiniteForwardResourceLayerInnerSourceProfile sampler q degree cutoff exponent Cprimitive Cslice
    Cdirect Cresource x gainLog stageLog Pmaster Plate rankThreshold
    hx hg hs hprimitive hdegree hExponent hCslice hresource hNative htags hlayers
    hvariables hsize hrank hsampling

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

noncomputable def preparedFiniteNestedSourceSliceExponent
    (m cutoff Cprimitive : ℕ) : ℕ :=
  1 + ∑ d : Fin (cutoff + 1), allocatedCandidateStageSliceExponent d.val m Cprimitive

noncomputable def preparedFiniteNestedSourceNativeExponent
    (m cutoff Cdirect : ℕ) : ℕ :=
  preparedFiniteForwardInnerSourceExponent Cdirect
    (preparedFiniteForwardActualNativeBudgetExponent m (preparedFiniteForwardDetectorPolynomial cutoff))

noncomputable def preparedFiniteNestedSourceExponent
    (m cutoff e Cprimitive Cdirect extra : ℕ) : ℕ :=
  2 + extra + preparedFiniteForwardFrontProfileExponent e +
    preparedCommonRadiusDensityCapNestedExponent m +
    preparedFiniteNestedSourceSliceExponent m cutoff Cprimitive + 1 +
    ∑ d : Fin (cutoff + 1), allocatedCandidateForwardScheduleExponent d.val m Cprimitive
      (preparedFiniteNestedSourceNativeExponent m cutoff Cdirect) 2

theorem preparedFiniteNestedSourceSliceExponent_bounds (m cutoff Cprimitive : ℕ) :
    1 ≤ preparedFiniteNestedSourceSliceExponent m cutoff Cprimitive ∧
    ∀ d ≤ cutoff, allocatedCandidateStageSliceExponent d m Cprimitive ≤
      preparedFiniteNestedSourceSliceExponent m cutoff Cprimitive := by
  constructor
  · unfold preparedFiniteNestedSourceSliceExponent
    omega
  · intro d hd
    have hsum := Finset.single_le_sum
      (f := fun i : Fin (cutoff + 1) => allocatedCandidateStageSliceExponent i.val m Cprimitive)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ (⟨d, Nat.lt_succ_of_le hd⟩ : Fin (cutoff + 1)))
    unfold preparedFiniteNestedSourceSliceExponent
    exact hsum.trans (Nat.le_add_left _ _)

theorem preparedFiniteNestedSourceExponent_bounds
    (m cutoff e Cprimitive Cdirect extra A : ℕ)
    (hA : preparedFiniteNestedSourceExponent m cutoff e Cprimitive Cdirect extra ≤ A) :
    2 ≤ A ∧ extra ≤ A ∧ preparedFiniteForwardFrontProfileExponent e ≤ A ∧
    preparedCommonRadiusDensityCapNestedExponent m ≤ A ∧
    preparedFiniteNestedSourceSliceExponent m cutoff Cprimitive + 1 ≤ A ∧
    ∀ d ≤ cutoff, allocatedCandidateForwardScheduleExponent d m Cprimitive
      (preparedFiniteNestedSourceNativeExponent m cutoff Cdirect) 2 ≤ A := by
  have hfields : 2 ≤ A ∧ extra ≤ A ∧ preparedFiniteForwardFrontProfileExponent e ≤ A ∧
      preparedCommonRadiusDensityCapNestedExponent m ≤ A ∧
      preparedFiniteNestedSourceSliceExponent m cutoff Cprimitive + 1 ≤ A := by
    unfold preparedFiniteNestedSourceExponent at hA
    omega
  refine ⟨hfields.1, hfields.2.1, hfields.2.2.1, hfields.2.2.2.1,
    hfields.2.2.2.2, ?_⟩
  intro d hd
  have hsum := Finset.single_le_sum
    (f := fun i : Fin (cutoff + 1) => allocatedCandidateForwardScheduleExponent i.val m Cprimitive
      (preparedFiniteNestedSourceNativeExponent m cutoff Cdirect) 2)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ (⟨d, Nat.lt_succ_of_le hd⟩ : Fin (cutoff + 1)))
  change allocatedCandidateForwardScheduleExponent d m Cprimitive
    (preparedFiniteNestedSourceNativeExponent m cutoff Cdirect) 2 ≤ _ at hsum
  unfold preparedFiniteNestedSourceExponent at hA
  omega

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

noncomputable def preparedFiniteNestedResourceLayerSourceExponent
    (m q cutoff e Cprimitive Cdirect extra : ℕ) : ℕ :=
  2 + extra + preparedFiniteForwardFrontProfileExponent e +
    preparedFiniteNestedSourceSliceExponent m cutoff Cprimitive + 1 +
    ∑ d : Fin (cutoff + 1), allocatedCandidateForwardScheduleExponent d.val m Cprimitive
      (preparedFiniteNestedSourceNativeExponent q cutoff Cdirect) 2

theorem preparedFiniteNestedResourceLayerSourceExponent_bounds
    (m q cutoff e Cprimitive Cdirect extra A : ℕ)
    (hA : preparedFiniteNestedResourceLayerSourceExponent
      m q cutoff e Cprimitive Cdirect extra ≤ A) :
    2 ≤ A ∧ extra ≤ A ∧ preparedFiniteForwardFrontProfileExponent e ≤ A ∧
    preparedFiniteNestedSourceSliceExponent m cutoff Cprimitive + 1 ≤ A ∧
    ∀ d ≤ cutoff, allocatedCandidateForwardScheduleExponent d m Cprimitive
      (preparedFiniteForwardInnerSourceExponent Cdirect
        (preparedFiniteForwardActualNativeBudgetExponent q
          (preparedFiniteForwardDetectorPolynomial cutoff))) 2 ≤ A := by
  have hfields : 2 ≤ A ∧ extra ≤ A ∧ preparedFiniteForwardFrontProfileExponent e ≤ A ∧
      preparedFiniteNestedSourceSliceExponent m cutoff Cprimitive + 1 ≤ A := by
    unfold preparedFiniteNestedResourceLayerSourceExponent at hA
    omega
  refine ⟨hfields.1, hfields.2.1, hfields.2.2.1, hfields.2.2.2, ?_⟩
  intro d hd
  have hsum := Finset.single_le_sum
    (f := fun i : Fin (cutoff + 1) => allocatedCandidateForwardScheduleExponent i.val m Cprimitive
      (preparedFiniteNestedSourceNativeExponent q cutoff Cdirect) 2)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ (⟨d, Nat.lt_succ_of_le hd⟩ : Fin (cutoff + 1)))
  change allocatedCandidateForwardScheduleExponent d m Cprimitive
    (preparedFiniteNestedSourceNativeExponent q cutoff Cdirect) 2 ≤ _ at hsum
  change allocatedCandidateForwardScheduleExponent d m Cprimitive
    (preparedFiniteNestedSourceNativeExponent q cutoff Cdirect) 2 ≤ A
  unfold preparedFiniteNestedResourceLayerSourceExponent at hA
  omega

theorem preparedFiniteNestedResourceLayerSourceSliceExponent_bounds
    (m cutoff Cprimitive : ℕ) :
    1 ≤ preparedFiniteNestedSourceSliceExponent m cutoff Cprimitive ∧
    ∀ d ≤ cutoff, allocatedCandidateStageSliceExponent d m Cprimitive ≤
      preparedFiniteNestedSourceSliceExponent m cutoff Cprimitive :=
  preparedFiniteNestedSourceSliceExponent_bounds m cutoff Cprimitive

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

noncomputable def preparedFiniteNestedSourceMaster
    (m : ℕ) (G : Type) [Fintype G] (count nX : ℕ) (Pdetect : Polynomial ℕ)
    (A Cdirect : ℕ) (constants : ℕ → ℕ)
    (Bstruct pnum Qstride gainLog stageLog : ℝ)
    {outerDepth innerDepth cutoff : ℕ}
    (k : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff) : ℝ :=
  let degree := preparedFiniteNestedForwardAllDegreeDegree k
  let u := preparedFiniteForwardPairedSourcePrecision A Cdirect constants
    (preparedFiniteNestedForwardAllDegreeStage k).val
    (preparedFiniteNestedForwardAllDegreeIsDirect k)
    (preparedFiniteNestedForwardAllDegreeSeed A constants Bstruct k) gainLog stageLog
  let pModel := preparedFiniteForwardWork A constants
    (preparedFiniteNestedForwardAllDegreeStage k).val
    (preparedFiniteNestedForwardAllDegreeSeed A constants Bstruct k)
  let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
  let D := allocatedComparisonDimension m pnum
  let pDetect := allocatedModelTestLog u pModel
  let gain := slicedDetectionGainLog degree
    (sampledSupportedSlicedDetectionConstant degree Pdetect) count
    pDetect pDetect (2 * u + 4 * pModel + 7)
  let Pk := scalarKernelLogarithmicBudget (Fin (degree + 1)) G (gain + pDetect + 4)
  let Pphysical := preparedFiniteScheduleLocalPhysical m nX count Qstride Pk
  let target := gain + 40 + coefficientErrorSpatialLog Pphysical
  let Eprofile := target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5
  let Prho := 2 * affineProfileInputEnvelope D
    (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ)
    Eprofile (pDetect + 2) + 2
  preparedFiniteScheduleLocalMaster Bstruct D pRadius Qstride
    Pphysical u pModel Prho target gain

noncomputable def preparedFiniteNestedSourceNative
    (m : ℕ) (G : Type) [Fintype G] (count nX : ℕ) (Pdetect : Polynomial ℕ)
    (A Cdirect : ℕ) (constants : ℕ → ℕ)
    (Bstruct pnum Qstride gainLog stageLog Plate : ℝ)
    {outerDepth innerDepth cutoff : ℕ}
    (k : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff) : ℝ :=
  (preparedModularGeneralDetectorResources
    (preparedModularGeneralDetectorConstants m
      (preparedFiniteNestedForwardAllDegreeDegree k))
    (preparedFiniteNestedForwardAllDegreeDegree k + 1)
    (preparedFiniteNestedSourceMaster m G count nX Pdetect A Cdirect constants
      Bstruct pnum Qstride gainLog stageLog k) Plate).nativeBudget

@[simp] theorem preparedFiniteNestedSourceMaster_front
    (m : ℕ) (G : Type) [Fintype G] (count nX : ℕ) (Pdetect : Polynomial ℕ)
    (A Cdirect : ℕ) (constants : ℕ → ℕ)
    (Bstruct pnum Qstride gainLog stageLog : ℝ)
    {outerDepth innerDepth cutoff : ℕ}
    (outer : Fin (outerDepth + 1)) (degree : Fin (cutoff + 1)) :
    preparedFiniteNestedSourceMaster m G count nX Pdetect A Cdirect constants
      Bstruct pnum Qstride gainLog stageLog
      (outer, (0 : Fin (innerDepth + 1)), degree, false) =
    preparedFiniteForwardActualFrontLocalMaster m G count nX Pdetect
      A Cdirect constants degree.val
      (candidateNestedForwardSeed A constants innerDepth outer.val Bstruct)
      gainLog stageLog Bstruct pnum Bstruct Qstride := rfl

@[simp] theorem preparedFiniteNestedSourceMaster_direct
    (m : ℕ) (G : Type) [Fintype G] (count nX : ℕ) (Pdetect : Polynomial ℕ)
    (A Cdirect : ℕ) (constants : ℕ → ℕ)
    (Bstruct pnum Qstride gainLog stageLog : ℝ)
    {outerDepth innerDepth cutoff : ℕ}
    (outer : Fin (outerDepth + 1)) (r : ℕ)
    (hrInner : r < innerDepth + 1) (hrDegree : r < cutoff + 1) :
    preparedFiniteNestedSourceMaster m G count nX Pdetect A Cdirect constants
      Bstruct pnum Qstride gainLog stageLog
      (outer, (⟨r, hrInner⟩ : Fin (innerDepth + 1)),
        (⟨r, hrDegree⟩ : Fin (cutoff + 1)), true) =
    preparedFiniteForwardActualLocalMaster m G count nX Pdetect
      A Cdirect constants r
      (candidateNestedForwardSeed A constants innerDepth outer.val Bstruct)
      gainLog stageLog Bstruct pnum Bstruct Qstride := rfl

end Erdos3.VectorPolynomial

end

end OAI
