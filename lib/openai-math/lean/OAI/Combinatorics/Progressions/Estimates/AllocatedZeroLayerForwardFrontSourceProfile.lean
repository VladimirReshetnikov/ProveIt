import OAI.Combinatorics.Progressions.Dynamics.PreparedFiniteForwardActualNativeBudget
import OAI.Combinatorics.Progressions.Dynamics.PreparedFiniteForwardFrontProfileBudget
import OAI.Combinatorics.Progressions.Polynomial.AllocatedNestedDegreeInduction

namespace OAI

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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateSampler

local instance preparedFrontSourceProfileSiteNonempty : Nonempty A.Site := A.site_nonempty

noncomputable def preparedFixedCenterFrontSourceProfile
    {degree e : ℕ} {p u pModel sliceBudget testBudget nativeBudget projectionPrecision
      E rawCap α : ℝ}
    (hξone : ξ ≤ 1)
    (hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x)
    (hu : 0 ≤ u) (hpModel : 0 ≤ pModel) (hInputModel : 2 * p + 3 ≤ pModel)
    (hNative : 0 ≤ nativeBudget)
    (hSliceNonneg : 0 ≤ sliceBudget) (hTestNontrivial : 2 ≤ testBudget)
    (hSliceLog : sliceBudget * Fintype.card (LayerSamplerVariables G I n B) ≤ pModel)
    (hRawCap : rawCap ≤ Real.exp pModel)
    (hPrecision : u + 2 * pModel + max (max nativeBudget 3)
      (2 * u + 4 * pModel + 20) + 32 ≤ projectionPrecision)
    (hProjection : projectionPrecision ≤ E)
    (hdirect : A.NativeDetection degree sliceBudget testBudget nativeBudget α)
    (hThreshold : α ≤ Real.exp (-(2 * u + 4 * pModel + 8)))
    (hexcess :
      (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
        (A.law.siteLaw (A.physicalBox hξone hmargin)) rawCap ≤
          6 * positiveProjectionAccuracy E)
    (hInputSlice : p ≤ sliceBudget)
    (hProjectionTest :
      AllocatedExternalCandidateProblem.positiveKernelPreparationParameter (2 * p) ≤ testBudget)
    (hMarkovPrecision :
      AllocatedExternalCandidateProblem.positiveKernelMarkovPrecisionParameter (2 * p) e ≤ u) :
    A.FrontSourceProfile degree p e := by
  have hcap := marginalCap_max_one_exp_bound hpModel hRawCap
  have haccuracy : positiveProjectionAccuracy E ≤ positiveProjectionAccuracy projectionPrecision := by
    unfold positiveProjectionAccuracy
    apply Real.exp_le_exp.mpr
    linarith only [hProjection]
  have hexcess' :
      (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
        (A.law.siteLaw (A.physicalBox hξone (fun x => (A.trimMargin_proper x).le)))
        (max 1 rawCap) ≤ 6 * positiveProjectionAccuracy projectionPrecision :=
    ((FiniteProbabilityWeights.excessMass_max_one_le
      (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty)
      (A.law.siteLaw (A.physicalBox hξone hmargin)) rawCap).trans hexcess).trans
      (mul_le_mul_of_nonneg_left haccuracy (by norm_num))
  exact {
    u := u
    pModel := pModel
    sliceBudget := sliceBudget
    testBudget := testBudget
    nativeBudget := nativeBudget
    projectionPrecision := projectionPrecision
    marginalCap := max 1 rawCap
    narrow := hξone
    u_nonneg := hu
    model_nonneg := hpModel
    input_model := hInputModel
    native_nonneg := hNative
    slice_nonneg := hSliceNonneg
    test_nontrivial := hTestNontrivial
    slice_log := hSliceLog
    marginal_one := hcap.1
    marginal_bound := hcap.2
    projection_precision := hPrecision
    detection := hdirect.mono_tests A le_rfl le_rfl hThreshold
    physical_excess := hexcess'
    input_slice := hInputSlice
    projection_test := hProjectionTest
    markov_precision := hMarkovPrecision }

end AllocatedExternalCandidateSampler
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

namespace AllocatedExternalCandidateSampler
local instance forwardFrontSourceSiteNonempty : Nonempty sampler.Site := sampler.site_nonempty

variable (cutoff A Cslice : ℕ) (constants : ℕ → ℕ)
    {x p gainLog stageLog native E rawCap : ℝ} {degree e : ℕ}

local notation "work" => preparedFiniteForwardWork A constants 0 x
local notation "modelPrecision" => preparedFiniteForwardModelPrecision A constants 0 x gainLog stageLog
local notation "sourcePrecision" => preparedFiniteForwardSourcePrecision A constants 0 x gainLog stageLog
local notation "slice" => (x + Cslice) ^ Cslice
local notation "test" => Polynomial.eval₂ (Nat.castRingHom ℝ)
    (allocatedModelTestLog sourcePrecision work) (preparedFiniteForwardDetectorPolynomial cutoff)

noncomputable def preparedFiniteForwardFrontSourceProfile
    (hA : preparedFiniteForwardFrontProfileExponent e ≤ A)
    (hCslice : 1 ≤ Cslice) (hSliceExponent : Cslice + 1 ≤ A)
    (hx : 0 ≤ x) (hp : p ∈ Set.Icc 0 x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x)
    (hvariables : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ x)
    (hξ : ξ ≤ 1) (hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i)
    (hnative : 0 ≤ native) (hcap : rawCap ≤ Real.exp work)
    (hprojection : modelPrecision + 2 * work + max (max native 3)
      (2 * modelPrecision + 4 * work + 20) + 32 ≤ E)
    (hdetection : sampler.NativeDetection degree slice test native
      (Real.exp (-(2 * modelPrecision + 4 * work + 8))))
    (hexcess :
      (FiniteProbabilityWeights.uniformFinset (integerBox N) sampler.integerBox_nonempty).excessMass
        (sampler.law.siteLaw (sampler.physicalBox hξ hmargin)) rawCap ≤
          6 * positiveProjectionAccuracy E) : sampler.FrontSourceProfile degree p e := by
  have hAtwo : 2 ≤ A := (preparedFiniteForwardFrontProfileExponent_two_le e).trans hA
  have hw : 0 ≤ work := preparedFiniteForwardWork_nonneg A constants 0 hx
  have hprecision := preparedFiniteForward_model_precision_bounds A constants 0 hx hg hs
  have hfront := preparedFiniteForwardFrontProfile_bounds e A constants hA hx hp hg hs
  have hslice := preparedFiniteForward_controlled_slice_bounds A Cslice constants 0
    (Fintype.card (LayerSamplerVariables G I n B)) hAtwo hSliceExponent hx hvariables
  have htest := (preparedFiniteForwardDetectorPolynomial_bounds cutoff hprecision.2.1 hw).1
  have hslice0 : 0 ≤ slice := by
    simpa only [preparedFiniteForwardParameter_zero] using hslice.1
  have hsliceLoss : slice * Fintype.card (LayerSamplerVariables G I n B) ≤ work := by
    simpa only [preparedFiniteForwardParameter_zero] using hslice.2.2
  have htwo : 2 ≤ test := by linarith only [hp.1, hfront.1, htest]
  exact sampler.preparedFixedCenterFrontSourceProfile
    hξ hmargin hprecision.1 hw hfront.1 hnative hslice0 htwo hsliceLoss
    hcap hprojection le_rfl hdetection le_rfl hexcess
    (preparedFiniteForwardFrontProfile_slice_bound Cslice hCslice hx hp.2)
    (hfront.2.1.trans htest) hfront.2.2

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

noncomputable def preparedFiniteForwardActualFrontLocalMaster
    (m : ℕ) (G : Type) [Fintype G] (count nX : ℕ) (Pdetect : Polynomial ℕ)
    (exponent Cdirect : ℕ) (stageCountConstant : ℕ → ℕ) (degree : ℕ)
    (x gainLog stageLog Bstruct pnum Pchart Qstride : ℝ) : ℝ :=
  let u := preparedFiniteForwardPairedSourcePrecision exponent Cdirect stageCountConstant 0
    false x gainLog stageLog
  let pModel := preparedFiniteForwardWork exponent stageCountConstant 0 x
  let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
  let D := allocatedComparisonDimension m pnum
  let pDetect := allocatedModelTestLog u pModel
  let gain := slicedDetectionGainLog degree (sampledSupportedSlicedDetectionConstant degree Pdetect) count
    pDetect pDetect (2 * u + 4 * pModel + 7)
  let Pk := scalarKernelLogarithmicBudget (Fin (degree + 1)) G (gain + pDetect + 4)
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

namespace AllocatedExternalCandidateSampler
local instance actualForwardFrontSourceSiteNonempty : Nonempty sampler.Site := sampler.site_nonempty

variable (cutoff exponent Cslice Cdirect : ℕ) (constants : ℕ → ℕ)
    {x p gainLog stageLog Bstruct pnum Pchart Qstride Plate E rawCap : ℝ} {degree e : ℕ}

local notation "work" => preparedFiniteForwardWork exponent constants 0 x
local notation "modelPrecision" => preparedFiniteForwardModelPrecision exponent constants 0 x gainLog stageLog
local notation "sourcePrecision" => preparedFiniteForwardSourcePrecision exponent constants 0 x gainLog stageLog
local notation "slice" => (x + Cslice) ^ Cslice
local notation "test" => Polynomial.eval₂ (Nat.castRingHom ℝ)
    (allocatedModelTestLog sourcePrecision work) (preparedFiniteForwardDetectorPolynomial cutoff)
local notation "master" => preparedFiniteForwardActualFrontLocalMaster m G
    (Fintype.card (LayerSamplerVariables G I n B)) (Fintype.card X)
    (preparedFiniteForwardDetectorPolynomial cutoff) exponent Cdirect constants degree
    x gainLog stageLog Bstruct pnum Pchart Qstride
local notation "native" => PreparedModularCanonicalDetectorResources.nativeBudget
    (preparedModularGeneralDetectorResources
      (preparedModularGeneralDetectorConstants m degree) (degree + 1) master Plate)
attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection

noncomputable def preparedFiniteForwardActualFrontSourceProfile
    (hExponent : preparedFiniteForwardFrontProfileExponent e ≤ exponent)
    (hCslice : 1 ≤ Cslice) (hSliceExponent : Cslice + 1 ≤ exponent)
    (hdegree : degree ≤ m)
    (hx : 0 ≤ x) (hp : p ∈ Set.Icc 0 x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x)
    (hBstruct : Bstruct ∈ Set.Icc 0 x) (hpnum : pnum ∈ Set.Icc 0 x)
    (hPchart : Pchart ∈ Set.Icc 0 x) (hQstride : Qstride ∈ Set.Icc 0 x)
    (hvariables : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ x)
    (hX : (Fintype.card X : ℝ) ≤ x) (hG : (Fintype.card G : ℝ) ≤ x)
    (hξ : ξ ≤ 1) (hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i)
    (hcap : rawCap ≤ Real.exp work)
    (hprojection : modelPrecision + 2 * work + max (max native 3)
      (2 * modelPrecision + 4 * work + 20) + 32 ≤ E)
    (hdetection : sampler.NativeDetection degree slice test native
      (Real.exp (-(2 * modelPrecision + 4 * work + 8))))
    (hexcess :
      (FiniteProbabilityWeights.uniformFinset (integerBox N) sampler.integerBox_nonempty).excessMass
        (sampler.law.siteLaw (sampler.physicalBox hξ hmargin)) rawCap ≤
          6 * positiveProjectionAccuracy E) : sampler.FrontSourceProfile degree p e := by
  have hExponentTwo : 2 ≤ exponent :=
    (preparedFiniteForwardFrontProfileExponent_two_le e).trans hExponent
  have hresource := (Classical.choose_spec
      (exists_preparedFiniteForwardActualNativeBudget m (preparedFiniteForwardDetectorPolynomial cutoff))).2
    ⟨degree, Nat.lt_succ_of_le hdegree⟩ exponent Cdirect constants 0 false
    (G := G) hExponentTwo hx hg hs hBstruct hpnum hPchart hQstride
    hvariables hX hG Plate
  have hnative : 0 ≤ native := hresource.2.2.1.1
  exact sampler.preparedFiniteForwardFrontSourceProfile cutoff exponent Cslice constants
    hExponent hCslice hSliceExponent hx hp hg hs hvariables hξ hmargin
    hnative hcap hprojection hdetection hexcess

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

local instance zeroLayerForwardFrontSiteNonempty : Nonempty A.Site := A.site_nonempty
attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection

variable (q cutoff exponent Cslice Cdirect : ℕ) (constants : ℕ → ℕ)
    {x p gainLog stageLog Bstruct pnum Pchart Qstride Plate : ℝ} {degree e : ℕ}
local notation "work" => preparedFiniteForwardWork exponent constants 0 x
local notation "modelPrecision" => preparedFiniteForwardModelPrecision exponent constants 0 x gainLog stageLog
local notation "sourcePrecision" => preparedFiniteForwardSourcePrecision exponent constants 0 x gainLog stageLog
local notation "test" => Polynomial.eval₂ (Nat.castRingHom ℝ)
    (allocatedModelTestLog sourcePrecision work) (preparedFiniteForwardDetectorPolynomial cutoff)
local notation "master" => preparedFiniteForwardActualFrontLocalMaster q G
    (Fintype.card (LayerSamplerVariables G I n B)) (Fintype.card X)
    (preparedFiniteForwardDetectorPolynomial cutoff) exponent Cdirect constants degree
    x gainLog stageLog Bstruct pnum Pchart Qstride
local notation "native" => PreparedModularCanonicalDetectorResources.nativeBudget
    (preparedModularGeneralDetectorResources
      (preparedModularGeneralDetectorConstants q degree) (degree + 1) master Plate)

noncomputable def zeroLayerForwardFrontSourceProfile
    (hExponent : preparedFiniteForwardFrontProfileExponent e ≤ exponent)
    (hCslice : 1 ≤ Cslice) (hSliceExponent : Cslice + 1 ≤ exponent)
    (hdegree : degree ≤ q)
    (hx : 0 ≤ x) (hp : p ∈ Set.Icc 0 x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x)
    (hBstruct : Bstruct ∈ Set.Icc 0 x) (hpnum : pnum ∈ Set.Icc 0 x)
    (hPchart : Pchart ∈ Set.Icc 0 x) (hQstride : Qstride ∈ Set.Icc 0 x)
    (hvariables : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ x)
    (hX : (Fintype.card X : ℝ) ≤ x) (hG : (Fintype.card G : ℝ) ≤ x)
    (hξ : ξ ≤ 1)
    {surplus L : ℝ} (hsurplus : 0 < surplus) (hsurplus1 : surplus ≤ 1)
    (htrim : τ = unconditionedSpatialTrimFraction (Fintype.card X) surplus)
    (hN : ∀ i, unconditionedSpatialWidthCutoff
      (allocatedExternalCandidateRootBudget B U b S) τ L ≤ (N i : ℝ))
    (hdetection : A.NativeDetection degree ((x + Cslice) ^ Cslice) test native
      (Real.exp (-(2 * modelPrecision + 4 * work + 8)))) :
    A.FrontSourceProfile degree p e := by
  have hExponentTwo : 2 ≤ exponent :=
    (preparedFiniteForwardFrontProfileExponent_two_le e).trans hExponent
  have hresource := (Classical.choose_spec
      (exists_preparedFiniteForwardActualNativeBudget q (preparedFiniteForwardDetectorPolynomial cutoff))).2
    ⟨degree, Nat.lt_succ_of_le hdegree⟩ exponent Cdirect constants 0 false
    (G := G) hExponentTwo hx hg hs hBstruct hpnum hPchart hQstride
    hvariables hX hG Plate
  have hnative : 0 ≤ native := hresource.2.2.1.1
  have hfront := preparedFiniteForwardFrontProfile_bounds e exponent constants hExponent hx hp hg hs
  have hwork : 1 ≤ work := by linarith only [hfront.1, hp.1]
  have hcap : (2 : ℝ) ≤ Real.exp work :=
    (by linarith : (2 : ℝ) ≤ work + 1).trans (Real.add_one_le_exp work)
  let precision := modelPrecision + 2 * work + max (max native 3)
    (2 * modelPrecision + 4 * work + 20) + 32
  have hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i := fun i => (A.trimMargin_proper i).le
  have hexcess :
      (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
        (A.law.siteLaw (A.physicalBox hξ hmargin)) 2 ≤
          6 * positiveProjectionAccuracy precision := by
    rw [A.fixedCenter_excess_zero_layers_of_spatial_cutoff hξ hmargin
      hsurplus hsurplus1 htrim hN]
    exact mul_nonneg (by norm_num) (Real.exp_nonneg _)
  exact A.preparedFiniteForwardFrontSourceProfile cutoff exponent Cslice constants
    hExponent hCslice hSliceExponent hx hp hg hs hvariables hξ hmargin
    hnative hcap (le_refl precision) hdetection hexcess

noncomputable def zeroLayerDegreeSourceProfile
    {degree e : ℕ} {p : ℝ}
    (front : A.FrontSourceProfile degree p e)
    (inner : A.InnerSourceProfile degree)
    (hinput : p ≤ inner.x) (htrim : τ ≤ 1) :
    A.DegreeSourceProfile degree p e where
  front := front
  inner := inner
  input_inner := hinput
  trim_le_one := htrim
  width_le_one := fun j => Fin.elim0 j
  polynomial_degree := fun j => Fin.elim0 j
  chartConstant := fun j => Fin.elim0 j
  chartConstant_nonneg := fun j => Fin.elim0 j
  chart_bound := fun j => Fin.elim0 j
  chart_small := fun j => Fin.elim0 j

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

end OAI
