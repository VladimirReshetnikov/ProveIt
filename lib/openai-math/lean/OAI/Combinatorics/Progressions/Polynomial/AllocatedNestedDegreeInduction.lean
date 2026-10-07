import OAI.Combinatorics.Progressions.Estimates.AllocatedCandidateGeneratedFastTerminal
import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateLocalFixedCenterFront
import OAI.Combinatorics.Progressions.Polynomial.CandidateNestedDegreeNetSchedule

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

local instance degreeSourceProfileSiteNonempty : Nonempty A.Site := A.site_nonempty

structure FrontSourceProfile (degree : ℕ) (p : ℝ) (e : ℕ) where
  u : ℝ
  pModel : ℝ
  sliceBudget : ℝ
  testBudget : ℝ
  nativeBudget : ℝ
  projectionPrecision : ℝ
  marginalCap : ℝ
  narrow : ξ ≤ 1
  u_nonneg : 0 ≤ u
  model_nonneg : 0 ≤ pModel
  input_model : 2 * p + 3 ≤ pModel
  native_nonneg : 0 ≤ nativeBudget
  slice_nonneg : 0 ≤ sliceBudget
  test_nontrivial : 2 ≤ testBudget
  slice_log : sliceBudget * Fintype.card (LayerSamplerVariables G I n B) ≤ pModel
  marginal_one : 1 ≤ marginalCap
  marginal_bound : marginalCap ≤ Real.exp pModel
  projection_precision : u + 2 * pModel + max (max nativeBudget 3)
    (2 * u + 4 * pModel + 20) + 32 ≤ projectionPrecision
  detection : A.NativeDetection degree sliceBudget testBudget nativeBudget
    (Real.exp (-(2 * u + 4 * pModel + 8)))
  physical_excess :
    (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
      (A.law.siteLaw (A.physicalBox narrow (fun x => (A.trimMargin_proper x).le)))
      marginalCap ≤ 6 * positiveProjectionAccuracy projectionPrecision
  input_slice : p ≤ sliceBudget
  projection_test :
    AllocatedExternalCandidateProblem.positiveKernelPreparationParameter (2 * p) ≤ testBudget
  markov_precision :
    AllocatedExternalCandidateProblem.positiveKernelMarkovPrecisionParameter (2 * p) e ≤ u

noncomputable abbrev degreeSourceCountConstants (r : ℕ) : ℕ :=
  fullChartStageCountConstant (r + 1) 254

structure InnerSourceProfile (degree : ℕ) where
  x : ℝ
  scheduleExponent : ℕ
  Cprimitive : ℕ
  Csource : ℕ
  gainLog : ℝ
  stageLog : ℝ
  sourceNative : ℕ → ℝ
  pTest : ℕ → ℝ
  detectionLoss : ℕ → ℝ
  rankThreshold : ℝ
  x_nonneg : 0 ≤ x
  gain_range : gainLog ∈ Set.Icc 0 x
  stage_range : stageLog ∈ Set.Icc 0 x
  primitive_pos : 1 ≤ Cprimitive
  base_exponent : allocatedCandidateStageBaseExponent degree m Cprimitive ≤ scheduleExponent
  slice_exponent : allocatedCandidateStageSliceExponent degree m Cprimitive + 1 ≤ scheduleExponent
  phase_exponent : ∀ r < degree,
    allocatedCandidateCompositePhaseConstant degree m 1
      (allocatedCandidatePromotedMajorConstant Csource) r ≤ scheduleExponent
  source_nonneg : ∀ r < degree, 0 ≤ sourceNative r
  source_bound : ∀ r < degree, sourceNative r ≤
    (preparedFiniteForwardSourcePrecision scheduleExponent degreeSourceCountConstants
        r x gainLog stageLog +
      preparedFiniteForwardWork scheduleExponent degreeSourceCountConstants r x + Csource) ^ Csource
  test_floor : ∀ r < degree, OrdinaryPolynomialPhase.budget r ≤ pTest r
  loss_nonneg : ∀ r < degree, 0 ≤ detectionLoss r
  loss_bound : ∀ r < degree, detectionLoss r ≤ Real.exp (-gainLog) / 2
  detection : ∀ r < degree, A.NativeDetection r
    (allocatedCandidateStageSlice degree m Cprimitive
      (preparedFiniteForwardParameter scheduleExponent degreeSourceCountConstants r x))
    (pTest r) (sourceNative r) (detectionLoss r)
  tags_input : (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ x
  layers_input : (m : ℝ) ≤ x
  variables_input : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ x
  size_floor : ∀ i, Real.exp
    (preparedFiniteForwardCumulative scheduleExponent degreeSourceCountConstants degree x) ≤ (N i : ℝ)
  rank_floor : Real.exp
    (preparedFiniteForwardCumulative scheduleExponent degreeSourceCountConstants degree x) ≤ rankThreshold
  sampling_rank : ∀ j, HasLayerSamplingRank (j.val + 1)
    (fun i => (N i : ℝ)) rankThreshold (U j) (poly j)

structure DegreeSourceProfile (degree : ℕ) (p : ℝ) (e : ℕ) where
  front : A.FrontSourceProfile degree p e
  inner : A.InnerSourceProfile degree
  input_inner : p ≤ inner.x
  trim_le_one : τ ≤ 1
  width_le_one : ∀ j, σ j ≤ 1
  polynomial_degree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j)
  chartConstant : Fin m → ℝ
  chartConstant_nonneg : ∀ j, 0 ≤ chartConstant j
  chart_bound : ∀ j v,
    ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ chartConstant j * ‖v‖
  chart_small : ∀ j, chartConstant j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

namespace AllocatedExternalCandidateProblem

theorem positiveKernelPreparationBinLog_mono_netExponent {p : ℝ}
    (hp : 0 ≤ p) {e f : ℕ} (hef : e ≤ f) :
    positiveKernelPreparationBinLog p e ≤ positiveKernelPreparationBinLog p f := by
  have hq := positiveKernelPreparationParameter_nonneg hp
  have hef' : (e : ℝ) ≤ f := Nat.cast_le.mpr hef
  have hf : (0 : ℝ) ≤ f := Nat.cast_nonneg f
  unfold positiveKernelPreparationBinLog
  calc
    _ ≤ (2 * p + positiveKernelPreparationParameter p + 5 + f) ^ e :=
      pow_le_pow_left₀ (by positivity) (by linarith only [hef']) e
    _ ≤ _ := pow_le_pow_right₀ (by linarith only [hp, hq, hf]) hef

theorem positiveKernelMarkovPrecisionParameter_mono_netExponent {p : ℝ}
    (hp : 0 ≤ p) {e f : ℕ} (hef : e ≤ f) :
    positiveKernelMarkovPrecisionParameter p e ≤ positiveKernelMarkovPrecisionParameter p f := by
  have hbin := positiveKernelPreparationBinLog_mono_netExponent hp hef
  unfold positiveKernelMarkovPrecisionParameter
  linarith only [hbin]

end AllocatedExternalCandidateProblem

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
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalCandidateSampler

def FrontSourceProfile.mono_netExponent {degree e f : ℕ} {p : ℝ}
    (source : A.FrontSourceProfile degree p f) (hp : 0 ≤ p) (hef : e ≤ f) :
    A.FrontSourceProfile degree p e :=
  { source with
    markov_precision :=
      (AllocatedExternalCandidateProblem.positiveKernelMarkovPrecisionParameter_mono_netExponent
        (by positivity : 0 ≤ 2 * p) hef).trans source.markov_precision }

def DegreeSourceProfile.mono_netExponent {degree e f : ℕ} {p : ℝ}
    (source : A.DegreeSourceProfile degree p f) (hp : 0 ≤ p) (hef : e ≤ f) :
    A.DegreeSourceProfile degree p e :=
  { source with front := source.front.mono_netExponent hp hef }

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

namespace AllocatedExternalCandidateProblem

theorem positiveKernelPreparationBinLog_mono_netExponent_calc {p : ℝ}
    (hp : 0 ≤ p) {e f : ℕ} (hef : e ≤ f) :
    positiveKernelPreparationBinLog p e ≤ positiveKernelPreparationBinLog p f := by
  have hq := positiveKernelPreparationParameter_nonneg hp
  have hef' : (e : ℝ) ≤ f := Nat.cast_le.mpr hef
  have hf : (0 : ℝ) ≤ f := Nat.cast_nonneg f
  unfold positiveKernelPreparationBinLog
  calc
    _ ≤ (2 * p + positiveKernelPreparationParameter p + 5 + f) ^ e :=
      pow_le_pow_left₀ (by positivity) (by linarith only [hef']) e
    _ ≤ _ := pow_le_pow_right₀ (by linarith only [hp, hq, hf]) hef

theorem positiveKernelMarkovPrecisionParameter_mono_netExponent_calc {p : ℝ}
    (hp : 0 ≤ p) {e f : ℕ} (hef : e ≤ f) :
    positiveKernelMarkovPrecisionParameter p e ≤ positiveKernelMarkovPrecisionParameter p f := by
  have hbin := positiveKernelPreparationBinLog_mono_netExponent_calc hp hef
  unfold positiveKernelMarkovPrecisionParameter
  linarith only [hbin]

end AllocatedExternalCandidateProblem

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
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalCandidateSampler

def FrontSourceProfile.mono_netExponent_calc {degree e f : ℕ} {p : ℝ}
    (source : A.FrontSourceProfile degree p f) (hp : 0 ≤ p) (hef : e ≤ f) :
    A.FrontSourceProfile degree p e :=
  { source with
    markov_precision :=
      (AllocatedExternalCandidateProblem.positiveKernelMarkovPrecisionParameter_mono_netExponent_calc
        (by positivity : 0 ≤ 2 * p) hef).trans source.markov_precision }

def DegreeSourceProfile.mono_netExponent_calc {degree e f : ℕ} {p : ℝ}
    (source : A.DegreeSourceProfile degree p f) (hp : 0 ≤ p) (hef : e ≤ f) :
    A.DegreeSourceProfile degree p e :=
  { source with front := source.front.mono_netExponent_calc hp hef }

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

noncomputable def preparedCommonRadiusDegreeSourceProfile
    {degree e : ℕ} {p Bstruct Pchart : ℝ}
    (front : sampler.FrontSourceProfile degree p e)
    (inner : sampler.InnerSourceProfile degree) (hInput : p ≤ inner.x)
    (hτ : τ ≤ 1) (hσone : ∀ j, σ j ≤ 1)
    (hdegree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v,
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hCbound : ∀ j, C j ≤ Real.exp Pchart)
    (hallow : Pchart + 1 ≤ Bstruct) (hB : 0 ≤ Bstruct)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Bstruct)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ Bstruct)
    (hn : ∀ j, (n j : ℝ) ≤ Bstruct)
    (hRadius : ∀ j, R j = allocatedCommonProductRadius m Bstruct Bstruct) :
    sampler.DegreeSourceProfile degree p e := by
  let rows : Fin m → Finset (Finset (Fin 0)) := fun _ => {∅}
  letI : ∀ j, Nonempty (rows j) := fun _ => ⟨⟨∅, by simp [rows]⟩⟩
  have hsmall := (preparedUniformEarlyRadius_eighth (G := G) B rows hB hB
    (by simp) hvars hI hn C hC hCbound hallow).1
  refine {
    front := front
    inner := inner
    input_inner := hInput
    trim_le_one := hτ
    width_le_one := hσone
    polynomial_degree := hdegree
    chartConstant := C
    chartConstant_nonneg := hC
    chart_bound := hchart
    chart_small := ?_
  }
  intro j
  simpa only [hRadius j, mul_assoc] using hsmall j

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal
attribute [local irreducible] AllocatedExternalCandidateSampler.DegreeGlobalizationAt

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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

theorem degreeGlobalizationAt_nested_suffix
    (weight : (X → ℤ) → ℂ) (total initial exponent innerDepth : ℕ)
    (constants : ℕ → ℕ) {x : ℝ} (hexponent : 2 ≤ exponent) (hx : 0 ≤ x)
    (step : ∀ j < total, ∀ q : ℝ,
      candidateNestedForwardSeed exponent constants innerDepth (2 * (j + 1)) x ≤ q →
      A.DegreeGlobalizationAt (E := E) weight (total - (j + 1))
        (RationalFilteredNilmanifold.refilteredQuotientNetExponent.{0, 0, 0}
          (total - (j + 1)) 1 (candidateNestedDegreeNetExponent total initial j) + 2)
        (candidateNestedForwardSeed exponent constants innerDepth (2 * (j + 1)) x) q →
      A.DegreeGlobalizationAt (E := E) weight (total - j)
        (candidateNestedDegreeNetExponent total initial j)
        (candidateNestedForwardSeed exponent constants innerDepth (2 * j) x) (3 * q + 2)) :
    ∀ j ≤ total,
      A.DegreeGlobalizationAt (E := E) weight (total - j)
        (candidateNestedDegreeNetExponent total initial j)
        (candidateNestedForwardSeed exponent constants innerDepth (2 * j) x)
        (candidateDegreeReturnBudget (total - j)
          (candidateNestedForwardSeed exponent constants innerDepth (2 * total) x)) := by
  let terminal := candidateNestedForwardSeed exponent constants innerDepth (2 * total) x
  have hterminal : 0 ≤ terminal :=
    candidateNestedForwardSeed_nonneg exponent constants innerDepth (2 * total) hx
  have all : ∀ d j, d + j = total →
      A.DegreeGlobalizationAt (E := E) weight d
        (candidateNestedDegreeNetExponent total initial j)
        (candidateNestedForwardSeed exponent constants innerDepth (2 * j) x)
        (candidateDegreeReturnBudget d terminal) := by
    intro d
    induction d with
    | zero =>
        intro j hj
        have hjeq : j = total := by omega
        subst j
        simpa only [candidateDegreeReturnBudget_zero] using
          A.degreeGlobalizationAt_zero (E := E) weight
            (candidateNestedDegreeNetExponent total initial total) terminal
    | succ d ih =>
        intro j hj
        have hjlt : j < total := by omega
        have hd : total - (j + 1) = d := by omega
        have hd' : total - j = d + 1 := by omega
        have lower := ih (j + 1) (by omega)
        have hnext : candidateNestedForwardSeed exponent constants innerDepth (2 * (j + 1)) x ≤
            candidateDegreeReturnBudget d terminal := by
          apply le_trans
            (candidateNestedForwardSeed_monotone exponent constants innerDepth hexponent hx
              (by omega : 2 * (j + 1) ≤ 2 * total))
          exact le_candidateDegreeReturnBudget d hterminal
        have current := step j hjlt (candidateDegreeReturnBudget d terminal) hnext
          (by simpa only [candidateNestedDegreeNetExponent_succ, hd] using lower)
        simpa only [hd', candidateDegreeReturnBudget_succ] using current
  intro j hj
  exact all (total - j) j (by omega)

theorem degreeGlobalizationAt_nested
    (weight : (X → ℤ) → ℂ) (total initial exponent innerDepth : ℕ)
    (constants : ℕ → ℕ) {x : ℝ} (hexponent : 2 ≤ exponent) (hx : 0 ≤ x)
    (step : ∀ j < total, ∀ q : ℝ,
      candidateNestedForwardSeed exponent constants innerDepth (2 * (j + 1)) x ≤ q →
      A.DegreeGlobalizationAt (E := E) weight (total - (j + 1))
        (RationalFilteredNilmanifold.refilteredQuotientNetExponent.{0, 0, 0}
          (total - (j + 1)) 1 (candidateNestedDegreeNetExponent total initial j) + 2)
        (candidateNestedForwardSeed exponent constants innerDepth (2 * (j + 1)) x) q →
      A.DegreeGlobalizationAt (E := E) weight (total - j)
        (candidateNestedDegreeNetExponent total initial j)
        (candidateNestedForwardSeed exponent constants innerDepth (2 * j) x) (3 * q + 2)) :
    A.DegreeGlobalizationAt (E := E) weight total initial x
      (candidateDegreeReturnBudget total
        (candidateNestedForwardSeed exponent constants innerDepth (2 * total) x)) := by
  simpa only [Nat.sub_zero, Nat.mul_zero, candidateNestedDegreeNetExponent_zero,
    candidateNestedForwardSeed_zero] using
    A.degreeGlobalizationAt_nested_suffix (E := E) weight total initial exponent innerDepth
      constants hexponent hx step 0 (Nat.zero_le total)

theorem degreeGlobalizationAt_nested_of_recursive_inputs
    (weight : (X → ℤ) → ℂ) (total initial exponent innerDepth : ℕ)
    (constants : ℕ → ℕ) {x : ℝ} (hexponent : 2 ≤ exponent) (hx : 0 ≤ x)
    (recursiveInput : ℕ → ℝ)
    (hrecursive : ∀ j < total, recursiveInput j ∈ Set.Icc 0
      (candidateNestedForwardSeed exponent constants innerDepth (2 * (j + 1)) x))
    (step : ∀ j < total, ∀ q : ℝ, recursiveInput j ≤ q →
      A.DegreeGlobalizationAt (E := E) weight (total - (j + 1))
        (RationalFilteredNilmanifold.refilteredQuotientNetExponent.{0, 0, 0}
          (total - (j + 1)) 1 (candidateNestedDegreeNetExponent total initial j) + 2)
        (recursiveInput j) q →
      A.DegreeGlobalizationAt (E := E) weight (total - j)
        (candidateNestedDegreeNetExponent total initial j)
        (candidateNestedForwardSeed exponent constants innerDepth (2 * j) x) (3 * q + 2)) :
    A.DegreeGlobalizationAt (E := E) weight total initial x
      (candidateDegreeReturnBudget total
        (candidateNestedForwardSeed exponent constants innerDepth (2 * total) x)) := by
  apply A.degreeGlobalizationAt_nested (E := E) weight total initial exponent innerDepth
    constants hexponent hx
  intro j hj q hq lower
  have hr := hrecursive j hj
  exact step j hj q (hr.2.trans hq) (DegreeGlobalizationAt.mono_input A lower hr.1 hr.2)

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

end OAI
