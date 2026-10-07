import OAI.Combinatorics.Progressions.Estimates.PreparedFiniteNestedSourceArrays
import OAI.Combinatorics.Progressions.Linear.PositiveKernelNativeDescentBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct

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

namespace AllocatedExternalCandidateSampler.FrontSourceProfile

variable {degree e : ℕ} {p : ℝ} (source : A.FrontSourceProfile degree p e)

noncomputable def familyCap : ℝ :=
  p + AllocatedExternalCandidateProblem.positiveKernelPreparationParameter (2 * p) +
    source.u + source.pModel + source.nativeBudget + (m : ℝ) +
    Fintype.card (LayerSamplerVariables G I n B) + 3

noncomputable def familyParameter : ℝ := candidateFrontFamilyParameter source.familyCap

theorem familyCap_bounds (hp : 0 ≤ p) :
    0 ≤ source.familyCap ∧ p ≤ source.familyCap ∧
    AllocatedExternalCandidateProblem.positiveKernelPreparationParameter (2 * p) ≤
      source.familyCap ∧
    source.u ≤ source.familyCap ∧ source.pModel ≤ source.familyCap ∧
    source.nativeBudget ≤ source.familyCap ∧ (m : ℝ) ≤ source.familyCap ∧
    (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ source.familyCap ∧
    3 ≤ source.familyCap := by
  have hq := AllocatedExternalCandidateProblem.positiveKernelPreparationParameter_nonneg
    (show 0 ≤ 2 * p by positivity)
  have hu := source.u_nonneg
  have hmodel := source.model_nonneg
  have hnative := source.native_nonneg
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hvariables : (0 : ℝ) ≤ Fintype.card (LayerSamplerVariables G I n B) :=
    Nat.cast_nonneg _
  dsimp only [familyCap]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    linarith only [hp, hq, hu, hmodel, hnative, hm, hvariables]

structure FamilyBudget : Prop where
  hpFamily : 0 ≤ source.familyParameter
  cost : p ≤ source.familyParameter
  projection : AllocatedExternalCandidateProblem.positiveKernelPreparationParameter (2 * p) ≤
    source.familyParameter
  native : max source.nativeBudget 3 ≤ source.familyParameter
  period : 2 * max source.nativeBudget 3 ≤ source.familyParameter
  variation : Real.exp (max source.nativeBudget 3) *
    (1 + (m : ℝ) * (((m + 1 : ℕ) : ℝ) *
      ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m)) ≤
        Real.exp source.familyParameter
  keepCard : ∀ keep : LayerSamplerVariables G I n B → Prop,
    (Fintype.card {i // keep i} : ℝ) ≤ source.familyParameter

theorem familyBudget (hp : 0 ≤ p) : source.FamilyBudget := by
  obtain ⟨hcap, hpCap, hqCap, _, _, hnCap, hmCap, hvCap, _⟩ := source.familyCap_bounds hp
  obtain ⟨hf0, hcf, hperiod, hvariation⟩ := candidateFrontFamilyBounds source.familyCap
    source.nativeBudget m (Fintype.card (LayerSamplerVariables G I n B))
    hcap hnCap hmCap hvCap
  refine ⟨hf0, hpCap.trans hcf, hqCap.trans hcf, ?_, hperiod, hvariation, ?_⟩
  · exact (by linarith [le_max_right source.nativeBudget (3 : ℝ)] :
      max source.nativeBudget 3 ≤ 2 * max source.nativeBudget 3).trans hperiod
  · intro keep
    have hcard : Fintype.card {i // keep i} ≤
        Fintype.card (LayerSamplerVariables G I n B) := Fintype.card_subtype_le _
    exact (Nat.cast_le.mpr hcard).trans (hvCap.trans hcf)

end AllocatedExternalCandidateSampler.FrontSourceProfile
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct

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

namespace AllocatedExternalCandidateSampler.FrontSourceProfile

variable {degree e : ℕ} {p : ℝ} (source : A.FrontSourceProfile degree p e)

noncomputable def frontModelBudget : ℝ :=
  max (max source.nativeBudget 3) (2 * source.u + 4 * source.pModel + 20)

noncomputable def frontTermLog : ℝ :=
  2 * source.frontModelBudget + 2 * source.u + 4 * source.pModel + 34

noncomputable def frontCorrelationLoss : ℝ :=
  AllocatedExternalCandidateProblem.positiveKernelPreparationParameter (2 * p) +
    AllocatedExternalCandidateProblem.positiveKernelPreparationBinLog (2 * p) e +
    (source.frontModelBudget + 2) + 4

noncomputable def frontRawMassLoss : ℝ :=
  2 * p + AllocatedExternalCandidateProblem.positiveKernelPreparationParameter (2 * p) +
    p * (AllocatedExternalCandidateProblem.positiveKernelPreparationBinLog (2 * p) e +
      source.frontTermLog) + 2

structure LossBudget : Prop where
  projection_nonneg :
    0 ≤ AllocatedExternalCandidateProblem.positiveKernelPreparationParameter (2 * p)
  bin_nonneg : 0 ≤ AllocatedExternalCandidateProblem.positiveKernelPreparationBinLog (2 * p) e
  bin_le_u : AllocatedExternalCandidateProblem.positiveKernelPreparationBinLog (2 * p) e ≤ source.u
  model_nonneg : 0 ≤ source.frontModelBudget
  model_bound : source.frontModelBudget ≤ 6 * source.familyCap + 20
  term_bound : source.frontTermLog ≤ 18 * source.familyCap + 74
  localPrecision : AllocatedExternalCandidateProblem.positiveKernelPreparationParameter (2 * p) ≤
    source.familyParameter
  correlation_nonneg : 0 ≤ source.frontCorrelationLoss
  correlation : source.frontCorrelationLoss ≤ source.familyParameter
  rawMass_nonneg : 0 ≤ source.frontRawMassLoss
  rawMass : source.frontRawMassLoss ≤ source.familyParameter

theorem lossBudget (hp : 0 ≤ p) : source.LossBudget := by
  have hp2 : 0 ≤ 2 * p := by positivity
  have hq := AllocatedExternalCandidateProblem.positiveKernelPreparationParameter_nonneg hp2
  have hbin := AllocatedExternalCandidateProblem.positiveKernelPreparationBinLog_nonneg hp2 e
  have hmarkov := source.markov_precision
  unfold AllocatedExternalCandidateProblem.positiveKernelMarkovPrecisionParameter at hmarkov
  have hbinU : AllocatedExternalCandidateProblem.positiveKernelPreparationBinLog (2 * p) e ≤
      source.u := by linarith only [hmarkov, hp, hq, hbin]
  obtain ⟨_, hpCap, hqCap, huCap, hmodelCap, hnativeCap, _, _, hcap⟩ :=
    source.familyCap_bounds hp
  obtain ⟨hQ0, hQ, hr0, hr, hM0, hM⟩ := candidateFrontSourceLossBounds
    source.familyCap p
    (AllocatedExternalCandidateProblem.positiveKernelPreparationParameter (2 * p))
    source.u source.pModel source.nativeBudget
    (AllocatedExternalCandidateProblem.positiveKernelPreparationBinLog (2 * p) e)
    hcap hp hq source.u_nonneg source.model_nonneg source.native_nonneg hbin
    hpCap hqCap huCap hmodelCap hnativeCap hbinU
  refine ⟨hq, hbin, hbinU, hQ0, hQ, ?_, (source.familyBudget hp).projection,
    ?_, ?_, hM0, hM⟩
  · dsimp only [frontTermLog, frontModelBudget]
    linarith only [hQ, huCap, hmodelCap]
  · dsimp only [frontCorrelationLoss, frontModelBudget]
    linarith only [hr0]
  · change _ ≤ candidateFrontFamilyParameter source.familyCap
    dsimp only [frontCorrelationLoss, frontModelBudget, candidateFrontFamilyParameter]
    linarith only [hr]

theorem primitiveFrontLoss_bounds (hp : 0 ≤ p) :
    let q := AllocatedExternalCandidateProblem.positiveKernelPreparationParameter (2 * p)
    let binLog := AllocatedExternalCandidateProblem.positiveKernelPreparationBinLog (2 * p) e
    let commonBudget := max source.nativeBudget 3
    let Qmodel := max commonBudget (2 * source.u + 4 * source.pModel + 20)
    let coefficientLog := Qmodel + 2
    let termLog := 2 * Qmodel + 2 * source.u + 4 * source.pModel + 34
    q ≤ source.familyParameter ∧
      q + binLog + coefficientLog + 4 ≤ source.familyParameter ∧
      2 * p + q + p * (binLog + termLog) + 2 ≤ source.familyParameter := by
  have budget := source.lossBudget hp
  exact ⟨budget.localPrecision, budget.correlation, budget.rawMass⟩

theorem exp_neg_familyParameter_le_rawMassLoss (hp : 0 ≤ p) :
    Real.exp (-source.familyParameter) ≤ Real.exp (-source.frontRawMassLoss) :=
  Real.exp_le_exp.mpr (neg_le_neg (source.lossBudget hp).rawMass)

theorem exp_neg_familyParameter_le_correlationLoss (hp : 0 ≤ p) :
    Real.exp (-source.familyParameter) ≤ Real.exp (-source.frontCorrelationLoss) :=
  Real.exp_le_exp.mpr (neg_le_neg (source.lossBudget hp).correlation)

end AllocatedExternalCandidateSampler.FrontSourceProfile
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open AllocatedExternalCandidateProblem

theorem exists_preparedFiniteForwardFrontFamilyScalar_budget (Cnative : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (m cardVars : ℕ) {t p u pModel native : ℝ},
      0 ≤ t → p ∈ Set.Icc 0 t → u ∈ Set.Icc 0 t → pModel ∈ Set.Icc 0 t →
      (m : ℝ) ≤ t → (cardVars : ℝ) ≤ t →
      native ∈ Set.Icc 0 ((t + Cnative) ^ Cnative) →
      candidateFrontFamilyParameter
        (p + positiveKernelPreparationParameter (2 * p) + u + pModel + native + m + cardVars + 3) ∈
          Set.Icc 0 ((t + C) ^ C) := by
  let X : Polynomial ℕ := Polynomial.X
  let Q : Polynomial ℕ :=
    (5 * X + (2 * X + 5) ^ positiveKernelPreparationExponent +
      (X + Polynomial.C Cnative) ^ Cnative + 6) ^ 4
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro m cardVars t p u pModel native ht hp hu hmodel hm hvars hn
  have hp2 : 0 ≤ 2 * p := by linarith only [hp.1]
  have hq0 := positiveKernelPreparationParameter_nonneg hp2
  have hq : positiveKernelPreparationParameter (2 * p) ≤
      (2 * t + 5) ^ positiveKernelPreparationExponent := by
    unfold positiveKernelPreparationParameter
    exact pow_le_pow_left₀ (by linarith only [hp.1])
      (by linarith only [hp.2]) _
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hv0 : (0 : ℝ) ≤ cardVars := Nat.cast_nonneg _
  have hbase0 : 0 ≤ p + positiveKernelPreparationParameter (2 * p) + u + pModel +
      native + m + cardVars + 3 + 3 := by
    linarith only [hp.1, hq0, hu.1, hmodel.1, hn.1, hm0, hv0]
  have hbase : p + positiveKernelPreparationParameter (2 * p) + u + pModel +
      native + m + cardVars + 3 + 3 ≤
      5 * t + (2 * t + 5) ^ positiveKernelPreparationExponent +
        (t + Cnative) ^ Cnative + 6 := by
    linarith only [hp.2, hq, hu.2, hmodel.2, hn.2, hm, hvars]
  have hbudget : (5 * t + (2 * t + 5) ^ positiveKernelPreparationExponent +
      (t + Cnative) ^ Cnative + 6) ^ 4 ≤ (t + C) ^ C := by
    simpa [Q, X, Polynomial.eval₂_pow] using hpoly t ht
  exact ⟨pow_nonneg hbase0 4, (pow_le_pow_left₀ hbase0 hbase 4).trans hbudget⟩

theorem exists_preparedFiniteForwardFrontFamily_budget (Cnative : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (A Cdirect : ℕ) (stageCountConstant : ℕ → ℕ)
      (m cardVars : ℕ) {x p gainLog stageLog native : ℝ},
      2 ≤ A → 0 ≤ x → p ∈ Set.Icc 0 x →
      gainLog ∈ Set.Icc 0 x → stageLog ∈ Set.Icc 0 x →
      (m : ℝ) ≤ x → (cardVars : ℝ) ≤ x →
      let u := preparedFiniteForwardModelPrecision A stageCountConstant 0 x gainLog stageLog
      let w := preparedFiniteForwardWork A stageCountConstant 0 x
      let t := preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant 0 false
        x gainLog stageLog + w
      native ∈ Set.Icc 0 ((t + Cnative) ^ Cnative) →
      candidateFrontFamilyParameter
        (p + positiveKernelPreparationParameter (2 * p) + u + w + native + m + cardVars + 3) ∈
          Set.Icc 0 ((t + C) ^ C) := by
  obtain ⟨C, hC, hbound⟩ := exists_preparedFiniteForwardFrontFamilyScalar_budget Cnative
  refine ⟨C, hC, ?_⟩
  intro A Cdirect stageCountConstant m cardVars x p gainLog stageLog native
    hA hx hp hg hs hm hvars u w t hn
  have hprecision := preparedFiniteForward_model_precision_bounds A stageCountConstant 0 hx hg hs
  have hu : 0 ≤ u := hprecision.1
  have hw : 0 ≤ w := preparedFiniteForwardWork_nonneg A stageCountConstant 0 hx
  have hxw : x ≤ w := by
    have hscalar := preparedFiniteForward_model_scalar_bounds A stageCountConstant 0 0
      hA hx (by simpa only [Nat.cast_zero] using hx)
    simpa only [preparedFiniteForwardParameter_zero] using hscalar.2.1
  have htEq : t = u + 3 * w + 1 := by
    dsimp only [t]
    rw [preparedFiniteForwardPairedSourcePrecision_model]
    have heq : preparedFiniteForwardSourcePrecision A stageCountConstant 0 x gainLog stageLog =
        u + 2 * w + 1 := hprecision.2.2.1
    rw [heq]
    ring
  have ht : 0 ≤ t := by linarith only [htEq, hu, hw]
  have hwt : w ≤ t := by linarith only [htEq, hu, hw]
  have hxt : x ≤ t := hxw.trans hwt
  exact hbound m cardVars ht ⟨hp.1, hp.2.trans hxt⟩
    ⟨hu, by linarith only [htEq, hw]⟩ ⟨hw, hwt⟩ (hm.trans hxt) (hvars.trans hxt) hn

theorem exists_preparedFiniteForwardFrontFamily_polynomial_later_work_budget
    (Cnative : ℕ) (P : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (A : ℕ), C ≤ A → ∀ (Cdirect : ℕ)
      (stageCountConstant : ℕ → ℕ) (innerDepth m cardVars : ℕ)
      {x p gainLog stageLog native : ℝ},
      1 ≤ innerDepth → 0 ≤ x → p ∈ Set.Icc 0 x →
      gainLog ∈ Set.Icc 0 x → stageLog ∈ Set.Icc 0 x →
      (m : ℝ) ≤ x → (cardVars : ℝ) ≤ x →
      let u := preparedFiniteForwardModelPrecision A stageCountConstant 0 x gainLog stageLog
      let w := preparedFiniteForwardWork A stageCountConstant 0 x
      let t := preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant 0 false
        x gainLog stageLog + w
      native ∈ Set.Icc 0 ((t + Cnative) ^ Cnative) →
      P.eval₂ (Nat.castRingHom ℝ)
        (candidateFrontFamilyParameter
          (p + positiveKernelPreparationParameter (2 * p) + u + w + native + m + cardVars + 3)) ≤
            preparedFiniteForwardWork A stageCountConstant innerDepth x := by
  obtain ⟨Cf, _, hfamily⟩ := exists_preparedFiniteForwardFrontFamily_budget Cnative
  obtain ⟨C, hC, hpoly⟩ := exists_preparedFiniteForward_local_polynomial_le_later_work Cf P
  refine ⟨C, hC, ?_⟩
  intro A hCA Cdirect stageCountConstant innerDepth m cardVars x p gainLog stageLog native
    hdepth hx hp hg hs hm hvars u w t hn
  have hf := hfamily A Cdirect stageCountConstant m cardVars (hC.trans hCA) hx hp hg hs hm hvars hn
  exact hpoly A Cdirect stageCountConstant innerDepth hx hg hs hCA hdepth hf

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct

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

namespace AllocatedExternalCandidateSampler.FrontSourceProfile

variable {degree e : ℕ} {p : ℝ} (source : A.FrontSourceProfile degree p e)

noncomputable def geometryBudget : ℝ :=
  source.familyParameter +
    (source.familyParameter + 2) ^
      RationalFilteredNilmanifold.positiveKernelNativeDescentExponent degree + 2

noncomputable def factorBudget : ℝ :=
  2 * source.familyParameter +
    verticalDecompositionBudget (3 * source.familyParameter + 1) + 2

structure FactorGeometryBudget : Prop where
  geometry_two : 2 ≤ source.geometryBudget
  geometry_input : source.familyParameter ≤ source.geometryBudget
  geometry_descent :
    (source.familyParameter + 2) ^
      RationalFilteredNilmanifold.positiveKernelNativeDescentExponent degree ≤
        source.geometryBudget
  factor_input : source.familyParameter ≤ source.factorBudget
  factor_nonneg : 0 ≤ source.factorBudget
  vertical_nonneg : 0 ≤ 3 * source.familyParameter + 1
  native_vertical : max source.nativeBudget 3 ≤ 3 * source.familyParameter + 1
  local_vertical :
    AllocatedExternalCandidateProblem.positiveKernelPreparationParameter (2 * p) +
      source.frontCorrelationLoss + 1 ≤ 3 * source.familyParameter + 1
  vertical_factor : verticalDecompositionBudget (3 * source.familyParameter + 1) ≤
    source.factorBudget
  correlation_factor : source.frontCorrelationLoss +
    verticalDecompositionBudget (3 * source.familyParameter + 1) + 2 ≤ source.factorBudget

theorem factorGeometryBudget (hp : 0 ≤ p) : source.FactorGeometryBudget := by
  have family := source.familyBudget hp
  have loss := source.lossBudget hp
  have hP := family.hpFamily
  have hdesc : 0 ≤ (source.familyParameter + 2) ^
      RationalFilteredNilmanifold.positiveKernelNativeDescentExponent degree := by positivity
  have hvertical : 0 ≤ 3 * source.familyParameter + 1 := by positivity
  have hdecomp := verticalDecompositionBudget_nonneg hvertical
  have hn := family.native
  have hl := family.projection
  have hr := loss.correlation
  refine ⟨?_, ?_, ?_, ?_, ?_, hvertical, ?_, ?_, ?_, ?_⟩
  · dsimp only [geometryBudget]
    linarith only [hP, hdesc]
  · dsimp only [geometryBudget]
    linarith only [hdesc]
  · dsimp only [geometryBudget]
    linarith only [hP]
  · dsimp only [factorBudget]
    linarith only [hP, hdecomp]
  · dsimp only [factorBudget]
    linarith only [hP, hdecomp]
  · linarith only [hP, hn]
  · linarith only [hP, hl, hr]
  · dsimp only [factorBudget]
    linarith only [hP]
  · dsimp only [factorBudget]
    linarith only [hP, hr]

end AllocatedExternalCandidateSampler.FrontSourceProfile
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical

theorem preparedFiniteNestedSourceNative_front_mem
    (q : ℕ) (G : Type) [Fintype G] (count nX : ℕ) (Pdetect : Polynomial ℕ)
    (exponent Cdirect : ℕ) (constants : ℕ → ℕ)
    {outerDepth innerDepth cutoff : ℕ}
    (outer : Fin (outerDepth + 1)) (degree : Fin (cutoff + 1))
    {Bstruct pnum Qstride gainLog stageLog : ℝ} (Plate : ℝ)
    (hA : 2 ≤ exponent) (hB : 0 ≤ Bstruct) (hdegree : degree.val ≤ q)
    (hnum : pnum ∈ Set.Icc 0 Bstruct) (hstride : Qstride ∈ Set.Icc 0 Bstruct)
    (hg : gainLog ∈ Set.Icc 0 Bstruct) (hs : stageLog ∈ Set.Icc 0 Bstruct)
    (hcount : (count : ℝ) ≤ Bstruct) (hnX : (nX : ℝ) ≤ Bstruct)
    (hG : (Fintype.card G : ℝ) ≤ Bstruct) :
    let x := candidateNestedForwardSeed exponent constants innerDepth outer.val Bstruct
    let u := preparedFiniteForwardPairedSourcePrecision exponent Cdirect constants 0 false
      x gainLog stageLog
    let w := preparedFiniteForwardWork exponent constants 0 x
    let C := preparedFiniteForwardActualNativeBudgetExponent q Pdetect
    preparedFiniteNestedSourceNative q G count nX Pdetect exponent Cdirect constants
      Bstruct pnum Qstride gainLog stageLog Plate
      (outer, (0 : Fin (innerDepth + 1)), degree, false) ∈ Set.Icc 0 ((u + w + C) ^ C) := by
  intro x u w C
  have hx : 0 ≤ x := candidateNestedForwardSeed_nonneg exponent constants innerDepth outer.val hB
  have hBx : Bstruct ≤ x := le_candidateNestedForwardSeed exponent constants innerDepth outer.val hA hB
  have lift {r : ℝ} (hr : r ∈ Set.Icc 0 Bstruct) : r ∈ Set.Icc 0 x := ⟨hr.1, hr.2.trans hBx⟩
  have hresource := (Classical.choose_spec
      (exists_preparedFiniteForwardActualNativeBudget q Pdetect)).2
    ⟨degree.val, Nat.lt_succ_of_le hdegree⟩ exponent Cdirect constants 0 false
    (G := G) hA hx (lift hg) (lift hs) ⟨hB, hBx⟩ (lift hnum)
    ⟨hB, hBx⟩ (lift hstride) (hcount.trans hBx) (hnX.trans hBx) (hG.trans hBx) Plate
  exact hresource.2.2.1

theorem exists_preparedFiniteNestedFrontFamily_polynomial_next_seed
    (q : ℕ) (Pdetect P : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ (exponent Cdirect : ℕ) (constants : ℕ → ℕ)
      (outerDepth innerDepth cutoff targetLayers count nX : ℕ)
      (G : Type) [Fintype G]
      (outer : Fin (outerDepth + 1)) (degree : Fin (cutoff + 1))
      (Bstruct pnum Qstride gainLog stageLog Plate p : ℝ),
      C ≤ exponent → 1 ≤ innerDepth → 0 ≤ Bstruct → degree.val ≤ q →
      pnum ∈ Set.Icc 0 Bstruct → Qstride ∈ Set.Icc 0 Bstruct →
      gainLog ∈ Set.Icc 0 Bstruct → stageLog ∈ Set.Icc 0 Bstruct →
      (targetLayers : ℝ) ≤ Bstruct → (count : ℝ) ≤ Bstruct →
      (nX : ℝ) ≤ Bstruct → (Fintype.card G : ℝ) ≤ Bstruct →
      let x := candidateNestedForwardSeed exponent constants innerDepth outer.val Bstruct
      p ∈ Set.Icc 0 x →
      let native := preparedFiniteNestedSourceNative q G count nX Pdetect exponent Cdirect constants
        Bstruct pnum Qstride gainLog stageLog Plate
        (outer, (0 : Fin (innerDepth + 1)), degree, false)
      let u := preparedFiniteForwardModelPrecision exponent constants 0 x gainLog stageLog
      let w := preparedFiniteForwardWork exponent constants 0 x
      P.eval₂ (Nat.castRingHom ℝ)
        (candidateFrontFamilyParameter (p +
          AllocatedExternalCandidateProblem.positiveKernelPreparationParameter (2 * p) +
          u + w + native + targetLayers + count + 3)) ≤
        candidateNestedForwardSeed exponent constants innerDepth (outer.val + 1) Bstruct := by
  let Cnative := preparedFiniteForwardActualNativeBudgetExponent q Pdetect
  obtain ⟨C, hC, hbound⟩ :=
    exists_preparedFiniteForwardFrontFamily_polynomial_later_work_budget Cnative P
  refine ⟨C, hC, ?_⟩
  intro exponent Cdirect constants outerDepth innerDepth cutoff targetLayers count nX G _
    outer degree Bstruct pnum Qstride gainLog stageLog Plate p hCA hdepth hB hdegree
    hnum hstride hg hs htarget hcount hnX hG x hp native u w
  have hA : 2 ≤ exponent := hC.trans hCA
  have hx : 0 ≤ x := candidateNestedForwardSeed_nonneg exponent constants innerDepth outer.val hB
  have hBx : Bstruct ≤ x := le_candidateNestedForwardSeed exponent constants innerDepth outer.val hA hB
  have lift {r : ℝ} (hr : r ∈ Set.Icc 0 Bstruct) : r ∈ Set.Icc 0 x := ⟨hr.1, hr.2.trans hBx⟩
  have hnative := preparedFiniteNestedSourceNative_front_mem q G count nX Pdetect
    exponent Cdirect constants (innerDepth := innerDepth) outer degree Plate hA hB hdegree hnum hstride hg hs hcount hnX hG
  exact (hbound exponent hCA Cdirect constants innerDepth targetLayers count
    hdepth hx hp (lift hg) (lift hs) (htarget.trans hBx) (hcount.trans hBx) hnative).trans
    (candidateNestedForwardWork_le_next_seed exponent constants innerDepth outer.val innerDepth hB le_rfl)

end Erdos3.VectorPolynomial

end

end OAI
