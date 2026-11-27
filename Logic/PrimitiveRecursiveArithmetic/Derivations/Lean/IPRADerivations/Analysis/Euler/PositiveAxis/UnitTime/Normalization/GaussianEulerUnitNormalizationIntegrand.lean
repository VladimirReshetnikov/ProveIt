import IPRADerivations.Analysis.Euler.Integration.Decay.Quadrature.GaussianEulerDecayQuadrature
import IPRADerivations.Analysis.Polynomials.Coefficients.Norms.GaussianCoefficientNormOrder

/-!
# The original Euler integrand at one is literally the decay evaluator

The original exponent samples equal the constant negative time. Their
zeroth samples therefore compute exactly the same exponential radius.
The original cutoff and finite scalar exponential agree at every
precision, before any quadrature or limiting comparison.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitNormalizationIntegrand

open_ipra
open ComplexLogarithmRemainder (oneCode)
open GaussianEulerIntegrandName (coefficient exponentF exponentData radius decayF decayData decayPoint evaluatorF fixedData)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianRationalSyntheticDivision (qone qmul_congr qadd_congr qmul_zero_left qzero_add)
open GaussianRationalHorner (qzero)
open GaussianRationalFiniteSum (sum_index_congr)
open GaussianRationalPolynomialExponential (scalarBody)
open GaussianCompactRiemannName (quadrature sampleBody sampleData)
open GaussianRationalRiemannRefinement (weight)
open GaussianRationalHorner (qmul)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem ceil_congr (u v : PTm n) (h : Γ ⊢[PRAAx] u ≐ v) : Γ ⊢[PRAAx]
    GaussianGeneralFTAConstants.ceilL1 u ≐ GaussianGeneralFTAConstants.ceilL1 v := by
  ipra_congr (GaussianGeneralFTAConstants.ceilL1 (var 0) : PTm 1) with [h]

private theorem index_radius_congr (R S p : PTm n) (h : Γ ⊢[PRAAx] R ≐ S) : Γ ⊢[PRAAx]
    GaussianRadiusExponentialName.index R p ≐ GaussianRadiusExponentialName.index S p := by
  ipra_congr (GaussianRadiusExponentialName.index (var 0) (var 1) : PTm 2) with [h, .eqRefl p]

theorem coefficient_one : Γ ⊢[PRAAx] coefficient (oneCode : PTm n) one ≐ qzero :=
  GaussianCoefficientNormOrder.qsub_self qone

theorem exponent_one (p a b : PTm n) : Γ ⊢[PRAAx]
    ap2 exponentF p (exponentData oneCode one a b) ≐ decayPoint a b :=
  (GaussianEulerIntegrandName.exponent_at p oneCode one a b).eqTrans
    ((qadd_congr ((qmul_congr coefficient_one (.eqRefl _)).eqTrans (qmul_zero_left _)) (.eqRefl _)).eqTrans
      (qzero_add _ (GaussianRationalMetric.qnegative_canonical _)))

theorem radius_one (a b : PTm n) : Γ ⊢[PRAAx]
    radius oneCode one a b ≐ GaussianNameBounds.U constantF (decayPoint a b) := by
  have sample : Γ ⊢[PRAAx] ap2 exponentF zero (exponentData oneCode one a b) ≐ ap2 constantF zero (decayPoint a b) :=
    (exponent_one zero a b).eqTrans (constant_at zero (decayPoint a b)).eqSymm
  exact congrAdd (ceil_congr _ _ sample) (.eqRefl two)

theorem cutoff_one (p a b : PTm n) : Γ ⊢[PRAAx]
    GaussianEulerIntegrandName.cutoff p oneCode one a b ≐
      GaussianRadiusExponentialName.index (GaussianNameBounds.U constantF (decayPoint a b)) p :=
  index_radius_congr _ _ p (radius_one a b)

theorem original_sample_is_decay (p a b : PTm n) : Γ ⊢[PRAAx]
    GaussianEulerIntegrandName.sample p oneCode one a b ≐ ap2 decayF p (decayData a b) := by
  let R := GaussianNameBounds.U constantF (decayPoint a b)
  have left := (GaussianEulerIntegrandName.sample_original_sum (Γ := Γ) p oneCode one a b).eqTrans
    (sum_index_congr scalarBody (congrSucc (cutoff_one p a b)) (exponent_one (GaussianEulerIntegrandName.exponentClock p oneCode one a b) a b))
  have right := (GaussianRadiusExponentialName.sample_at (Γ := Γ) constantF R p (decayPoint a b)).eqTrans
    (sum_index_congr scalarBody (.eqRefl _) (constant_at _ _))
  exact left.eqTrans right.eqSymm

theorem original_evaluator_is_decay (p a b x : PTm n) : Γ ⊢[PRAAx]
    ap3 evaluatorF p (pairT a b) (fixedData oneCode one) ≐
      ap3 GaussianEulerDecayQuadrature.evaluatorF p (pairT a b) x :=
  (original_sample_is_decay p a b).eqTrans (GaussianEulerDecayQuadrature.evaluator_at p a b x).eqSymm

theorem original_grid_row_is_decay (i p N a C E x : PTm n) : Γ ⊢[PRAAx]
    inst2 (sampleBody evaluatorF) i (sampleData p N a C E (fixedData oneCode one)) ≐
      inst2 (sampleBody GaussianEulerDecayQuadrature.evaluatorF) i (sampleData p N a C E x) :=
  (GaussianCompactRiemannName.sample_body_at evaluatorF i p N a C E _).eqTrans
    ((original_evaluator_is_decay p _ _ x).eqTrans (GaussianCompactRiemannName.sample_body_at _ i p N a C E x).eqSymm)

theorem original_grid_is_decay (p N a C E x : PTm n) : Γ ⊢[PRAAx]
    quadrature evaluatorF p N a C E (fixedData oneCode one) ≐
      quadrature GaussianEulerDecayQuadrature.evaluatorF p N a C E x := by
  have rows : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual (sampleBody evaluatorF)
      (sampleBody GaussianEulerDecayQuadrature.evaluatorF) N (sampleData p N a C E (fixedData oneCode one)) (sampleData p N a C E x) := by
    refine .allI (.impI ?_)
    simpa only [GaussianRationalFiniteSum.termsEqual,GaussianCompactRiemannName.subst_sampleData,
      GaussianEulerIntegrandName.subst_fixedData,ComplexLogarithmRemainder.subst_oneCode,ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero,Syn.shift] using
      (original_grid_row_is_decay (Γ := _ :: Γ.map Fm.shift) (var 0) (Syn.shift p) (Syn.shift N) (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift x))
  exact qmul_congr (.eqRefl _) (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ rows)

theorem original_Euler_unit_integrand_literal_decay_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (GaussianEulerIntegrandName.sample (var 0) oneCode one (var 1) (var 2) ≐ ap2 decayF (var 0) (decayData (var 1) (var 2))) :=
  closeUniv 3 (original_sample_is_decay _ _ _)

theorem original_Euler_unit_quadrature_literal_decay_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (quadrature evaluatorF (var 0) (var 1) (var 2) (var 3) (var 4) (fixedData oneCode one) ≐
      quadrature GaussianEulerDecayQuadrature.evaluatorF (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (original_grid_is_decay _ _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianEulerUnitNormalizationIntegrand
