import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerDecayQuadrature
import IPRADerivations.Analysis.Gamma.GaussianGammaEncodingRescaling
import IPRADerivations.Core.CongruenceTactic

/-!
# The original Euler integrand at one

At an encoded unit argument the computed power exponent is identically
zero. The literal Euler exponent and the decay exponent then have the
same zeroth observation, the same computed radius, and the same query
at every scheduled precision. This proves equality of the actual
samples and of the two finite sums on the very same grid.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitIntegrand

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (oneCode scale)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianEulerIntegrandName (coefficient exponentF exponentData decayPoint decayF decayData
  fixedData sample evaluatorF)
open GaussianRationalHorner (qzero ofGaussian)
open GaussianRationalSyntheticDivision (qone qsub_congr qadd_congr qmul_congr qmul_zero_left qzero_add)
open GaussianRationalMetric (qnegative_canonical)
open GaussianEulerDecayMesh (observation)
open GaussianCompactRiemannName (sampleBody sampleData sample_body_at quadrature)
open GaussianRationalFiniteSum (termsEqual)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem encoded_unit_coefficient (B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] coefficient (scale B oneCode) B ≐ qzero := by
  have hc : Γ ⊢[PRAAx] ofGaussian (scale B oneCode) B ≐ qone :=
    (GaussianGammaEncodingRescaling.fraction_denominator_congr _ _ _ (by ipra_ring)).eqTrans
      (GaussianGammaEncodingRescaling.fraction_rescale oneCode one B (le_refl _) hB)
  exact (qsub_congr hc (.eqRefl _)).eqTrans (GaussianCoefficientNormOrder.qsub_self _)

theorem unit_coefficient : Γ ⊢[PRAAx] coefficient (oneCode : PTm n) one ≐ qzero :=
  GaussianCoefficientNormOrder.qsub_self _

theorem unit_exponent_at (p z B a b : PTm n) (h : Γ ⊢[PRAAx] coefficient z B ≐ qzero) :
    Γ ⊢[PRAAx] ap2 exponentF p (exponentData z B a b) ≐ decayPoint a b :=
  (GaussianEulerIntegrandName.exponent_at p z B a b).eqTrans
    ((qadd_congr ((qmul_congr h (.eqRefl _)).eqTrans (qmul_zero_left _)) (.eqRefl _)).eqTrans
      (qzero_add _ (qnegative_canonical _)))

theorem equal_radius (z B a b : PTm n) (h : Γ ⊢[PRAAx] coefficient z B ≐ qzero) :
    Γ ⊢[PRAAx] GaussianEulerIntegrandName.radius z B a b ≐ GaussianNameBounds.U constantF (decayPoint a b) := by
  have hs := (unit_exponent_at zero z B a b h).eqTrans (constant_at zero (decayPoint a b)).eqSymm
  unfold GaussianEulerIntegrandName.radius GaussianNameBounds.U GaussianNameBounds.ceiling GaussianNameBounds.initial
  apply congrAdd _ (.eqRefl two)
  ipra_congr (GaussianGeneralFTAConstants.ceilL1 (var 0) : PTm 1) with [hs]

theorem exact_sample (p z B a b : PTm n) (h : Γ ⊢[PRAAx] coefficient z B ≐ qzero) :
    Γ ⊢[PRAAx] sample p z B a b ≐ observation a b p := by
  let R := GaussianEulerIntegrandName.radius z B a b
  let S := GaussianNameBounds.U constantF (decayPoint a b)
  let Y := decayPoint a b
  let I := GaussianRadiusExponentialName.inputPrecision R p
  let J := GaussianRadiusExponentialName.index R p
  let I' := GaussianRadiusExponentialName.inputPrecision S p
  let J' := GaussianRadiusExponentialName.index S p
  let f : PTm n → PTm n → PTm n := GaussianRationalPolynomialExponential.scalarSum
  have j : Γ ⊢[PRAAx] J ≐ J' := by
    simpa only [J, J', GaussianRadiusExponentialName.subst_index, Syn.subst_var,
      Matrix.cons_val_zero, Matrix.cons_val_one] using
      Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (GaussianRadiusExponentialName.index (var 0) (var 1) : PTm 2)
        (σ := ![R,p]) (σ' := ![S,p]) (fun i => by
          fin_cases i
          · exact equal_radius z B a b h
          · exact .eqRefl p)
  have left : Γ ⊢[PRAAx] sample p z B a b ≐ f Y J :=
    (GaussianEulerIntegrandName.sample_original_sum p z B a b).eqTrans
      (GaussianNameConjugation.scalar_sum_congr J (unit_exponent_at I z B a b h))
  have right : Γ ⊢[PRAAx] observation a b p ≐ f Y J' := by
    have e : Γ ⊢[PRAAx] observation a b p ≐ f (ap2 constantF I' Y) J' :=
      GaussianRadiusExponentialName.sample_at constantF S p Y
    exact e.eqTrans (GaussianNameConjugation.scalar_sum_congr J' (constant_at I' Y))
  have same : Γ ⊢[PRAAx] f Y J ≐ f Y J' :=
    GaussianRationalFiniteSum.sum_index_congr GaussianRationalPolynomialExponential.scalarBody
      (congrSucc j) (.eqRefl Y)
  exact left.eqTrans (same.eqTrans right.eqSymm)

theorem exact_grid_entry (i p N a C E z B : PTm n) (h : Γ ⊢[PRAAx] coefficient z B ≐ qzero) :
    Γ ⊢[PRAAx]
      inst2 (sampleBody evaluatorF) i (sampleData p N a C E (fixedData z B)) ≐
        inst2 (sampleBody GaussianEulerDecayQuadrature.evaluatorF) i (sampleData p N a C E (fixedData z B)) :=
  (sample_body_at evaluatorF i p N a C E (fixedData z B)).eqTrans
    ((exact_sample p z B (a*N+C*i) (E*N) h).eqTrans
      (GaussianEulerDecayQuadrature.cell_at i p N a C E (fixedData z B)).eqSymm)

theorem exact_quadrature (p N a C E z B : PTm n) (h : Γ ⊢[PRAAx] coefficient z B ≐ qzero) :
    Γ ⊢[PRAAx] quadrature evaluatorF p N a C E (fixedData z B) ≐
      quadrature GaussianEulerDecayQuadrature.evaluatorF p N a C E (fixedData z B) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] coefficient (Syn.shift z) (Syn.shift B) ≐ qzero := by
    simpa [Fm.shift, Syn.shift] using h.shift
  let X := fixedData z B
  let f := sampleBody evaluatorF
  let g := sampleBody GaussianEulerDecayQuadrature.evaluatorF
  have entries : Γ ⊢[PRAAx] termsEqual f g N (sampleData p N a C E X) (sampleData p N a C E X) := by
    refine .allI (.impI ?_)
    simpa [termsEqual, f, g, X, Syn.shift, fixedData] using
      exact_grid_entry (var 0) (Syn.shift p) (Syn.shift N) (Syn.shift a) (Syn.shift C)
        (Syn.shift E) (Syn.shift z) (Syn.shift B) hs.wk
  unfold quadrature GaussianRationalRiemannRefinement.leftSum
  exact qmul_congr (.eqRefl _) (GaussianRationalFiniteSum.sum_congr_bounded f g N _ _ entries)

theorem encoded_one_Euler_decay_sample_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ sample (var 0) (scale (var 1) oneCode) (var 1) (var 2) (var 3) ≐
      observation (var 2) (var 3) (var 0)) :=
  closeUniv 4 (.impI (exact_sample _ _ _ _ _ (encoded_unit_coefficient _ Prf.hyp0)))

theorem original_one_Euler_decay_quadrature_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (quadrature evaluatorF (var 0) (var 1) (var 2) (var 3) (var 4) (fixedData oneCode one) ≐
      quadrature GaussianEulerDecayQuadrature.evaluatorF (var 0) (var 1) (var 2) (var 3) (var 4) (fixedData oneCode one)) :=
  closeUniv 5 (exact_quadrature _ _ _ _ _ _ _ unit_coefficient)

end LeanProofs.IPRA.Analysis.GaussianEulerUnitIntegrand
