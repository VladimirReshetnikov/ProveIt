import IPRADerivations.Analysis.Polynomials.GaussianPolynomialLinearFactorCoefficients
import IPRADerivations.Analysis.Exponential.GaussianRationalPolynomialExponentialCoefficients

/-!
# The literal linear coefficient of a finite polynomial exponential

The existing exponential cutoff theorem reduces exponent one to its
first two actual power terms. Its original constant-one stage and
degree-zero convolution then identify the stored linear coefficient
with the original input linear coefficient. All cutoffs and degrees
are arbitrary internal numerical indices; the original input code must
be canonical only at the single coefficient whose literal equality is
claimed. No power, exponential, or coefficient output law is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialExponentialLinear

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qzero qmul canonical ofGaussian)
open GaussianRationalSyntheticDivision (qone qmul_congr qadd_congr)
open GaussianRationalPolynomialExponential (polynomial inverseFactorial)
open GaussianRationalPolynomialPowers (powerPrefix)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient exponent_inside exponent_outside)
open GaussianRationalPolynomialExponentialStability (coefficient exponent_congr)
open GaussianRationalMonicReduction (singleton)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (entry_congr)
open Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem inverse_factorial_one : Γ ⊢[PRAAx] inverseFactorial (one : PTm n) ≐ qone := by
  have f : Γ ⊢[PRAAx] fact (one : PTm n) ≐ one :=
    (fact_succ zero zero).eqTrans ((congrMul (fact_zero zero) (.eqRefl one)).eqTrans (by ipra_ring))
  simpa only [inverseFactorial,GaussianRationalHorner.subst_ofGaussian,
    ComplexLogarithmRemainder.subst_oneCode,Syn.subst_var,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.head_cons,GaussianRationalSyntheticDivision.qone] using
    (Prf.eqCongr (Γ := Γ) (ofGaussian (var 0) (var 1) : PTm 2)
      (σ := ![ComplexLogarithmRemainder.oneCode,fact one])
      (σ' := ![ComplexLogarithmRemainder.oneCode,one])
      (fun i => by fin_cases i; exact .eqRefl _; exact f))

theorem first_power_linear (C N K : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hK : Γ ⊢[PRAAx] le one K)
    (hc : Γ ⊢[PRAAx] canonical (entry C (monus N one))) : Γ ⊢[PRAAx]
    exponentCoefficient (powerPrefix C N K one) (one*N) one ≐ entry C (monus N one) := by
  have code := (GaussianRationalPolynomialPowers.prefix_succ (Γ := Γ) C N K zero hK).eqTrans
    (GaussianPolynomialDeterminantTerms.product_congr (GaussianRationalPolynomialPowers.prefix_zero C N K)
      (.eqRefl C) (zero_mul N) (.eqRefl N))
  exact (exponent_congr code (one_mul N) (.eqRefl one)).eqTrans
    ((exponent_inside _ _ _ hN).eqTrans
      ((GaussianPolynomialLinearFactorCoefficients.constant_left_value _ _ _ _
        (GaussianRationalMonicReconstruction.monus_le_left N one)).eqTrans
          (GaussianPolynomialDeterminantTerms.one_mul_canonical _ hc)))

theorem linear_reader (C N K : PTm n) (hC : Γ ⊢[PRAAx] entry C N ≐ qzero)
    (hN : Γ ⊢[PRAAx] le one N) (hK : Γ ⊢[PRAAx] le one K)
    (hc : Γ ⊢[PRAAx] canonical (entry C (monus N one))) : Γ ⊢[PRAAx]
    exponentCoefficient (polynomial C N K) (K*N) one ≐ entry C (monus N one) := by
  have initial : Γ ⊢[PRAAx] coefficient C N K zero one ≐ qzero :=
    (exponent_congr (GaussianRationalPolynomialExponential.stage_zero C N K) (zero_mul N) (.eqRefl one)).eqTrans
      (exponent_outside (singleton qone) zero one (le_refl one))
  have term : Γ ⊢[PRAAx] GaussianRationalPolynomialExponentialCoefficients.term C N K one one ≐ entry C (monus N one) :=
    (qmul_congr inverse_factorial_one (first_power_linear C N K hN hK hc)).eqTrans
      (GaussianPolynomialDeterminantTerms.one_mul_canonical _ hc)
  exact (GaussianRationalPolynomialExponentialStability.finite_exponential_cutoff C N K one hC hN hK).eqTrans
    ((GaussianRationalPolynomialExponentialCoefficients.coefficient_recurrence C N K zero one hN).eqTrans
      ((qadd_congr initial term).eqTrans (GaussianRationalSyntheticDivision.qzero_add _ hc)))

theorem linear_value (C N K : PTm n) (hC : Γ ⊢[PRAAx] entry C N ≐ qzero)
    (hN : Γ ⊢[PRAAx] le one N) (hK : Γ ⊢[PRAAx] le one K)
    (hc : Γ ⊢[PRAAx] canonical (entry C (monus N one))) : Γ ⊢[PRAAx]
    entry (polynomial C N K) (monus (K*N) one) ≐ entry C (monus N one) := by
  have hD : Γ ⊢[PRAAx] le one (K*N) := le_congr (by ipra_ring) (.eqRefl _)
    (LeanProofs.IPRA.AnalyticNumberTheory.PhiLower.le_mul_mono hK hN)
  exact (exponent_inside _ _ _ hD).eqSymm.eqTrans (linear_reader C N K hC hN hK hc)

theorem actual_finite_exponential_linear_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (entry (var 0) (var 1) ≐ qzero ⟶ le one (var 1) ⟶ le one (var 2) ⟶
      canonical (entry (var 0) (monus (var 1) one)) ⟶
      entry (polynomial (var 0) (var 1) (var 2)) (monus (var 2*var 1) one) ≐
        entry (var 0) (monus (var 1) one)) :=
  closeUniv 3 (.impI (.impI (.impI (.impI (linear_value _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianPolynomialExponentialLinear
