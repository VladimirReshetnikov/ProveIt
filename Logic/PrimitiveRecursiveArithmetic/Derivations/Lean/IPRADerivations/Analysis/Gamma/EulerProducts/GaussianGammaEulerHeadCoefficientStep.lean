import IPRADerivations.Analysis.Polynomials.GaussianPolynomialRightLinearRows
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaEulerHeadQuadratic

/-!
# The exact neighboring-coefficient step of the original Euler head

Every original interior coefficient of X product(k=1..N+1)(1+X/k)
is the sum of the same coefficient of the original preceding head and
its preceding coefficient times the original reciprocal point 1/(N+1).
The actual buffer convolution supplies the rule at arbitrary internal
rows; all factor and coefficient guards are discharged here. The leading
row and the original zero constant are included, with no Newton identity
or Gamma coefficient recurrence used as an input.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaEulerHeadCoefficientStep

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qzero qadd qmul canonical)
open GaussianRationalSyntheticDivision (qone qmul_congr qadd_congr canonicalCoefficients)
open GaussianGammaEulerHeadPolynomial (polynomial)
open GaussianGammaHarmonicIncrement (reciprocalPoint)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem positive_canonical (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    canonicalCoefficients (polynomial N) := by
  have form := RationalIntegerNormalization.positive_form (Γ := Γ) hN
  have value : Γ ⊢[PRAAx] polynomial N ≐ GaussianGammaEulerHeadPolynomial.advance (pred N) (polynomial (pred N)) :=
    (congrAp2 GaussianGammaEulerHeadPolynomial.headF form (.eqRefl zero)).eqTrans
      (GaussianGammaEulerHeadPolynomial.polynomial_succ (pred N))
  exact GaussianRationalMonicReduction.canonical_coefficients_congr value
    (GaussianRationalPolynomialProduct.product_canonical _ _ _ _)

theorem positive_entry_canonical (N i : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hi : Γ ⊢[PRAAx] le i (succ N)) : Γ ⊢[PRAAx] canonical (entry (polynomial N) i) :=
  GaussianRationalSyntheticDivision.canonical_coefficient_at _ _ (positive_canonical N hN)
    (lt_congr (.eqRefl _) (GaussianGammaEulerHeadPolynomial.polynomial_length N).eqSymm
      ((succ_monus_succ _ _).eqTrans hi))

theorem leading_step (N : PTm n) : Γ ⊢[PRAAx]
    entry (polynomial (succ N)) zero ≐ qmul (entry (polynomial N) zero) (reciprocalPoint N) := by
  have stable := GaussianPolynomialRightLinearRows.coefficient_stabilized (Γ := Γ)
    (polynomial N) (GaussianGammaEulerFactorPolynomial.polynomial N) one (succ (succ N)) zero
      (zero_lt_succ (succ N))
  have first := GaussianPolynomialLinearFactorCoefficients.first_row (Γ := Γ)
    (polynomial N) (GaussianGammaEulerFactorPolynomial.polynomial N) one zero (zero_le one)
  exact (entry_congr (GaussianGammaEulerHeadPolynomial.polynomial_succ N) (.eqRefl zero)).eqTrans
    ((GaussianRationalPolynomialProduct.product_lookup _ _ _ _ zero (zero_le _)).eqTrans
      (stable.eqTrans (first.eqTrans (qmul_congr (.eqRefl _) (GaussianGammaEulerHeadQuadratic.factor_leading N)))))

theorem interior_step (N r : PTm n) (hr : Γ ⊢[PRAAx] le r N) : Γ ⊢[PRAAx]
    entry (polynomial (succ N)) (succ r) ≐
      qadd (entry (polynomial N) r) (qmul (entry (polynomial N) (succ r)) (reciprocalPoint N)) := by
  have raw := GaussianPolynomialRightLinearRows.original_interior_row (Γ := Γ)
    (polynomial N) (GaussianGammaEulerFactorPolynomial.polynomial N) (succ N) r
      ((succ_monus_succ _ _).eqTrans hr)
  have firstCan : Γ ⊢[PRAAx] canonical (entry (polynomial N) r) := by
    refine .orE (zero_or_succ N) ?_ ?_
    · have idx : ((N ≐ zero) :: Γ) ⊢[PRAAx] r ≐ zero :=
        (monus_zero r).eqSymm.eqTrans (le_congr (.eqRefl _) Prf.hyp0 hr.wk)
      have source : ((N ≐ zero) :: Γ) ⊢[PRAAx] entry (polynomial N) r ≐ qone :=
        (entry_congr (congrAp2 GaussianGammaEulerHeadPolynomial.headF Prf.hyp0 (.eqRefl zero)) idx).eqTrans
          ((entry_congr GaussianGammaEulerHeadPolynomial.polynomial_zero (.eqRefl zero)).eqTrans
            (GaussianGammaLinearCoefficient.monomial_leading qone))
      exact GaussianRationalHorner.canonical_congr source GaussianRationalSyntheticDivision.qone_canonical
    · have pos : ((N ≐ succ (pred N)) :: Γ) ⊢[PRAAx] le one N :=
        le_congr (.eqRefl one) Prf.hyp0.eqSymm (zero_lt_succ (pred N))
      exact positive_entry_canonical N r pos (le_trans hr.wk (le_succ_self N))
  exact (entry_congr (GaussianGammaEulerHeadPolynomial.polynomial_succ N) (.eqRefl (succ r))).eqTrans
    (raw.eqTrans ((qadd_congr
      ((qmul_congr (.eqRefl _) (GaussianGammaPolynomialConstantLinear.factor_constant N)).eqTrans
        (GaussianReciprocalHorner.qmul_one_right _ firstCan))
      (qmul_congr (.eqRefl _) (GaussianGammaEulerHeadQuadratic.factor_leading N)))))

theorem constant_zero (N : PTm n) : Γ ⊢[PRAAx]
    entry (polynomial N) (succ N) ≐ qzero :=
  (GaussianGammaPolynomialConstantLinear.head_low N).andE₁

theorem original_Euler_head_leading_coefficient_step_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (entry (polynomial (succ (var 0))) zero ≐ qmul (entry (polynomial (var 0)) zero) (reciprocalPoint (var 0))) :=
  closeUniv 1 (leading_step _)

theorem original_Euler_head_all_interior_coefficient_steps_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (var 1) (var 0) ⟶ entry (polynomial (succ (var 0))) (succ (var 1)) ≐
      qadd (entry (polynomial (var 0)) (var 1))
        (qmul (entry (polynomial (var 0)) (succ (var 1))) (reciprocalPoint (var 0)))) :=
  closeUniv 2 (.impI (interior_step _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaEulerHeadCoefficientStep
