import IPRADerivations.Analysis.Gamma.EulerProducts.Approximants.GaussianGammaFiniteEulerFactorization

/-!
# The actual finite sampled Gamma coefficient recurrence

The original combined kernel has proved constant one. The genuine
original Cauchy-to-prior-sum program therefore splits its product with
the SAME finite Gamma polynomial into the previous-coefficient sum plus
the current coefficient. Actual natural scaling and normalized
subtraction cancel the current coefficient, giving
s*c_(s+1)=priorSum(kernel, original polynomial, s+1).
Only numerical horizon guards remain. No coefficient or output law is
an input; passage to canonical names in C42 remains separate.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaFiniteCoefficientRecurrence

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qadd)
open GaussianRationalSyntheticDivision (qone qadd_congr qmul_congr qsub_congr)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient exponent_inside data)
open GaussianRationalPolynomialProduct (product)
open GaussianRationalCoefficientRecursion (priorTerm priorBody priorSum)
open GaussianRationalNaturalScale (natScale)
open GaussianGammaFiniteEulerFactorization (whole totalDegree)
open GaussianGammaReciprocalDegreeCells (degree)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem last_prior_unit (P D C B e : PTm n) (hP : Γ ⊢[PRAAx] entry P D ≐ qone) : Γ ⊢[PRAAx]
    priorTerm P D C B e e ≐ GaussianTranslatedNonconstant.recode (exponentCoefficient C B e) := by
  have kernel : Γ ⊢[PRAAx] exponentCoefficient P D (monus e e) ≐ qone :=
    (GaussianRationalPolynomialExponentialStability.exponent_congr (.eqRefl _) (.eqRefl _) (monus_self e)).eqTrans
      ((exponent_inside _ _ _ (zero_le D)).eqTrans ((entry_congr (.eqRefl _) (monus_zero D)).eqTrans hP))
  exact (qmul_congr (.eqRefl _) kernel).eqTrans
    ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans (GaussianRationalFiniteProduct.raw_one_left _))

theorem original_product_prior_with_unit (P D C B e : PTm n)
    (hLP : Γ ⊢[PRAAx] length P ≐ succ D) (hLC : Γ ⊢[PRAAx] length C ≐ succ B)
    (hP : Γ ⊢[PRAAx] entry P D ≐ qone)
    (heD : Γ ⊢[PRAAx] le e D) (heB : Γ ⊢[PRAAx] le e B) : Γ ⊢[PRAAx]
    exponentCoefficient (product P C D B) (D+B) e ≐ qadd (priorSum P D C B e) (exponentCoefficient C B e) :=
  (GaussianFiniteLogarithmCoefficientRecursion.product_commuted_exponent P D C B e hLP hLC heD).eqTrans
    ((GaussianRationalLowCoefficientConvolution.product_exponent C P B D e heB heD).eqTrans
      ((GaussianFiniteLogarithmCoefficientRecursion.cauchy_to_prior P D C B e heD heB).eqTrans
        ((GaussianRationalFiniteSum.sum_succ priorBody e (data P C D B e)).eqTrans
          ((qadd_congr (.eqRefl _) ((GaussianRationalCoefficientRecursion.prior_at P D C B e e).eqTrans
            (last_prior_unit P D C B e hP))).eqTrans
              (GaussianRationalSyntheticCoefficientValues.qadd_recode_right _ _)))))

def coefficient (q N L K e : PTm n) : PTm n := exponentCoefficient (whole q N L K) (totalDegree N L K) e
def recurrenceSum (q N L K e : PTm n) : PTm n := priorSum
  (GaussianGammaCombinedEulerKernelPolynomial.polynomial q N L) (degree L)
  (whole q N L K) (totalDegree N L K) e
@[simp] theorem subst_coefficient {l : ℕ} (σ : Fin n → PTm l) (q N L K e : PTm n) :
    Syn.subst σ (coefficient q N L K e) =
      coefficient (Syn.subst σ q) (Syn.subst σ N) (Syn.subst σ L) (Syn.subst σ K) (Syn.subst σ e) := by simp [coefficient]
@[simp] theorem subst_recurrenceSum {l : ℕ} (σ : Fin n → PTm l) (q N L K e : PTm n) :
    Syn.subst σ (recurrenceSum q N L K e) =
      recurrenceSum (Syn.subst σ q) (Syn.subst σ N) (Syn.subst σ L) (Syn.subst σ K) (Syn.subst σ e) := by simp [recurrenceSum]

theorem scaled_prior (q N L K e : PTm n) (hD : Γ ⊢[PRAAx] le e (degree L))
    (hK : Γ ⊢[PRAAx] le e K) (hH : Γ ⊢[PRAAx] le e (succ N)) : Γ ⊢[PRAAx]
    natScale e (coefficient q N L K e) ≐ qadd (recurrenceSum q N L K e) (coefficient q N L K e) :=
  (GaussianGammaFiniteEulerFactorization.original_scaled_coefficient_factorization q N L K e hD hK hH).eqTrans
    (original_product_prior_with_unit _ _ _ _ _
      (GaussianGammaCombinedEulerKernelPolynomial.polynomial_length q N L) (GaussianRationalPolynomialProduct.product_length _ _ _ _)
      (GaussianGammaCombinedEulerKernelPolynomial.constant q N L) hD (le_trans hH (le_add_right _ _)))

theorem original_sampled_coefficient_recurrence (q N L K s : PTm n)
    (hD : Γ ⊢[PRAAx] le (succ s) (degree L)) (hK : Γ ⊢[PRAAx] le (succ s) K)
    (hH : Γ ⊢[PRAAx] le (succ s) (succ N)) : Γ ⊢[PRAAx]
    natScale s (coefficient q N L K (succ s)) ≐ recurrenceSum q N L K (succ s) :=
  (GaussianReciprocalHorner.qsub_add_cancel _ _ (GaussianRationalNaturalScale.natScale_canonical _ _)).eqSymm.eqTrans
    ((qsub_congr ((GaussianGammaEulerHeadNewton.scale_succ s _).eqSymm.eqTrans
      (scaled_prior q N L K (succ s) hD hK hH)) (.eqRefl _)).eqTrans
        (GaussianReciprocalHorner.qsub_add_cancel _ _ (GaussianRationalFiniteSum.sum_canonical _ _ _)))

theorem original_finite_Gamma_sampled_coefficient_prior_recurrence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (succ (var 4)) (degree (var 2)) ⟶ le (succ (var 4)) (var 3) ⟶ le (succ (var 4)) (succ (var 1)) ⟶
      natScale (var 4) (coefficient (var 0) (var 1) (var 2) (var 3) (succ (var 4))) ≐
        recurrenceSum (var 0) (var 1) (var 2) (var 3) (succ (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (original_sampled_coefficient_recurrence _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianGammaFiniteCoefficientRecurrence
