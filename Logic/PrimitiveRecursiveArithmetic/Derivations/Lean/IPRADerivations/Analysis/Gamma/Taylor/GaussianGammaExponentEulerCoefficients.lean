import IPRADerivations.Analysis.Gamma.Taylor.GaussianGammaExponentCoefficientStability
import IPRADerivations.Analysis.Logarithm.FiniteSeries.GaussianFiniteLogarithmCoefficientRecursion

/-!
# Euler coefficients of the actual sampled Gamma exponent

The original padded exponent buffer has zero Euler constant, its original
sampled gamma-H_N linear coefficient, and signed original reciprocal-power
tail samples at every higher degree. The factor m cancels the actual
logarithmic coefficient 1/m. At N=0 the same literal finite tail sample is
the existing zeta sample. The genuine factorial-exponential prior
recursion applies to this SAME input with its shape and zero-constant
guards discharged. No logarithmic identity or canonical Gamma recurrence
is assumed; the original Euler-head contribution remains separate.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaExponentEulerCoefficients

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qzero qmul)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient exponent_inside)
open GaussianRationalNaturalScale (natScale natScale_congr)
open GaussianRationalEulerCoefficients (euler parityPoint)
open GaussianGammaExponentCoefficientPolynomial (polynomial)
open GaussianGammaReciprocalDegreeCells (degree)
open RationalGaussianEmbedding (embed)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem degree_fits (L j : PTm n) (hj : Γ ⊢[PRAAx] le j L) : Γ ⊢[PRAAx]
    le (degree j) (degree L) :=
  le_congr (by unfold degree; ipra_ring) (by unfold degree; ipra_ring) (add_le_add_right two hj)

theorem euler_zero (q N L : PTm n) : Γ ⊢[PRAAx]
    exponentCoefficient (euler (polynomial q N L) (degree L)) (degree L) zero ≐ qzero :=
  (GaussianRationalEulerCoefficients.euler_exponent _ _ _ (zero_le _)).eqTrans
    (GaussianRationalNaturalScale.natScale_zero _)

theorem euler_linear (q N L : PTm n) : Γ ⊢[PRAAx]
    exponentCoefficient (euler (polynomial q N L) (degree L)) (degree L) one ≐
      GaussianGammaLinearCoefficient.coefficient q N :=
  (GaussianRationalEulerCoefficients.euler_exponent _ _ _
    (le_trans (le_succ_self one) (GaussianGammaZetaDegreeName.degree_positive L))).eqTrans
      ((natScale_congr (.eqRefl _) (GaussianGammaExponentCoefficientStability.linear_reader q N L)).eqTrans
        (GaussianRationalNaturalScale.natScale_one_canonical _ (GaussianRationalMetric.qsub_canonical _ _)))

theorem euler_high (q N L j : PTm n) (hj : Γ ⊢[PRAAx] le j L) : Γ ⊢[PRAAx]
    exponentCoefficient (euler (polynomial q N L) (degree L)) (degree L) (degree j) ≐
      qmul (parityPoint (succ j)) (embed (RationalReciprocalPowerName.tailSample q (degree j) N)) :=
  (GaussianRationalEulerCoefficients.euler_exponent _ _ _ (degree_fits L j hj)).eqTrans
    ((natScale_congr (.eqRefl _) (GaussianGammaExponentCoefficientStability.high_reader q N L j hj)).eqTrans
      ((GaussianRationalWeightedCoefficientConvolution.left_scale_product _ _ _).eqTrans
        (qmul_congr (GaussianRationalEulerCoefficients.logarithm_weight_cancel (succ j)) (.eqRefl _))))

theorem original_zero_cutoff_tail (q m : PTm n) : Γ ⊢[PRAAx]
    RationalReciprocalPowerName.tailSample q m zero ≐ RationalReciprocalPowerName.zetaSample q m :=
  (RationalReciprocalPowerName.tail_sample_at q m zero).eqTrans
    (RationalReciprocalPowerName.zeta_sample_at q m).eqSymm

theorem zero_cutoff_euler_high (q L j : PTm n) (hj : Γ ⊢[PRAAx] le j L) : Γ ⊢[PRAAx]
    exponentCoefficient (euler (polynomial q zero L) (degree L)) (degree L) (degree j) ≐
      qmul (parityPoint (succ j)) (embed (RationalReciprocalPowerName.zetaSample q (degree j))) :=
  (euler_high q zero L j hj).eqTrans
    (qmul_congr (.eqRefl _) (RationalGaussianRealPart.embed_congr (original_zero_cutoff_tail q (degree j))))

theorem actual_exponential_recursion (q N L K e : PTm n)
    (he : Γ ⊢[PRAAx] le e (degree L)) (hK : Γ ⊢[PRAAx] le e K) : Γ ⊢[PRAAx]
    natScale e (exponentCoefficient
      (GaussianRationalPolynomialExponential.polynomial (polynomial q N L) (degree L) K) (K*degree L) e) ≐
        GaussianRationalCoefficientRecursion.priorSum (euler (polynomial q N L) (degree L)) (degree L)
          (GaussianRationalPolynomialExponential.polynomial (polynomial q N L) (degree L) K) (K*degree L) e :=
  GaussianFiniteLogarithmCoefficientRecursion.finite_recursion_point _ _ _ _
    (GaussianGammaExponentCoefficientPolynomial.polynomial_length q N L)
    (GaussianRationalMonicReduction.added_canonical _ _ _)
    (GaussianGammaPolynomialConstantLinear.input_constant q N L) he hK

theorem original_Gamma_exponent_signed_reciprocal_tail_Euler_coefficients_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (le (var 3) (var 2) ⟶
        exponentCoefficient (euler (polynomial (var 0) (var 1) (var 2)) (degree (var 2)))
          (degree (var 2)) (degree (var 3)) ≐
            qmul (parityPoint (succ (var 3)))
              (embed (RationalReciprocalPowerName.tailSample (var 0) (degree (var 3)) (var 1)))) :=
  closeUniv 4 (.impI (euler_high _ _ _ _ Prf.hyp0))

theorem original_Gamma_exponent_actual_factorial_exponential_prior_recursion_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (le (var 4) (degree (var 2)) ⟶ le (var 4) (var 3) ⟶
        natScale (var 4) (exponentCoefficient
          (GaussianRationalPolynomialExponential.polynomial (polynomial (var 0) (var 1) (var 2))
            (degree (var 2)) (var 3)) (var 3*degree (var 2)) (var 4)) ≐
          GaussianRationalCoefficientRecursion.priorSum
            (euler (polynomial (var 0) (var 1) (var 2)) (degree (var 2))) (degree (var 2))
            (GaussianRationalPolynomialExponential.polynomial (polynomial (var 0) (var 1) (var 2))
              (degree (var 2)) (var 3)) (var 3*degree (var 2)) (var 4)) :=
  closeUniv 5 (.impI (.impI (actual_exponential_recursion _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaExponentEulerCoefficients
