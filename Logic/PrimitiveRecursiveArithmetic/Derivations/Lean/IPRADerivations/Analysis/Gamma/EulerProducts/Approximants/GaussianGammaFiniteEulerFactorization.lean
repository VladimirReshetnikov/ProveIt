import IPRADerivations.Analysis.Polynomials.Products.GaussianPolynomialProductEulerFactorization
import IPRADerivations.Analysis.Gamma.EulerProducts.Exponents.GaussianGammaCombinedEulerKernelPolynomial
import IPRADerivations.Analysis.Gamma.Taylor.GaussianGammaFiniteCoefficientPolynomial

/-!
# Actual finite Gamma polynomial Euler factorization

The original stored head and the actual factorial exponential of the
original sampled exponent supply their genuine kernel jets internally.
The actual full finite Gamma polynomial therefore satisfies
Euler(P)=(head harmonic kernel+Euler(original exponent))*P through the
stated numerical degree cutoffs. No component jet, differential equation
or output identity is an input. The generic source-specific kernel cells
are the original gamma and reconstructed-zeta samples; canonical C42
observation transport remains separate.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaFiniteEulerFactorization

open_ipra
open GaussianRationalHorner (qzero)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient exponent_inside)
open GaussianRationalPolynomialProduct (product)
open GaussianRationalEulerCoefficients (euler)
open GaussianRationalNaturalScale (natScale)
open GaussianPolynomialLowJetProduct (jetEqual)
open GaussianGammaEulerHeadLogarithmicKernel (kernel)
open GaussianGammaEulerHeadPolynomial (polynomial)
open GaussianGammaReciprocalDegreeCells (degree)
open LeanProofs.IPRA.Foundations.SequenceComposition (entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem head_product_zero (N D : PTm n) : Γ ⊢[PRAAx]
    exponentCoefficient (product (kernel N D) (polynomial N) D (succ N)) (D+succ N) zero ≐ qzero :=
  (exponent_inside _ _ _ (zero_le _)).eqTrans
    ((entry_congr (.eqRefl _) (monus_zero _)).eqTrans
      ((GaussianPolynomialFirstCoefficients.constant_value _ _ _ _).eqTrans
        ((qmul_congr (GaussianGammaEulerHeadLogarithmicKernel.kernel_constant N D)
          (GaussianGammaEulerHeadCoefficientStep.constant_zero N)).eqTrans
            (GaussianRationalSyntheticDivision.qmul_zero_right _))))

theorem head_kernel_reader (N D e : PTm n) (hN : Γ ⊢[PRAAx] le e (succ N))
    (hD : Γ ⊢[PRAAx] le e D) : Γ ⊢[PRAAx]
    exponentCoefficient (euler (polynomial N) (succ N)) (succ N) e ≐
      exponentCoefficient (product (kernel N D) (polynomial N) D (succ N)) (D+succ N) e := by
  refine .orE (zero_or_succ e) ?_ ?_
  · have left : ((e ≐ zero) :: Γ) ⊢[PRAAx]
        exponentCoefficient (euler (polynomial N) (succ N)) (succ N) e ≐ qzero :=
      (GaussianRationalPolynomialExponentialStability.exponent_congr (.eqRefl _) (.eqRefl _) Prf.hyp0).eqTrans
        ((GaussianRationalEulerCoefficients.euler_exponent _ _ _ (zero_le _)).eqTrans
          (GaussianRationalNaturalScale.natScale_zero _))
    exact left.eqTrans ((head_product_zero N D).eqSymm.eqTrans
      (GaussianRationalPolynomialExponentialStability.exponent_congr (.eqRefl _) (.eqRefl _) Prf.hyp0.eqSymm))
  · have nh : ((e ≐ succ (pred e)) :: Γ) ⊢[PRAAx] le (succ (pred e)) (succ N) :=
      le_congr Prf.hyp0 (.eqRefl _) hN.wk
    have dh : ((e ≐ succ (pred e)) :: Γ) ⊢[PRAAx] le (succ (pred e)) D :=
      le_congr Prf.hyp0 (.eqRefl _) hD.wk
    exact (GaussianRationalPolynomialExponentialStability.exponent_congr (.eqRefl _) (.eqRefl _) Prf.hyp0).eqTrans
      ((GaussianGammaEulerHeadLogarithmicKernel.original_positive_Euler_product N D (pred e) dh nh).eqSymm.eqTrans
        (GaussianRationalPolynomialExponentialStability.exponent_congr (.eqRefl _) (.eqRefl _) Prf.hyp0.eqSymm))

theorem head_kernel_jet (N D e : PTm n) (hN : Γ ⊢[PRAAx] le e (succ N))
    (hD : Γ ⊢[PRAAx] le e D) : Γ ⊢[PRAAx]
    jetEqual (euler (polynomial N) (succ N)) (succ N)
      (product (kernel N D) (polynomial N) D (succ N)) (D+succ N) e := by
  have ns : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift e) (succ (Syn.shift N)) := by simpa [Fm.shift,Syn.shift] using hN.shift
  have ds : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift e) (Syn.shift D) := by simpa [Fm.shift,Syn.shift] using hD.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (succ (Syn.shift e)) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] le (var 0) (Syn.shift e) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  simpa only [Δ,Syn.shift,GaussianGammaEulerHeadPolynomial.subst_polynomial,GaussianGammaEulerHeadLogarithmicKernel.subst_kernel,
    GaussianRationalEulerCoefficients.subst_euler,GaussianRationalPolynomialProduct.subst_product,PTm.subst_add,PTm.subst_succ] using
      head_kernel_reader (Syn.shift N) (Syn.shift D) (var 0) (le_trans hi ns.wk) (le_trans hi ds.wk)

def input (q N L : PTm n) : PTm n := GaussianGammaExponentCoefficientPolynomial.polynomial q N L
def exponential (q N L K : PTm n) : PTm n := GaussianRationalPolynomialExponential.polynomial (input q N L) (degree L) K
def totalDegree (N L K : PTm n) : PTm n := succ N+K*degree L
def whole (q N L K : PTm n) : PTm n := product (polynomial N) (exponential q N L K) (succ N) (K*degree L)
ipra_subst input
ipra_subst exponential
ipra_subst totalDegree
ipra_subst whole

theorem exponential_kernel_reader (q N L K e : PTm n) (hD : Γ ⊢[PRAAx] le e (degree L))
    (hK : Γ ⊢[PRAAx] le e K) : Γ ⊢[PRAAx]
    exponentCoefficient (euler (exponential q N L K) (K*degree L)) (K*degree L) e ≐
      exponentCoefficient (product (euler (input q N L) (degree L)) (exponential q N L K)
        (degree L) (K*degree L)) (degree L+K*degree L) e :=
  (GaussianRationalEulerCoefficients.euler_exponent _ _ _
    (GaussianRationalPolynomialPowerSupport.min_product e K (degree L) hD hK)).eqTrans
      (GaussianRationalFiniteExponentialEuler.finite_euler_scaled _ _ _ _
        (GaussianGammaExponentCoefficientPolynomial.polynomial_length q N L)
        (GaussianRationalMonicReduction.added_canonical _ _ _)
        (GaussianGammaPolynomialConstantLinear.input_constant q N L) hD hK)

theorem exponential_kernel_jet (q N L K e : PTm n) (hD : Γ ⊢[PRAAx] le e (degree L))
    (hK : Γ ⊢[PRAAx] le e K) : Γ ⊢[PRAAx]
    jetEqual (euler (exponential q N L K) (K*degree L)) (K*degree L)
      (product (euler (input q N L) (degree L)) (exponential q N L K) (degree L) (K*degree L))
        (degree L+K*degree L) e := by
  have ds : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift e) (degree (Syn.shift L)) := by simpa [Fm.shift,Syn.shift] using hD.shift
  have ks : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift e) (Syn.shift K) := by simpa [Fm.shift,Syn.shift] using hK.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (succ (Syn.shift e)) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] le (var 0) (Syn.shift e) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  simpa only [Δ,Syn.shift,subst_exponential,subst_input,GaussianGammaReciprocalDegreeCells.subst_degree,
    GaussianRationalEulerCoefficients.subst_euler,GaussianRationalPolynomialProduct.subst_product,PTm.subst_add,PTm.subst_mul] using
      exponential_kernel_reader (Syn.shift q) (Syn.shift N) (Syn.shift L) (Syn.shift K) (var 0) (le_trans hi ds.wk) (le_trans hi ks.wk)

theorem original_Euler_factorization (q N L K e : PTm n) (hD : Γ ⊢[PRAAx] le e (degree L))
    (hK : Γ ⊢[PRAAx] le e K) (hH : Γ ⊢[PRAAx] le e (succ N)) : Γ ⊢[PRAAx]
    exponentCoefficient (euler (whole q N L K) (totalDegree N L K)) (totalDegree N L K) e ≐
      exponentCoefficient (product (GaussianGammaCombinedEulerKernelPolynomial.polynomial q N L)
        (whole q N L K) (degree L) (totalDegree N L K)) (degree L+totalDegree N L K) e :=
  GaussianPolynomialProductEulerFactorization.original_product_Euler_factorization _ _ _ _ _ _ _ _
    (GaussianGammaEulerHeadPolynomial.polynomial_length N) (GaussianRationalPolynomialExponential.polynomial_length _ _ _)
    (GaussianGammaEulerHeadLogarithmicKernel.kernel_length N (degree L)) (GaussianRationalEulerCoefficients.euler_length _ _)
    hH (GaussianRationalPolynomialPowerSupport.min_product e K (degree L) hD hK) hD
    (head_kernel_jet N (degree L) e hH hD) (exponential_kernel_jet q N L K e hD hK)

theorem original_scaled_coefficient_factorization (q N L K e : PTm n) (hD : Γ ⊢[PRAAx] le e (degree L))
    (hK : Γ ⊢[PRAAx] le e K) (hH : Γ ⊢[PRAAx] le e (succ N)) : Γ ⊢[PRAAx]
    natScale e (exponentCoefficient (whole q N L K) (totalDegree N L K) e) ≐
      exponentCoefficient (product (GaussianGammaCombinedEulerKernelPolynomial.polynomial q N L)
        (whole q N L K) (degree L) (totalDegree N L K)) (degree L+totalDegree N L K) e :=
  (GaussianRationalEulerCoefficients.euler_exponent _ _ _ (le_trans hH (le_add_right _ _))).eqSymm.eqTrans
    (original_Euler_factorization q N L K e hD hK hH)

theorem original_finite_Gamma_actual_Euler_factorization_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (var 4) (degree (var 2)) ⟶ le (var 4) (var 3) ⟶ le (var 4) (succ (var 1)) ⟶
      natScale (var 4) (exponentCoefficient (whole (var 0) (var 1) (var 2) (var 3)) (totalDegree (var 1) (var 2) (var 3)) (var 4)) ≐
        exponentCoefficient (product (GaussianGammaCombinedEulerKernelPolynomial.polynomial (var 0) (var 1) (var 2))
          (whole (var 0) (var 1) (var 2) (var 3)) (degree (var 2)) (totalDegree (var 1) (var 2) (var 3)))
            (degree (var 2)+totalDegree (var 1) (var 2) (var 3)) (var 4)) :=
  closeUniv 5 (.impI (.impI (.impI (original_scaled_coefficient_factorization _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianGammaFiniteEulerFactorization
