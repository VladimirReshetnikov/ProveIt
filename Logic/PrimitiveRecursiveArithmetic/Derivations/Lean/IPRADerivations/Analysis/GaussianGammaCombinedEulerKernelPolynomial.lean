import IPRADerivations.Analysis.GaussianGammaEulerHeadLogarithmicKernel
import IPRADerivations.Analysis.GaussianGammaCombinedEulerKernel

/-!
# The actual stored combined Gamma Euler kernel

The SAME original harmonic head kernel and the actual Euler buffer of
the SAME sampled Gamma exponent are added by the original coefficient
program. Its real cells are constant one, the original sampled gamma
linearly, and signed original reconstructed zeta samples at every higher
degree. This binds the source kernel to an actual stored finite buffer;
the full product-Euler factorization and canonical C42 are separate.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaCombinedEulerKernelPolynomial

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qmul)
open GaussianRationalSyntheticDivision (qone qadd_congr qmul_congr)
open GaussianRationalEulerCoefficients (euler parityPoint)
open GaussianGammaReciprocalDegreeCells (degree)
open GaussianRationalLowCoefficientConvolution (exponent_inside)
open GaussianGammaHarmonicPowerPoints (point)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def polynomial (q N L : PTm n) : PTm n := GaussianRationalPolynomialBuffers.added
  (GaussianGammaEulerHeadLogarithmicKernel.kernel N (degree L))
  (euler (GaussianGammaExponentCoefficientPolynomial.polynomial q N L) (degree L)) (succ (degree L))
@[simp] theorem subst_polynomial {l : ℕ} (σ : Fin n → PTm l) (q N L : PTm n) :
    Syn.subst σ (polynomial q N L) = polynomial (Syn.subst σ q) (Syn.subst σ N) (Syn.subst σ L) := by simp [polynomial]

theorem polynomial_length (q N L : PTm n) : Γ ⊢[PRAAx] length (polynomial q N L) ≐ succ (degree L) :=
  GaussianRationalPolynomialBuffers.added_length _ _ _

theorem constant (q N L : PTm n) : Γ ⊢[PRAAx] entry (polynomial q N L) (degree L) ≐ qone :=
  (GaussianRationalPolynomialBuffers.added_lookup _ _ _ _ (le_refl (succ (degree L)))).eqTrans
    ((qadd_congr (GaussianGammaEulerHeadLogarithmicKernel.kernel_constant N (degree L))
      (GaussianRationalEulerCoefficients.euler_constant _ _)).eqTrans
        (GaussianReciprocalHorner.qadd_zero_right _ GaussianRationalSyntheticDivision.qone_canonical))

theorem degree_at_least_one (L : PTm n) : Γ ⊢[PRAAx] le one (degree L) :=
  le_trans (le_succ_self one) (GaussianGammaZetaDegreeName.degree_positive L)

theorem head_linear (N L : PTm n) : Γ ⊢[PRAAx]
    entry (GaussianGammaEulerHeadLogarithmicKernel.kernel N (degree L)) (monus (degree L) one) ≐ point one N :=
  (GaussianGammaEulerHeadLogarithmicKernel.kernel_positive N (degree L) zero (degree_at_least_one L)).eqTrans
    ((qmul_congr GaussianRationalParityPower.parity_zero (.eqRefl _)).eqTrans
      (GaussianPolynomialDeterminantTerms.one_mul_canonical _ (GaussianGammaHarmonicPowerPoints.point_canonical _ _)))

theorem linear (q N L : PTm n) : Γ ⊢[PRAAx]
    entry (polynomial q N L) (monus (degree L) one) ≐
      RationalGaussianEmbedding.embed (GammaEulerConstantName.gammaSample q zero) :=
  (GaussianRationalPolynomialBuffers.added_lookup _ _ _ _
    ((succ_monus_succ _ _).eqTrans (GaussianRationalMonicReconstruction.monus_le_left _ _))).eqTrans
      ((qadd_congr (head_linear N L) (exponent_inside _ _ _ (degree_at_least_one L)).eqSymm).eqTrans
        (GaussianGammaCombinedEulerKernel.linear_total q N L))

theorem high (q N L j : PTm n) (hj : Γ ⊢[PRAAx] le j L) : Γ ⊢[PRAAx]
    entry (polynomial q N L) (monus (degree L) (degree j)) ≐
      qmul (parityPoint (succ j))
        (RationalGaussianEmbedding.embed (RationalReciprocalPowerName.reconstructedSample q (degree j) N)) :=
  (GaussianRationalPolynomialBuffers.added_lookup _ _ _ _
    ((succ_monus_succ _ _).eqTrans (GaussianRationalMonicReconstruction.monus_le_left _ _))).eqTrans
      ((qadd_congr
        (GaussianGammaEulerHeadLogarithmicKernel.kernel_positive N (degree L) (succ j)
          (GaussianGammaExponentEulerCoefficients.degree_fits L j hj))
        (exponent_inside _ _ _ (GaussianGammaExponentEulerCoefficients.degree_fits L j hj)).eqSymm).eqTrans
          (GaussianGammaCombinedEulerKernel.high_total q N L j hj))

def polynomialF : PR 3 := PTm.toPR (polynomial (var 0) (var 1) (var 2))
theorem polynomial_program (q N L : PTm n) : Γ ⊢[PRAAx] ap3 polynomialF q N L ≐ polynomial q N L := by
  simpa [polynomialF,ap3] using toPR_eq (Γ := Γ) (polynomial (var 0) (var 1) (var 2) : PTm 3) ![q,N,L]

theorem original_Gamma_stored_combined_Euler_kernel_linear_coefficient_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (entry (polynomial (var 0) (var 1) (var 2)) (monus (degree (var 2)) one) ≐
        RationalGaussianEmbedding.embed (GammaEulerConstantName.gammaSample (var 0) zero)) :=
  closeUniv 3 (linear _ _ _)

theorem original_Gamma_stored_combined_Euler_kernel_high_coefficients_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (le (var 3) (var 2) ⟶ entry (polynomial (var 0) (var 1) (var 2)) (monus (degree (var 2)) (degree (var 3))) ≐
        qmul (parityPoint (succ (var 3)))
          (RationalGaussianEmbedding.embed
            (RationalReciprocalPowerName.reconstructedSample (var 0) (degree (var 3)) (var 1)))) :=
  closeUniv 4 (.impI (high _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaCombinedEulerKernelPolynomial
