import IPRADerivations.Analysis.Gamma.Taylor.GaussianGammaExponentEulerCoefficients
import IPRADerivations.Analysis.Gamma.EulerProducts.Exponents.GaussianGammaHarmonicPowerPoints
import IPRADerivations.Analysis.Names.Arithmetic.RationalGaussianNameEmbedding

/-!
# The original harmonic and tail contributions give the C42 kernel

The linear harmonic term cancels the SAME original sampled gamma-H_N.
At every higher degree, the signed harmonic-power prefix plus the
actual Euler coefficient of the original Gamma exponent is exactly the
signed original reconstructed zeta sample. The original sharp C17
reconstruction theorem supplies independent observation error for the
unsigned combined kernel. These are genuine source-sample identities;
the head's logarithmic derivative and canonical C42 remain separate.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaCombinedEulerKernel

open_ipra
open GaussianRationalHorner (qadd qmul)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr)
open GaussianRationalEulerCoefficients (euler parityPoint)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient)
open GaussianGammaExponentCoefficientPolynomial (polynomial)
open GaussianGammaHarmonicPowerPoints (point)
open GaussianGammaReciprocalDegreeCells (degree)
open RationalGaussianEmbedding (embed)
open GaussianRationalMetric (distanceBounded)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def fullPower (q m N : PTm n) : PTm n := qadd (point m N) (embed (RationalReciprocalPowerName.tailSample q m N))
ipra_subst fullPower

theorem full_power_is_original_reconstruction (q m N : PTm n) : Γ ⊢[PRAAx]
    fullPower q m N ≐ embed (RationalReciprocalPowerName.reconstructedSample q m N) :=
  (RationalGaussianEmbedding.embed_add _ _).eqSymm.eqTrans
    (RationalGaussianRealPart.embed_congr
      ((RationalAlgebra.add_congr (.eqRefl _) (RationalReciprocalPowerName.tail_sample_at q m N)).eqTrans
        (RationalReciprocalPowerName.reconstruction_sample_at q m N).eqSymm))

theorem linear_total (q N L : PTm n) : Γ ⊢[PRAAx]
    qadd (point one N)
      (exponentCoefficient (euler (polynomial q N L) (degree L)) (degree L) one) ≐
        embed (GammaEulerConstantName.gammaSample q zero) :=
  (qadd_congr (GaussianGammaHarmonicPowerPoints.first_is_original_harmonic N)
    (GaussianGammaExponentEulerCoefficients.euler_linear q N L)).eqTrans
      (GaussianRationalLinearProduct.add_sub_right _ _ (RationalGaussianEmbedding.embed_canonical _))

theorem high_total (q N L j : PTm n) (hj : Γ ⊢[PRAAx] le j L) : Γ ⊢[PRAAx]
    qadd (qmul (parityPoint (succ j)) (point (degree j) N))
      (exponentCoefficient (euler (polynomial q N L) (degree L)) (degree L) (degree j)) ≐
        qmul (parityPoint (succ j)) (embed (RationalReciprocalPowerName.reconstructedSample q (degree j) N)) :=
  (qadd_congr (.eqRefl _) (GaussianGammaExponentEulerCoefficients.euler_high q N L j hj)).eqTrans
    ((GaussianRationalCoefficientScaling.qmul_add _ _ _).eqSymm.eqTrans
      (qmul_congr (.eqRefl _) (full_power_is_original_reconstruction q (degree j) N)))

theorem full_power_zeta_error (p q m N : PTm n) (hm : Γ ⊢[PRAAx] le two m) : Γ ⊢[PRAAx]
    distanceBounded (embed (RationalReciprocalPowerName.zetaSample p m)) (fullPower q m N)
      (unit p+unit q) (unit p*unit q) :=
  GaussianRationalReciprocal.bound_congr
    (GaussianRationalSyntheticDivision.qsub_congr (.eqRefl _) (full_power_is_original_reconstruction q m N).eqSymm)
    (.eqRefl _) (.eqRefl _)
      (RationalGaussianNameEmbedding.distance_from_radius _ _ _ _
        (GaussianRationalHorner.positive_product _ _ (unit_positive p) (unit_positive q))
        (RationalReciprocalPowerName.reconstruction_error p q m N hm))

theorem original_Gamma_linear_Euler_kernel_is_sampled_gamma_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (qadd (point one (var 1))
      (exponentCoefficient (euler (polynomial (var 0) (var 1) (var 2)) (degree (var 2))) (degree (var 2)) one) ≐
        embed (GammaEulerConstantName.gammaSample (var 0) zero)) :=
  closeUniv 3 (linear_total _ _ _)

theorem original_Gamma_high_Euler_kernel_is_signed_reconstructed_zeta_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (le (var 3) (var 2) ⟶
        qadd (qmul (parityPoint (succ (var 3))) (point (degree (var 3)) (var 1)))
          (exponentCoefficient (euler (polynomial (var 0) (var 1) (var 2)) (degree (var 2)))
            (degree (var 2)) (degree (var 3))) ≐
          qmul (parityPoint (succ (var 3)))
            (embed (RationalReciprocalPowerName.reconstructedSample (var 0) (degree (var 3)) (var 1)))) :=
  closeUniv 4 (.impI (high_total _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaCombinedEulerKernel
