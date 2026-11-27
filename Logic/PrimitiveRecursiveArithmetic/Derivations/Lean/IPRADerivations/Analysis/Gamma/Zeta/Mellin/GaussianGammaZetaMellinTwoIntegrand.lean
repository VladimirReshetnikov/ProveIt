import IPRADerivations.Analysis.Gamma.Zeta.Mellin.Compact.GaussianGammaZetaMellinIntegrand
import IPRADerivations.Analysis.Euler.PositiveAxis.Moments.GaussianEulerNaturalPower
import IPRADerivations.Analysis.Euler.PositiveAxis.PositiveScaling.GaussianEulerPositiveScalingConstant
import IPRADerivations.Analysis.Gamma.FunctionalEquations.ReciprocalGamma.GaussianGammaAdjacentCutoff
import IPRADerivations.Analysis.Gamma.EulerProducts.Factorials.GaussianGammaFactorialValues
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianPowers.GaussianRationalPowerAlgebra

/-!
# The literal Mellin integrand at two

At the specialized parameter, the original Euler log-power is the
rational input itself. The other factor remains the original reciprocal
of the unscaled exponential minus one.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinTwoIntegrand

open_ipra
open ComplexLogarithmRemainder (oneCode)
open GaussianGammaEulerHeadShift (shifted)
open GaussianEulerIntegrandName (powerF powerData coefficient)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaZetaMellinIntegrand (nameF data reciprocalF reciprocalData denominatorF denominatorData)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_refl)
open GaussianPositiveRationalLogarithm (fraction)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def integrandF : PR 2 := multiplyF constantF reciprocalF
def integrandData (a b : PTm n) : PTm n := multiplyData constantF reciprocalF (fraction a b) (reciprocalData a b)

private theorem time_chart (a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] GaussianHarmonicIntegerExponential.source a b b a :=
  .andI hb (.andI (.andI ha hb) (.andI
    (le_congr (one_mul b) (mul_comm a b) (mul_le_mul_right b ha))
    (le_congr (one_mul a) (mul_comm b a) (mul_le_mul_right a hb))))

theorem original_power_at_two (a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] crossEquivalent powerF constantF (powerData (shifted oneCode one) one a b) (fraction a b) := by
  have exponent : Γ ⊢[PRAAx] coefficient (shifted oneCode one) one ≐
      GaussianRationalNaturalScale.naturalPoint one :=
    (GaussianEulerPositiveScalingConstant.shifted_coefficient oneCode one (le_refl one)).eqTrans
      GaussianGammaFactorialValues.natural_one.eqSymm
  have reduction := GaussianEulerNaturalPower.original_power (shifted oneCode one) one one a b b a
    (le_refl one) (time_chart a b ha hb) exponent
  have power_one := GaussianRationalPowerAlgebra.power_one (fraction a b)
    (GaussianRationalHorner.ofGaussian_canonical _ _ hb)
  exact cross_trans _ _ _ _ _ _ reduction (GaussianGammaWeierstrassApproximant.constant_data_cross _ _ power_one)

theorem original_integrand_at_two (a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] crossEquivalent nameF integrandF (data (shifted oneCode one) one a b) (integrandData a b) := by
  have reciprocal_regular := GaussianNameReciprocal.name_fast denominatorF b (denominatorData a b)
    (GaussianGammaZetaMellinIntegrand.denominator_regular a b)
    (GaussianGammaZetaMellinIntegrand.denominator_apart a b ha hb)
  exact GaussianGammaAdjacentCutoff.multiply_cross _ _ _ _ _ _ _ _
    (GaussianEulerIntegrandName.power_regular _ _ a b (.andI (le_refl one) (.andI ha hb)))
    (constant_regular _) reciprocal_regular reciprocal_regular
    (original_power_at_two a b ha hb) (cross_refl _ _ reciprocal_regular)

theorem actual_original_Mellin_integrand_at_two_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 0) ⋏ le one (var 1) ⟶ crossEquivalent nameF integrandF
      (data (shifted oneCode one) one (var 0) (var 1)) (integrandData (var 0) (var 1))) :=
  closeUniv 2 (.impI (original_integrand_at_two _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinTwoIntegrand
