import IPRADerivations.Analysis.Gamma.EulerProducts.Factorials.GaussianGammaHalfRisingFactorial
import IPRADerivations.Analysis.Integration.Moments.GaussianEvenMomentIntegral

/-!
# Actual half-integer Gamma and Gaussian values relative to Gamma(1/2)

The source-derived V8 original Gamma identity and the checked original
half-integer rising product give the exact factorial coefficient of the
SAME Gamma(1/2) name. The original positive-half-line Gaussian sampler
consequently has that coefficient times Gamma(1/2) divided by its
original factor 2 alpha^(N+1/2). No sqrt(pi) base value is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaHalfIntegerValues

open_ipra
open GaussianGammaHalfIntegerDomain (argument radius half_source)
open ComplexLogarithmRemainder (oneCode)
open GaussianGammaHalfRisingFactorial (factorialValue)
open GaussianGammaReciprocalInverse (gammaF gammaData gamma_regular)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans cross_at)
open GaussianEuclideanDistanceName (pointCN)
open GaussianCoefficientNameBounds (unit)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def baseData : PTm n := gammaData oneCode one two two
def gammaInput (N : PTm n) : PTm n := gammaData (argument N) (radius N) two two
abbrev valueF : PR 2 := multiplyF constantF gammaF
def valueData (N : PTm n) : PTm n := multiplyData constantF gammaF (factorialValue N) baseData
abbrev gaussianValueF : PR 2 := multiplyF GaussianEulerSquareFactorInverse.inverseFactorF valueF
def gaussianValueData (N c d : PTm n) : PTm n := multiplyData GaussianEulerSquareFactorInverse.inverseFactorF valueF
  (GaussianEulerSquareFactorInverse.inverseFactorData (argument N) two c d) (valueData N)
ipra_subst baseData [GaussianGammaReciprocalInverse.gammaData, GaussianGammaReciprocalInverse.gammaHeight]
ipra_subst gammaInput [GaussianGammaReciprocalInverse.gammaData, GaussianGammaReciprocalInverse.gammaHeight]
ipra_subst valueData
ipra_subst gaussianValueData

theorem base_regular : Γ ⊢[PRAAx] pointCN gammaF (baseData : PTm n) :=
  gamma_regular oneCode one two one two (GaussianGammaDensityDomain.base_gamma_source oneCode one two two half_source)
theorem value_regular (N : PTm n) : Γ ⊢[PRAAx] pointCN valueF (valueData N) :=
  multiply_fast _ _ _ _ (constant_regular _) base_regular

theorem original_half_integer_value (N : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent gammaF valueF (gammaInput N) (valueData N) := by
  have old := GaussianGammaRisingFactorial.original_Gamma_rising_factorial (Γ := Γ) oneCode one two one two one two N
    (GaussianGammaDensityDomain.rising_input oneCode one two two N half_source)
  have replace := GaussianGammaAdjacentCutoff.multiply_cross (Γ := Γ) constantF constantF gammaF gammaF
    (GaussianGammaRepeatedShift.risingProduct oneCode two N) (factorialValue N) baseData baseData
    (constant_regular _) (constant_regular _) base_regular base_regular
    (GaussianGammaWeierstrassApproximant.constant_data_cross _ _ (GaussianGammaHalfRisingFactorial.original_half_rising_factorial N))
    (cross_refl _ _ base_regular)
  exact cross_trans _ _ _ _ _ _ old replace

theorem original_Gaussian_even_value (N c d : PTm n) (hc : Γ ⊢[PRAAx] le one c) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    crossEquivalent GaussianEvenMomentIntegral.nameF gaussianValueF (GaussianEvenMomentIntegral.data N c d) (gaussianValueData N c d) := by
  let I := GaussianEulerSquareFactorInverse.inverseFactorF
  let X := GaussianEulerSquareFactorInverse.inverseFactorData (argument N) two c d
  have hi := GaussianEulerSquareFactorInverse.inverse_regular (argument N) two c d (.andI (zero_lt_succ one) (.andI hc hd))
  have hg := GaussianEulerIntegralGammaIdentification.original_gamma_regular (Γ := Γ) _ _ _ _ (GaussianGammaHalfIntegerDomain.original_source N)
  have replace := GaussianGammaAdjacentCutoff.multiply_cross (Γ := Γ) I I gammaF valueF X X (gammaInput N) (valueData N)
    hi hi hg (value_regular N) (cross_refl _ _ hi) (original_half_integer_value N)
  exact cross_trans _ _ _ _ _ _ (GaussianEvenMomentIntegral.original_even_moment N c d hc hd) replace

theorem original_Gaussian_observations (p q N c d : PTm n) (hc : Γ ⊢[PRAAx] le one c) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    distanceBounded (ap2 GaussianEvenMomentIntegral.nameF p (GaussianEvenMomentIntegral.data N c d))
      (ap2 gaussianValueF q (gaussianValueData N c d)) (unit p+unit q) (unit p*unit q) :=
  cross_at _ _ _ _ p q (original_Gaussian_even_value N c d hc hd)

theorem actual_original_half_integer_Gamma_factorial_multiplier_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (crossEquivalent gammaF valueF (gammaInput (var 0)) (valueData (var 0))) := closeUniv 1 (original_half_integer_value _)
theorem actual_original_Gaussian_even_factorial_multiplier_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ le one (var 2) ⟶ crossEquivalent GaussianEvenMomentIntegral.nameF gaussianValueF
      (GaussianEvenMomentIntegral.data (var 0) (var 1) (var 2)) (gaussianValueData (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (original_Gaussian_even_value _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaHalfIntegerValues
