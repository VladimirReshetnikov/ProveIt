import IPRADerivations.Analysis.Gamma.HalfInteger.GaussianGammaHalfSqrtPi
import IPRADerivations.Analysis.Gamma.HalfInteger.GaussianGammaHalfIntegerValues

/-!
# Half-integer and positive-half Gaussian values with the explicit square root

The original Gamma values at N+1/2 use the exact factorial multiplier
(2N)!/(4^N N!) and the independently computed square root of π. The
positive-half even-moment evaluator uses the same value with its
original inverse quadratic scaling factor.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaHalfSqrtValues

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaHalfSqrtPi (original_half_is_sqrt_pi)
open GaussianGammaHalfIntegerValues (baseData base_regular gammaInput)
open GaussianGammaHalfRisingFactorial (factorialValue)
open GaussianGammaHalfIntegerDomain (argument)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans cross_refl)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianEuclideanDistanceName (pointCN)
open GaussianEulerSquareFactorInverse (inverseFactorF inverseFactorData)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev sqrtF : PR 2 := GaussianGammaHalfSqrtPi.nameF
abbrev valueF : PR 2 := multiplyF constantF sqrtF
def valueData (N x : PTm n) : PTm n := multiplyData constantF sqrtF (factorialValue N) x
abbrev momentF : PR 2 := multiplyF inverseFactorF valueF
def momentData (N c d x : PTm n) : PTm n := multiplyData inverseFactorF valueF
  (inverseFactorData (argument N) two c d) (valueData N x)

theorem sqrt_regular (x : PTm n) : Γ ⊢[PRAAx] pointCN sqrtF x := by
  let H := (baseData : PTm n)
  have eq : Γ ⊢[PRAAx] crossEquivalent gammaF sqrtF H x := original_half_is_sqrt_pi x
  exact cross_trans sqrtF gammaF sqrtF x H x (cross_symm gammaF sqrtF H x eq) eq

theorem sqrt_factorial_replacement (N x : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent GaussianGammaHalfIntegerValues.valueF valueF (GaussianGammaHalfIntegerValues.valueData N) (valueData N x) := by
  let c := factorialValue N
  have hC : Γ ⊢[PRAAx] pointCN constantF c := constant_regular c
  exact GaussianGammaAdjacentCutoff.multiply_cross constantF constantF gammaF sqrtF c c baseData x
    hC hC base_regular (sqrt_regular x) (cross_refl _ _ hC) (original_half_is_sqrt_pi x)

theorem original_half_integer_value (N x : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent gammaF valueF (gammaInput N) (valueData N x) :=
  cross_trans _ _ _ _ _ _
    (GaussianGammaHalfIntegerValues.original_half_integer_value N) (sqrt_factorial_replacement N x)

theorem original_even_moment (N c d x : PTm n)
    (hc : Γ ⊢[PRAAx] le one c) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    crossEquivalent GaussianEvenMomentIntegral.nameF momentF (GaussianEvenMomentIntegral.data N c d)
      (momentData N c d x) := by
  let D := inverseFactorData (argument N) two c d
  let A := GaussianGammaHalfIntegerValues.valueData N
  let B := valueData N x
  have factor : Γ ⊢[PRAAx] pointCN inverseFactorF D :=
    GaussianEulerSquareFactorInverse.inverse_regular _ _ _ _ (.andI (zero_lt_succ one) (.andI hc hd))
  have left : Γ ⊢[PRAAx] pointCN GaussianGammaHalfIntegerValues.valueF A :=
    GaussianGammaHalfIntegerValues.value_regular N
  have right : Γ ⊢[PRAAx] pointCN valueF B :=
    multiply_fast constantF sqrtF (factorialValue N) x (constant_regular _) (sqrt_regular x)
  have replace := GaussianGammaAdjacentCutoff.multiply_cross inverseFactorF inverseFactorF
    GaussianGammaHalfIntegerValues.valueF valueF D D A B factor factor left right
    (cross_refl _ _ factor) (sqrt_factorial_replacement N x)
  exact cross_trans _ _ _ _ _ _ (GaussianGammaHalfIntegerValues.original_Gaussian_even_value N c d hc hd) replace

theorem actual_original_Gamma_positive_half_integer_sqrt_Pi_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (crossEquivalent gammaF valueF (gammaInput (var 0)) (valueData (var 0) (var 1))) :=
  closeUniv 2 (original_half_integer_value _ _)

theorem actual_positive_half_Gaussian_even_sqrt_Pi_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (le one (var 1) ⟶ le one (var 2) ⟶
        crossEquivalent GaussianEvenMomentIntegral.nameF momentF
          (GaussianEvenMomentIntegral.data (var 0) (var 1) (var 2)) (momentData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (.impI (original_even_moment _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaHalfSqrtValues
