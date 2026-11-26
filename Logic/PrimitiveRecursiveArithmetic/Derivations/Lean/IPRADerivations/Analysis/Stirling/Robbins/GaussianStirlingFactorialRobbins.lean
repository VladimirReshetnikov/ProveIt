import IPRADerivations.Analysis.Stirling.Bounds.GaussianStirlingMultiplicativeBoundsCaps
import IPRADerivations.Analysis.Stirling.Robbins.GaussianStirlingFactorialRobbinsQuotient

/-!
# The original factorial ratio and the quantitative Stirling modulus

The sharp signed logarithmic bounds imply strict multiplicative
bounds on the same native factorial quotient at every positive
integer. The cutoff 2^p works for independent requested precision p.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingFactorialRobbins

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEulerPowerChartTimeOrder (order_trans)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (positive_product)
open GaussianStirlingFactorialRobbinsQuotient (factorialRatioF factorialRatioData factorial_ratio)
open GaussianStirlingMultiplicative (quotientF quotientData expRemainderF expRemainderData)
open GaussianStirlingMultiplicativeAlgebra (remainderF remainderData)
open GaussianStirlingMultiplicativeBounds (conventionalUpper upperDen)
open GaussianStirlingMultiplicativeBoundsCaps (interval integer_interval cap_denominator conventional_le_factor)
open GaussianStirlingNames (source)
open GaussianStirlingRationalTelescopers (small_numeral_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem const_refl (c : PTm n) : Γ ⊢[PRAAx] crossEquivalent constantF constantF c c :=
  cross_refl _ _ (constant_regular _)

theorem factorial_interval (i x : PTm n) (hi : Γ ⊢[PRAAx] le one i) :
    Γ ⊢[PRAAx] interval factorialRatioF i one (factorialRatioData i x) := by
  let q := quotientData i one x
  let y := factorialRatioData i x
  let a : PTm n := fraction one one
  let b := conventionalUpper i one
  have e := factorial_ratio i x hi
  have e' := cross_symm _ _ _ _ e
  have k := integer_interval i x hi
  refine .andI (.andI ?_ (.impI ?_)) (.andI ?_ (.impI ?_))
  · exact GaussianNamedRealOrderTransport.transport constantF constantF quotientF factorialRatioF a a q y
      (const_refl a) e k.andE₁.andE₁
  · exact k.andE₁.andE₂.wk.impE (GaussianNamedRealOrderTransport.transport quotientF factorialRatioF constantF constantF q y a a
      e.wk (const_refl a) Prf.hyp0)
  · exact GaussianNamedRealOrderTransport.transport factorialRatioF quotientF constantF constantF y q b b
      e' (const_refl b) k.andE₂.andE₁
  · exact k.andE₂.andE₂.wk.impE (GaussianNamedRealOrderTransport.transport constantF constantF factorialRatioF quotientF b b y q
      (const_refl b) e'.wk Prf.hyp0)

def dyadicUpper (p : PTm n) : PTm n := fraction (unit p+one) (unit p)

def errorAt (p i x : PTm n) : Fm PTm n :=
  realOrder factorialRatioF constantF (factorialRatioData i x) (dyadicUpper p) ⋏
    neg (realOrder constantF factorialRatioF (dyadicUpper p) (factorialRatioData i x))

theorem dyadic_modulus (p i x : PTm n) (hi : Γ ⊢[PRAAx] le (unit p) i) :
    Γ ⊢[PRAAx] errorAt p i x := by
  have hp := unit_positive (Γ := Γ) p
  have h := le_trans hp hi
  have hs : Γ ⊢[PRAAx] source i one := .andI h (le_refl one)
  have step : Γ ⊢[PRAAx] le i (num 6*i) :=
    le_congr (one_mul i) (.eqRefl _) (mul_le_mul_right i (small_numeral_positive 5))
  have room := le_trans hi (le_trans step (cap_denominator i one hs h).andE₁)
  have b := conventional_le_factor i one (unit p) hs h hp room
  have k := factorial_interval i x h
  refine .andI (order_trans _ _ _ _ _ _ k.andE₂.andE₁ b) (.impI ?_)
  exact k.andE₂.andE₂.wk.impE (order_trans _ _ _ _ _ _ b.wk Prf.hyp0)

theorem actual_factorial_Robbins_multiplicative_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 0) ⟶
      (GaussianStirlingRobbins.bounds remainderF (var 0) one (remainderData (var 0) one (var 1)) ⋏
        (crossEquivalent expRemainderF factorialRatioF (expRemainderData (var 0) one (var 1))
          (factorialRatioData (var 0) (var 1)) ⋏
          interval factorialRatioF (var 0) one (factorialRatioData (var 0) (var 1))))) :=
  closeUniv 2 (.impI (.andI (GaussianStirlingRobbins.integer_bounds _ _ Prf.hyp0)
    (.andI (GaussianStirlingFactorialRobbinsQuotient.exp_remainder_is_factorial_ratio _ _ Prf.hyp0)
      (factorial_interval _ _ Prf.hyp0))))

theorem actual_factorial_Stirling_dyadic_modulus_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (unit (var 0)) (var 1) ⟶ errorAt (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (dyadic_modulus _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianStirlingFactorialRobbins
