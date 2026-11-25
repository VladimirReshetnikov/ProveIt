import IPRADerivations.Analysis.GaussianStirlingFactorialRobbinsPower

/-!
# The conventional factorial Stirling denominator

The exact normalization already certified for the factorial quotient
is the product of the primitive recursive power n^n, the positive
square root of 2 Pi n, and exp(-n).
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingFactorialRobbinsDenominator

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaFiniteApproximantName (exponential_input exponentialInputData)
open GaussianGaussTriplicationPi (doubledPiF doubledPiData doubled_pi_regular)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameBounds (U)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (multiply_associative multiply_commutative negative_fast negativeF oneF)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianStirlingFactorialRobbinsPower (naturalPower halfLogData half_log_regular half_log_real
  sqrtIntegerF sqrtIntegerData sqrt_integer_regular sqrt_integer_square scaled_power_split)
open GaussianStirlingFactorialRobbinsQuotient (factorialDenominatorF factorialDenominatorData
  factorialReciprocalF factorialReciprocalData factorial_denominator_inverse)
open GaussianStirlingLogDuplication (exponential_sum exponential_regular)
open GaussianStirlingMultiplicative (sqrtF sqrtData sqrt_regular sqrt_square powerF powerData firstFactorsF firstFactorsData
  denominatorF denominatorData decayF decayData)
open GaussianStirlingMultiplicativeAlgebra (normalizationData normalizationF normalization_regular)
open GaussianStirlingNames (source productF product_regular)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "ed" => exponentialInputData
local notation "CF" => GaussianStirlingConstant.nameF
local notation "CD" => GaussianStirlingConstant.nameData

abbrev sqrtExponentF : PR 2 := addF CF productF
def sqrtExponentData (i x : PTm n) : PTm n := addData (CD x) (halfLogData i)
abbrev sqrtFactorF : PR 2 := E sqrtExponentF
def sqrtFactorData (i x : PTm n) : PTm n := ed sqrtExponentF (sqrtExponentData i x)
abbrev denominatorCoreF : PR 2 := multiplyF constantF sqrtFactorF
def denominatorCoreData (i x : PTm n) : PTm n := multiplyData constantF sqrtFactorF (naturalPower i) (sqrtFactorData i x)
abbrev conventionalDenominatorF : PR 2 := multiplyF denominatorCoreF decayF
def conventionalDenominatorData (i x : PTm n) : PTm n :=
  multiplyData denominatorCoreF decayF (denominatorCoreData i x) (decayData i one)

theorem sqrt_exponent_regular (i x : PTm n) (hi : Γ ⊢[PRAAx] le one i) :
    Γ ⊢[PRAAx] pointCN sqrtExponentF (sqrtExponentData i x) :=
  add_fast _ _ _ _ (GaussianStirlingConstant.name_regular x) (half_log_regular i hi)

theorem sqrt_exponent_real (i x : PTm n) :
    Γ ⊢[PRAAx] GaussianSignedNameExponentialOrder.realSamples sqrtExponentF (sqrtExponentData i x) :=
  GaussianStirlingNames.add_real _ _ _ _ (GaussianStirlingConstant.name_real x) (half_log_real i)

theorem sqrt_factor_regular (i x : PTm n) (hi : Γ ⊢[PRAAx] le one i) :
    Γ ⊢[PRAAx] pointCN sqrtFactorF (sqrtFactorData i x) :=
  exponential_regular _ _ (sqrt_exponent_regular i x hi)

theorem sqrt_factor_real (i x : PTm n) :
    Γ ⊢[PRAAx] GaussianSignedNameExponentialOrder.realSamples sqrtFactorF (sqrtFactorData i x) :=
  GaussianEulerVerticalRealSamples.original_exponential_real_samples _ _ _ (sqrt_exponent_real i x)

theorem sqrt_factor_positive (p i x : PTm n) (hi : Γ ⊢[PRAAx] le one i) :
    Γ ⊢[PRAAx] RationalValueBounds.upper
      (GaussianEuclideanDistanceName.fraction one (pw (num 3) (U sqrtExponentF (sqrtExponentData i x))))
      (fstT (ap2 sqrtFactorF p (sqrtFactorData i x))) one (unit p) :=
  GaussianRealExponentialCompactLower.original_observation_lower sqrtExponentF p _ _
    (exponential_input _ _ (sqrt_exponent_regular i x hi)) (sqrt_exponent_real i x)

theorem sqrt_factors (i x : PTm n) (hi : Γ ⊢[PRAAx] le one i) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF sqrtF sqrtIntegerF) sqrtFactorF
      (multiplyData sqrtF sqrtIntegerF (sqrtData x) (sqrtIntegerData i)) (sqrtFactorData i x) :=
  exponential_sum CF productF (CD x) (halfLogData i)
    (GaussianStirlingConstant.name_regular x) (half_log_regular i hi)

set_option maxHeartbeats 550000 in
theorem sqrt_factor_square (i x : PTm n) (hi : Γ ⊢[PRAAx] le one i) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF sqrtFactorF sqrtFactorF) (multiplyF doubledPiF constantF)
      (multiplyData sqrtFactorF sqrtFactorF (sqrtFactorData i x) (sqrtFactorData i x))
      (multiplyData doubledPiF constantF (doubledPiData x) (fraction i one)) := by
  let S := multiplyF sqrtF sqrtIntegerF
  let X := sqrtData x
  let Y := sqrtIntegerData i
  let z := multiplyData sqrtF sqrtIntegerF X Y
  let Z := sqrtFactorData i x
  have hX := sqrt_regular (Γ := Γ) x
  have hY := sqrt_integer_regular i hi
  have hS : Γ ⊢[PRAAx] pointCN S z := multiply_fast _ _ _ _ hX hY
  have hZ := sqrt_factor_regular i x hi
  have move := cross_symm _ _ _ _ (sqrt_factors i x hi)
  have first := multiply_cross sqrtFactorF S sqrtFactorF S Z z Z z hZ hS hZ hS move move
  have group := GaussianGammaReciprocalInverse.named_product_exchange sqrtF sqrtIntegerF sqrtF sqrtIntegerF
    X Y X Y hX hY hX hY
  have last := multiply_cross (multiplyF sqrtF sqrtF) doubledPiF (multiplyF sqrtIntegerF sqrtIntegerF) constantF
    (multiplyData sqrtF sqrtF X X) (doubledPiData x) (multiplyData sqrtIntegerF sqrtIntegerF Y Y) (fraction i one)
    (multiply_fast _ _ _ _ hX hX) (doubled_pi_regular x) (multiply_fast _ _ _ _ hY hY) (constant_regular _)
    (sqrt_square x) (sqrt_integer_square i hi)
  exact cross_trans _ _ _ _ _ _ first (cross_trans _ _ _ _ _ _ group last)

private theorem swap_front (f g h : PR 2) (x y z : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) (hh : Γ ⊢[PRAAx] pointCN h z) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF f (multiplyF g h)) (multiplyF g (multiplyF f h))
      (multiplyData f (multiplyF g h) x (multiplyData g h y z))
      (multiplyData g (multiplyF f h) y (multiplyData f h x z)) := by
  have m := multiply_cross (multiplyF f g) (multiplyF g f) h h
    (multiplyData f g x y) (multiplyData g f y x) z z (multiply_fast _ _ _ _ hf hg) (multiply_fast _ _ _ _ hg hf)
    hh hh (multiply_commutative _ _ _ _ hf hg) (cross_refl _ _ hh)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (multiply_associative f g h x y z hf hg hh))
    (cross_trans _ _ _ _ _ _ m (multiply_associative g f h y x z hg hf hh))

set_option maxHeartbeats 700000 in
theorem conventional_first_factors (i x : PTm n) (hi : Γ ⊢[PRAAx] le one i) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF constantF firstFactorsF) denominatorCoreF
      (multiplyData constantF firstFactorsF (fraction i one) (firstFactorsData i one x))
      (denominatorCoreData i x) := by
  let N := fraction i one
  let A := sqrtData x
  let B := powerData i one
  let C := sqrtIntegerData i
  let D := naturalPower i
  let S := multiplyF constantF powerF
  let T := multiplyF sqrtIntegerF constantF
  let S0 := multiplyData constantF powerF N B
  let T0 := multiplyData sqrtIntegerF constantF C D
  let J := multiplyF sqrtF sqrtIntegerF
  let K := multiplyData sqrtF sqrtIntegerF A C
  have hs : Γ ⊢[PRAAx] source i one := .andI hi (le_refl one)
  have hn := constant_regular (Γ := Γ) N
  have ha := sqrt_regular (Γ := Γ) x
  have hb := exponential_regular _ _ (product_regular i one hs)
  have hc := sqrt_integer_regular i hi
  have hd := constant_regular (Γ := Γ) D
  have hr := sqrt_factor_regular i x hi
  have first := swap_front constantF sqrtF powerF N A B hn ha hb
  have next := multiply_cross sqrtF sqrtF S T A A S0 T0 ha ha
    (multiply_fast _ _ _ _ hn hb) (multiply_fast _ _ _ _ hc hd) (cross_refl _ _ ha) (scaled_power_split i hi)
  have assoc := cross_symm _ _ _ _ (multiply_associative sqrtF sqrtIntegerF constantF A C D ha hc hd)
  have last := multiply_cross J sqrtFactorF constantF constantF K (sqrtFactorData i x) D D
    (multiply_fast _ _ _ _ ha hc) hr hd hd (sqrt_factors i x hi) (cross_refl _ _ hd)
  exact cross_trans _ _ _ _ _ _ first
    (cross_trans _ _ _ _ _ _ next (cross_trans _ _ _ _ _ _ assoc
      (cross_trans _ _ _ _ _ _ last (multiply_commutative _ _ _ _ hr hd))))

theorem conventional_denominator (i x : PTm n) (hi : Γ ⊢[PRAAx] le one i) :
    Γ ⊢[PRAAx] crossEquivalent factorialDenominatorF conventionalDenominatorF
      (factorialDenominatorData i x) (conventionalDenominatorData i x) := by
  let N := fraction i one
  let d := decayData i one
  let F := multiplyF constantF firstFactorsF
  let P := firstFactorsData i one x
  let v := multiplyData constantF firstFactorsF N P
  have hs : Γ ⊢[PRAAx] source i one := .andI hi (le_refl one)
  have hN := constant_regular (Γ := Γ) N
  have hf : Γ ⊢[PRAAx] pointCN firstFactorsF P :=
    multiply_fast _ _ _ _ (sqrt_regular x) (exponential_regular _ _ (product_regular i one hs))
  have hD : Γ ⊢[PRAAx] pointCN decayF d := exponential_regular _ _ (negative_fast constantF N hN)
  have assoc := cross_symm _ _ _ _ (multiply_associative constantF firstFactorsF decayF N P d hN hf hD)
  have final := multiply_cross F denominatorCoreF decayF decayF v (denominatorCoreData i x) d d
    (multiply_fast _ _ _ _ hN hf) (multiply_fast _ _ _ _ (constant_regular _) (sqrt_factor_regular i x hi))
    hD hD (conventional_first_factors i x hi) (cross_refl _ _ hD)
  exact cross_trans _ _ _ _ _ _ assoc final

theorem conventional_denominator_inverse (i x : PTm n) (hi : Γ ⊢[PRAAx] le one i) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF conventionalDenominatorF factorialReciprocalF) oneF
      (multiplyData conventionalDenominatorF factorialReciprocalF
        (conventionalDenominatorData i x) (factorialReciprocalData i x)) (normalizationData i one x) := by
  let f := factorialReciprocalData i x
  have hs : Γ ⊢[PRAAx] source i one := .andI hi (le_refl one)
  have hN := constant_regular (Γ := Γ) (fraction i one)
  have hf : Γ ⊢[PRAAx] pointCN firstFactorsF (firstFactorsData i one x) :=
    multiply_fast _ _ _ _ (sqrt_regular x) (exponential_regular _ _ (product_regular i one hs))
  have hD := exponential_regular _ _ (negative_fast constantF _ hN)
  have hF := multiply_fast constantF denominatorF _ _ hN (multiply_fast _ _ _ _ hf hD)
  have hC : Γ ⊢[PRAAx] pointCN conventionalDenominatorF (conventionalDenominatorData i x) :=
    multiply_fast denominatorCoreF decayF _ _
    (multiply_fast _ _ _ _ (constant_regular _) (sqrt_factor_regular i x hi)) hD
  have hR : Γ ⊢[PRAAx] pointCN factorialReciprocalF f := multiply_fast _ _ _ _ (constant_regular _)
    (exponential_regular _ _ (negative_fast normalizationF _ (normalization_regular i one x hs)))
  have e := multiply_cross conventionalDenominatorF factorialDenominatorF factorialReciprocalF factorialReciprocalF
    (conventionalDenominatorData i x) (factorialDenominatorData i x) f f hC hF hR hR
    (cross_symm _ _ _ _ (conventional_denominator i x hi)) (cross_refl _ _ hR)
  exact cross_trans _ _ _ _ _ _ e (factorial_denominator_inverse i x hi)

theorem actual_conventional_factorial_denominator_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 0) ⟶ crossEquivalent factorialDenominatorF conventionalDenominatorF
      (factorialDenominatorData (var 0) (var 1)) (conventionalDenominatorData (var 0) (var 1))) :=
  closeUniv 2 (.impI (conventional_denominator _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianStirlingFactorialRobbinsDenominator
