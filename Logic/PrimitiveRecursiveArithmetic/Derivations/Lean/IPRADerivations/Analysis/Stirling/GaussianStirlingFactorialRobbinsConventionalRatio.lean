import IPRADerivations.Analysis.Stirling.GaussianStirlingFactorialRobbinsDenominator

/-!
# The cleared conventional factorial Stirling ratio

The actual named ratio times n^n sqrt(2 Pi n) equals the exact
factorial times the original exp(n). Both exponential factors use
their original independent clocks.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingFactorialRobbinsConventionalRatio

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaFactorialValues (factorialValue)
open GaussianGammaFiniteApproximantName (exponential_input exponentialInputData)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameBounds (U)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (multiply_associative multiply_commutative multiply_one multiply_one_left
  negativeF negativeData negative_fast oneF one_fast)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianStirlingFactorialRobbinsDenominator (denominatorCoreF denominatorCoreData sqrt_factor_regular
  conventionalDenominatorF conventionalDenominatorData conventional_denominator_inverse)
open GaussianStirlingFactorialRobbinsQuotient (factorialRatioF factorialRatioData factorialReciprocalF factorialReciprocalData)
open GaussianStirlingLogDuplication (exponential_regular)
open GaussianStirlingMultiplicative (reciprocalF decayF decayData)
open GaussianStirlingMultiplicativeAlgebra (normalizationF normalizationData normalization_regular)
open GaussianStirlingNames (source)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "ed" => exponentialInputData

abbrev naturalExpF : PR 2 := E constantF
def naturalExpData (i : PTm n) : PTm n := ed constantF (fraction i one)
abbrev numeratorF : PR 2 := multiplyF constantF naturalExpF
def numeratorData (i : PTm n) : PTm n := multiplyData constantF naturalExpF (factorialValue i) (naturalExpData i)

private theorem decay_times_exp (i y : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF decayF naturalExpF) oneF
      (multiplyData decayF naturalExpF (decayData i one) (naturalExpData i)) y := by
  let c := fraction i one
  let R := U constantF c
  let V := U (negativeF constantF) (negativeData c)
  let X := naturalExpData i
  let Y := decayData i one
  let Z := GaussianRadiusExponentialName.data R (negativeData c)
  have h := constant_regular (Γ := Γ) c
  have qi := exponential_input constantF c h
  have neg := negative_fast constantF c h
  have vi := exponential_input (negativeF constantF) (negativeData c) neg
  have ri := GaussianExponentialInverse.negative_input constantF R c qi
  have xp := exponential_regular _ _ h
  have yp := exponential_regular _ _ neg
  have zp := GaussianRadiusExponentialName.name_regular _ _ _ ri
  have move := GaussianExponentialRadiusIndependence.same_input_cross (negativeF constantF) V R _ vi ri
  have cross := multiply_cross naturalExpF naturalExpF decayF decayF X X Y Z xp xp yp zp (cross_refl _ _ xp) move
  exact cross_trans _ _ _ _ _ _ (multiply_commutative _ _ _ _ yp xp)
    (cross_trans _ _ _ _ _ _ cross
      (cross_trans _ _ _ _ _ _ (GaussianExponentialInverse.exponential_inverse constantF R c qi)
        (GaussianBoundedInverseApartness.ones_equivalent c y)))

private theorem reciprocal_regular (i x : PTm n) (hi : Γ ⊢[PRAAx] le one i) :
    Γ ⊢[PRAAx] pointCN factorialReciprocalF (factorialReciprocalData i x) :=
  multiply_fast _ _ _ _ (constant_regular _)
    (exponential_regular _ _ (negative_fast normalizationF (normalizationData i one x)
      (normalization_regular i one x (.andI hi (le_refl one)))))

set_option maxHeartbeats 850000 in
theorem reciprocal_times_core (i x : PTm n) (hi : Γ ⊢[PRAAx] le one i) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF factorialReciprocalF denominatorCoreF) naturalExpF
      (multiplyData factorialReciprocalF denominatorCoreF (factorialReciprocalData i x) (denominatorCoreData i x))
      (naturalExpData i) := by
  let F := factorialReciprocalF
  let G := denominatorCoreF
  let D := decayF
  let P := naturalExpF
  let f := factorialReciprocalData i x
  let g := denominatorCoreData i x
  let d := decayData i one
  let p := naturalExpData i
  let M := multiplyF F G
  let m := multiplyData F G f g
  let B := multiplyF D P
  let b := multiplyData D P d p
  let C := conventionalDenominatorF
  let c := conventionalDenominatorData i x
  have fr := reciprocal_regular i x hi
  have gr : Γ ⊢[PRAAx] pointCN G g := multiply_fast _ _ _ _ (constant_regular _) (sqrt_factor_regular i x hi)
  have nr := constant_regular (Γ := Γ) (fraction i one)
  have dr : Γ ⊢[PRAAx] pointCN D d := exponential_regular _ _ (negative_fast constantF _ nr)
  have pr : Γ ⊢[PRAAx] pointCN P p := exponential_regular _ _ nr
  have mr : Γ ⊢[PRAAx] pointCN M m := multiply_fast _ _ _ _ fr gr
  have br : Γ ⊢[PRAAx] pointCN B b := multiply_fast _ _ _ _ dr pr
  have cr : Γ ⊢[PRAAx] pointCN C c := multiply_fast _ _ _ _ gr dr
  have reduce := multiply_cross M M B oneF m m b m mr mr br (one_fast m)
    (cross_refl _ _ mr) (decay_times_exp i m)
  have start := cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (multiply_one M m mr)) (cross_symm _ _ _ _ reduce)
  have assoc₁ := multiply_associative F G B f g b fr gr br
  have assoc₂ := cross_symm _ _ _ _ (multiply_associative G D P g d p gr dr pr)
  have move := multiply_cross F F (multiplyF G B) (multiplyF C P) f f (multiplyData G B g b) (multiplyData C P c p)
    fr fr (multiply_fast _ _ _ _ gr br) (multiply_fast _ _ _ _ cr pr) (cross_refl _ _ fr) assoc₂
  have assoc₃ := cross_symm _ _ _ _ (multiply_associative F C P f c p fr cr pr)
  have one := cross_trans _ _ _ _ _ _ (multiply_commutative _ _ _ _ fr cr)
    (cross_trans _ _ _ _ _ _ (conventional_denominator_inverse i x hi)
      (GaussianBoundedInverseApartness.ones_equivalent (normalizationData i one x) p))
  have finish := multiply_cross (multiplyF F C) oneF P P (multiplyData F C f c) p p p
    (multiply_fast _ _ _ _ fr cr) (one_fast p) pr pr one (cross_refl _ _ pr)
  exact cross_trans _ _ _ _ _ _ start (cross_trans _ _ _ _ _ _ assoc₁ (cross_trans _ _ _ _ _ _ move
    (cross_trans _ _ _ _ _ _ assoc₃ (cross_trans _ _ _ _ _ _ finish (multiply_one_left P p pr)))))

theorem cleared_conventional_ratio (i x : PTm n) (hi : Γ ⊢[PRAAx] le one i) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF factorialRatioF denominatorCoreF) numeratorF
      (multiplyData factorialRatioF denominatorCoreF (factorialRatioData i x) (denominatorCoreData i x))
      (numeratorData i) := by
  let F := factorialReciprocalF
  let G := denominatorCoreF
  let u := factorialValue i
  let f := factorialReciprocalData i x
  let g := denominatorCoreData i x
  let p := naturalExpData i
  have fr := reciprocal_regular i x hi
  have gr : Γ ⊢[PRAAx] pointCN G g := multiply_fast _ _ _ _ (constant_regular _) (sqrt_factor_regular i x hi)
  have ur := constant_regular (Γ := Γ) u
  have pr := exponential_regular constantF (fraction i one) (constant_regular (Γ := Γ) _)
  have group := multiply_associative constantF F G u f g ur fr gr
  have finish := multiply_cross constantF constantF (multiplyF F G) naturalExpF u u (multiplyData F G f g) p
    ur ur (multiply_fast _ _ _ _ fr gr) pr (cross_refl _ _ ur) (reciprocal_times_core i x hi)
  exact cross_trans _ _ _ _ _ _ group finish

theorem actual_conventional_factorial_ratio_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 0) ⟶ crossEquivalent (multiplyF factorialRatioF denominatorCoreF) numeratorF
      (multiplyData factorialRatioF denominatorCoreF (factorialRatioData (var 0) (var 1))
        (denominatorCoreData (var 0) (var 1))) (numeratorData (var 0))) :=
  closeUniv 2 (.impI (cleared_conventional_ratio _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianStirlingFactorialRobbinsConventionalRatio
