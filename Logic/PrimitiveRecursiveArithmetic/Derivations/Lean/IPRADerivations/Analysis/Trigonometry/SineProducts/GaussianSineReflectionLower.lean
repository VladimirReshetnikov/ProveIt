import IPRADerivations.Analysis.Trigonometry.SineProducts.GaussianSineProductReflectionLower
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Reflection.GaussianGammaReflectionSineTransfer
import IPRADerivations.Analysis.Trigonometry.Arctangent.DivisionAngles.GaussianArctangentDivisionAngleGaps

/-!
# Transfer of the explicit R3 lower bound to the original sine

The original quadrature samples of π are at least two. The product
identity at the input transfers the finite R3 constant to actual
sine observations at the stated dyadic reserve.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianSineReflectionLower

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianSineProductReflectionLower (numerator denominator source named_product_lower numerator_positive denominator_positive)
open GaussianGammaReflectionSineTransfer (productIdentification sineAtPiF sineAtPiData sine_as_product)
open GaussianGammaReflectionProduct (productLinearF productLinearData)
open GaussianGammaHalfPiName (meshAt clearing observation)
open GaussianArctangentDivisionAngleGaps (quarter_lower)
open GaussianArctangentDivisionAngles (quarterNumerator quarterDenominator)
open GaussianRationalLowerBounds (lower lower_congr lower_from_representation lower_to_cleared product_lower)
open GaussianRationalMetric (distanceBounded bounded_difference_iff)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianRationalHorner (positive_product ofGaussian_represents qmul qmul_canonical)
open GaussianRationalSyntheticDivision (rescale_to)
open GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive)
open GaussianNameEquivalence (cross_at)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus multiply_at)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianBalancedRadiusArithmetic (unit_monotone)
open ComplexLogarithmRemainder (normSq scale oneCode normSq_scale normSq_one)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "P" => GaussianGammaHalfPiName.nameF

theorem original_pi_sample_lower (p x : PTm n) : Γ ⊢[PRAAx] lower (ap2 P p x) two one := by
  let C := num 4*BaselQuadrature.Q (meshAt p) (clearing p)
  let D := quarterDenominator p
  have hD := GaussianRationalPolynomialExponential.factorial_positive (Γ := Γ) (clearing p)
  have comp : Γ ⊢[PRAAx] le (two*D) C := by
    apply le_congr (by ipra_ring) ?_ (mul_le_mul_right two (quarter_lower (Γ := Γ) p))
    unfold C quarterNumerator GaussianArctangentExponentialPrefix.total BaselQuadrature.Q
    ipra_ring
  have norm : Γ ⊢[PRAAx] normSq (scale C oneCode) ≐ C*C :=
    (normSq_scale C oneCode).eqTrans ((congrMul (.eqRefl _) normSq_one).eqTrans (by ipra_ring))
  have point : Γ ⊢[PRAAx] lower (observation p) two one := by
    apply lower_from_representation _ (scale C oneCode) D _ _ hD (le_refl one) (ofGaussian_represents _ _ hD)
    exact le_congr (by ipra_ring) (norm.eqSymm.eqTrans (by ipra_ring)) (le_mul_mono comp comp)
  exact lower_congr (GaussianGammaHalfPiName.sample_at p x).eqSymm (.eqRefl _) (.eqRefl _) point

theorem lower_after_half_error (q r A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] lower q (two*A) B) (hd : Γ ⊢[PRAAx] distanceBounded q r A B) :
    Γ ⊢[PRAAx] lower r A B := by
  let E := rawDen q*rawDen r
  let Q := scale (rawDen r) (rawGaussian q)
  let T := scale (rawDen q) (rawGaussian r)
  have hE : Γ ⊢[PRAAx] le one E := positive_product _ _ (raw_den_positive q) (raw_den_positive r)
  have hq : Γ ⊢[PRAAx] GaussianRationalHorner.represents q Q E :=
    rescale_to _ _ _ _ _ (raw_represents q) (.eqRefl _)
  have ht : Γ ⊢[PRAAx] GaussianRationalHorner.represents r T E :=
    rescale_to _ _ _ _ _ (raw_represents r) (by unfold E; ipra_ring)
  have ref := lower_to_cleared q Q E (two*A) B hE hB hq h
  have differ := (bounded_difference_iff q r Q T E A B hE hB hq ht).iffMp hd
  have native := GaussianGeneralCoefficientNames.native_apart_tail Q T (A*E) B
    (le_congr (by ipra_ring) (.eqRefl _) ref) (le_congr (.eqRefl _) (by ipra_ring) differ)
  exact lower_from_representation r T E A B hE hB ht (le_congr (by ipra_ring) (.eqRefl _) native)

def threshold (d R L : PTm n) : PTm n := L+two*denominator d R L

theorem scaled_sample_lower (z R B a d L p x : PTm n) (hs : Γ ⊢[PRAAx] source z R B a d L)
    (hL : Γ ⊢[PRAAx] le L (unit p)) :
    Γ ⊢[PRAAx] lower (ap2 (multiplyF P productLinearF) p (multiplyData P productLinearF x (productLinearData z R B)))
      (two*numerator a L) (denominator d R L) := by
  let y := productLinearData z R B
  let k := GaussianFastValueCut.exponent (multiplyModulus P productLinearF x y) p
  have hk : Γ ⊢[PRAAx] le p k := le_add_right _ _
  have hD := denominator_positive d R L (le_trans hs.andE₁.andE₂.andE₁ hs.andE₁.andE₂.andE₂)
  have e : Γ ⊢[PRAAx] ap2 (multiplyF P productLinearF) p (multiplyData P productLinearF x y) ≐
      qmul (ap2 P k x) (ap2 productLinearF k y) :=
    (multiply_at P productLinearF x y p).eqTrans (GaussianExponentialReference.recode_fixed _ (qmul_canonical _ _))
  exact lower_congr e.eqSymm (.eqRefl _) (one_mul _)
    (product_lower _ _ _ _ _ _ (le_refl one) hD (original_pi_sample_lower k x)
      (named_product_lower z R B a d L k hs (le_trans hL (unit_monotone p k hk))))

theorem actual_sine_lower (z R B a d L p x : PTm n) (hs : Γ ⊢[PRAAx] source z R B a d L)
    (hS : Γ ⊢[PRAAx] productIdentification z R B x) (hp : Γ ⊢[PRAAx] le (threshold d R L) (unit p)) :
    Γ ⊢[PRAAx] lower (ap2 sineAtPiF p (sineAtPiData z B x)) (numerator a L) (denominator d R L) := by
  let A := numerator a L
  let D := denominator d R L
  let y := multiplyData P productLinearF x (productLinearData z R B)
  let q := ap2 (multiplyF P productLinearF) p y
  let r := ap2 sineAtPiF p (sineAtPiData z B x)
  let U := unit p
  have hD := denominator_positive d R L (le_trans hs.andE₁.andE₂.andE₁ hs.andE₁.andE₂.andE₂)
  have hA := numerator_positive a L hs.andE₁.andE₂.andE₁
  have hU := unit_positive (Γ := Γ) p
  have src : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B :=
    .andI hs.andE₁.andE₁.andE₁ (.andI hs.andE₁.andE₁.andE₂ hs.andE₂.andE₁)
  have eq := sine_as_product z R B x src hS
  have near := cross_at _ _ _ _ p p eq
  have large : Γ ⊢[PRAAx] le (two*D) U := le_trans (le_add_left _ _) hp
  have cmp : Γ ⊢[PRAAx] le ((U+U)*D) (A*(U*U)) := by
    have useful : Γ ⊢[PRAAx] le (two*D) (A*U) :=
      le_trans large (le_congr (one_mul U) (.eqRefl _) (mul_le_mul_right U hA))
    exact le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right U useful)
  have e := distance_symmetric r q A D hD (distance_radius_mono r q _ _ _ _ (positive_product _ _ hU hU) hD cmp near)
  exact lower_after_half_error q r A D hD (scaled_sample_lower z R B a d L p x hs
    (le_trans (le_add_right _ _) hp)) e

theorem actual_original_sine_R3_bound_of_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      productIdentification (var 0) (var 1) (var 2) (var 7) ⟶ le (threshold (var 4) (var 1) (var 5)) (unit (var 6)) ⟶
      lower (ap2 sineAtPiF (var 6) (sineAtPiData (var 0) (var 2) (var 7)))
        (numerator (var 3) (var 5)) (denominator (var 4) (var 1) (var 5))) :=
  closeUniv 8 (.impI (.impI (.impI
    (actual_sine_lower _ _ _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianSineReflectionLower
