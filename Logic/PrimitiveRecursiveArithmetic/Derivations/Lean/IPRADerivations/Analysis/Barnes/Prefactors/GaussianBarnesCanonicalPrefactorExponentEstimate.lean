import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.Prefactors.GaussianBarnesCanonicalPrefactorExponentDerivative
import IPRADerivations.Analysis.Barnes.Prefactors.GaussianBarnesCanonicalPrefactorLipschitz
import IPRADerivations.Analysis.Names.FiniteOperations.Products.Bounds.GaussianNamedBoundedProductObservation

/-!
# Quantitative expansion of the original Barnes prefactor exponent

The square increment has its literal quadratic remainder. Propagating
it through the original named Stirling and Euler constant arithmetic
gives a bound for the small exponent increment and a quadratic rate
for its first-order approximation.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPrefactorExponentEstimate

open_ipra
open GaussianRationalPowerDifference (bounded_sum_one bounded_sum_same)
open ComplexLogarithmRemainder (add)
open GaussianBarnesCanonicalPrefactor
  (linearF quadraticCoefficientF quadraticCoefficientData quadraticF polynomialF negativeHalf correctionF quadratic_coefficient_regular)
open GaussianBarnesCanonicalPrefactorInverse (exponentF)
open GaussianBarnesCanonicalPrefactorExponentDerivative
  (linearOf quadraticOf polynomialOf correctionOf exponentOf square squareStep twicePoint linearSquare incrementData linearData derivativeData)
open GaussianBarnesCanonicalPrefactorLipschitz (linearGain quadraticGain halfGain exponentGain)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameBounds (U all_samples_bounded)
open GaussianNamedDifferenceRate (rate_parameters_congr self_rate)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (ofGaussian ofGaussian_represents ofGaussian_canonical qadd qmul qmul_canonical qadd_canonical positive_product)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalReciprocal (bounded_product bound_congr qone qone_bounded)
open GaussianRationalSyntheticDivision (qmul_congr qadd_congr qsub_congr qadd_sub_cancel)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "C" => constantF
local notation "Q" => quadraticCoefficientF
local notation "S" => GaussianStirlingConstant.nameF

def quadraticErrorGain : PTm n := halfGain*quadraticGain

@[simp] theorem subst_quadraticErrorGain {m : ℕ} (σ : Fin n → PTm m) :
    Syn.subst σ (quadraticErrorGain : PTm n) = quadraticErrorGain :=
  by simp [quadraticErrorGain,halfGain,quadraticGain,quadraticCoefficientData,negativeHalf,one,two]

private theorem bounds_product (f g : PR 2) (p x y A B L : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hf : ∀ k, Γ ⊢[PRAAx] bounded (ap2 f k x) A B) (hg : ∀ k, Γ ⊢[PRAAx] bounded (ap2 g k y) L one) :
    Γ ⊢[PRAAx] bounded (ap2 (multiplyF f g) p (multiplyData f g x y)) (A*L) B := by
  let k := GaussianFastValueCut.exponent (GaussianNameArithmetic.multiplyModulus f g x y) p
  exact bound_congr (GaussianNamedBoundedProductObservation.name_at f g p x y).eqSymm (.eqRefl _)
    (show Γ ⊢[PRAAx] B*one ≐ B by ipra_ring)
    (bounded_product _ _ _ _ _ _ hB (le_refl one) (hf k) (hg k))

private theorem bounds_left_product (f g : PR 2) (p x y A B L : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hf : ∀ k, Γ ⊢[PRAAx] bounded (ap2 f k x) L one) (hg : ∀ k, Γ ⊢[PRAAx] bounded (ap2 g k y) A B) :
    Γ ⊢[PRAAx] bounded (ap2 (multiplyF f g) p (multiplyData f g x y)) (L*A) B := by
  let k := GaussianFastValueCut.exponent (GaussianNameArithmetic.multiplyModulus f g x y) p
  exact bound_congr (GaussianNamedBoundedProductObservation.name_at f g p x y).eqSymm (.eqRefl _) (one_mul _)
    (bounded_product _ _ _ _ _ _ (le_refl one) hB (hf k) (hg k))

private theorem bounds_sum (f g : PR 2) (p x y A D B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hf : ∀ k, Γ ⊢[PRAAx] bounded (ap2 f k x) A B) (hg : ∀ k, Γ ⊢[PRAAx] bounded (ap2 g k y) D B) :
    Γ ⊢[PRAAx] bounded (ap2 (addF f g) p (addData x y)) (A+D) B := by
  let k := GaussianFastValueCut.exponent two p
  have read := (GaussianNameArithmetic.add_at (Γ := Γ) f g x y p).eqTrans
    (GaussianExponentialReference.recode_fixed _ (qadd_canonical (ap2 f k x) (ap2 g k y)))
  exact bound_congr read.eqSymm (.eqRefl _) (.eqRefl _)
    (bounded_sum_same _ _ _ _ _ hB (hf k) (hg k))

private theorem constant_bound (p q A B : PTm n) (h : Γ ⊢[PRAAx] bounded q A B) :
    Γ ⊢[PRAAx] bounded (ap2 C p q) A B := bound_congr (constant_at p q).eqSymm (.eqRefl _) (.eqRefl _) h

theorem exponent_sample_bound (p a b A D B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (ha : Γ ⊢[PRAAx] bounded a A B) (hb : Γ ⊢[PRAAx] bounded b D B) :
    Γ ⊢[PRAAx] bounded (ap2 exponentF p (exponentOf a b)) (linearGain*A+halfGain*(A+quadraticGain*D)) B := by
  let s : PTm n := GaussianStirlingConstant.nameData zero
  let q : PTm n := quadraticCoefficientData
  let c : PTm n := negativeHalf
  have sBound := all_samples_bounded S s (GaussianStirlingConstant.name_regular (Γ := Γ) zero)
  have qBound := all_samples_bounded Q q (quadratic_coefficient_regular (Γ := Γ))
  have cBound := all_samples_bounded C c (constant_regular (Γ := Γ) c)
  have hlin : ∀ j, Γ ⊢[PRAAx] bounded (ap2 linearF j (linearOf a)) (linearGain*A) B := fun j =>
    bound_congr (.eqRefl _) (mul_comm _ _) (.eqRefl _)
      (bounds_product C S j a s A B linearGain hB (fun k => constant_bound k a A B ha)
        (fun k => GaussianRadiusExponentialName.bounded_samples_at S linearGain s k sBound))
  have hquad : ∀ j, Γ ⊢[PRAAx] bounded (ap2 quadraticF j (quadraticOf b)) (quadraticGain*D) B := fun j =>
    bound_congr (.eqRefl _) (mul_comm _ _) (.eqRefl _)
      (bounds_product C Q j b q D B quadraticGain hB (fun k => constant_bound k b D B hb)
        (fun k => GaussianRadiusExponentialName.bounded_samples_at Q quadraticGain q k qBound))
  have hpoly : ∀ j, Γ ⊢[PRAAx] bounded (ap2 polynomialF j (polynomialOf a b)) (A+quadraticGain*D) B := fun j =>
    bounds_sum C quadraticF j a (quadraticOf b) A (quadraticGain*D) B hB (fun k => constant_bound k a A B ha) hquad
  have hcorr : ∀ j, Γ ⊢[PRAAx] bounded (ap2 correctionF j (correctionOf a b)) (halfGain*(A+quadraticGain*D)) B := fun j =>
    bounds_left_product C polynomialF j c (polynomialOf a b) _ B halfGain hB
      (fun k => GaussianRadiusExponentialName.bounded_samples_at C halfGain c k cBound) hpoly
  exact bounds_sum linearF correctionF p (linearOf a) (correctionOf a b) _ _ B hB hlin hcorr

private theorem native_step_bound (h H B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hh : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded h H) : Γ ⊢[PRAAx] bounded (ofGaussian h B) H B :=
  GaussianRationalMetric.bounded_of_cleared _ _ _ _ _ hB hB (ofGaussian_represents h B hB)
    (le_congr (.eqRefl _) (mul_comm _ _) (le_mul_mono (le_refl (B*B)) hh))

theorem increment_sample_bound (p z h R B H : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B))
    (hw : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (add z h) (R*B))
    (hh : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded h H) :
    Γ ⊢[PRAAx] bounded (ap2 exponentF p (incrementData z h B)) (exponentGain R*H) B := by
  let a := ofGaussian (add z h) B
  let b := ofGaussian z B
  have e := GaussianBarnesCanonicalHeadCorrectionDerivative.point_increment z h B hB
  have hs := native_step_bound h H B hB hh
  have d : Γ ⊢[PRAAx] distanceBounded a b H B := bound_congr e.eqSymm (.eqRefl _) (.eqRefl _) hs
  have aBound := GaussianGammaEulerHead.fraction_disk (add z h) R B hB hw
  have bBound := GaussianGammaEulerHead.fraction_disk z R B hB hz
  have q : Γ ⊢[PRAAx] bounded (squareStep z h B) (two*R*H) B :=
    GaussianRationalDistanceOrder.distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (GaussianNameArithmetic.product_distance a b a b H H B R R hB d d aBound bBound)
  exact bound_congr (.eqRefl _) (by unfold exponentGain; ipra_ring) (.eqRefl _)
    (exponent_sample_bound p (ofGaussian h B) (squareStep z h B) H (two*R*H) B hB hs q)

theorem derivative_sample_bound (p z R B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) :
    Γ ⊢[PRAAx] bounded (ap2 exponentF p (derivativeData z B)) (exponentGain R) one := by
  let a := ofGaussian z B
  have b := GaussianGammaEulerHead.fraction_disk z R B hB hz
  have twoB : Γ ⊢[PRAAx] bounded (twicePoint z B) (two*R) one := bound_congr (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (bounded_sum_one b b)
  exact bound_congr (.eqRefl _) (by unfold exponentGain; ipra_ring) (.eqRefl _)
    (exponent_sample_bound p qone (twicePoint z B) one (two*R) one (le_refl one) qone_bounded twoB)

private theorem left_distribute (a b c : PTm n) : Γ ⊢[PRAAx] qmul a (qadd b c) ≐ qadd (qmul a b) (qmul a c) :=
  (GaussianRationalPowerAlgebra.qmul_commutative a (qadd b c)).eqTrans
    ((GaussianEulerIncompleteFactorialCombination.right_distribute b c a).eqTrans
      (qadd_congr (GaussianRationalPowerAlgebra.qmul_commutative b a) (GaussianRationalPowerAlgebra.qmul_commutative c a)))

private theorem square_expansion (z h B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] squareStep z h B ≐ qadd (linearSquare z h B) (qmul (ofGaussian h B) (ofGaussian h B)) := by
  let a := ofGaussian z B
  let b := ofGaussian (add z h) B
  let s := ofGaussian h B
  have step := GaussianBarnesCanonicalHeadCorrectionDerivative.point_increment z h B hB
  have rebuild : Γ ⊢[PRAAx] qadd a s ≐ b := (qadd_congr (.eqRefl a) step.eqSymm).eqTrans
    (GaussianRationalLinearProduct.add_sub_right a b (ofGaussian_canonical _ _ hB))
  have first := (GaussianRationalPowerDifference.product_difference (Γ := Γ) b a b a).eqTrans
    (qadd_congr (qmul_congr step rebuild.eqSymm) ((qmul_congr (.eqRefl _) step).eqTrans
      (GaussianRationalPowerAlgebra.qmul_commutative a s)))
  have second := qadd_congr (left_distribute (Γ := Γ) s a s) (.eqRefl (qmul s a))
  have reorder := (GaussianRationalSumAlgebra.qadd_associative (Γ := Γ) (qmul s a) (qmul s s) (qmul s a)).eqTrans
    ((qadd_congr (.eqRefl _) (GaussianReciprocalHorner.qadd_commutative (qmul s s) (qmul s a))).eqTrans
      (GaussianRationalSumAlgebra.qadd_associative _ _ _).eqSymm)
  exact first.eqTrans (second.eqTrans (reorder.eqTrans
    (qadd_congr (left_distribute s a a).eqSymm (.eqRefl _))))

theorem square_error (z h B H : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hh : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded h H) :
    Γ ⊢[PRAAx] distanceBounded (squareStep z h B) (linearSquare z h B) (H*H) (B*B) := by
  have hs := native_step_bound h H B hB hh
  have product := bounded_product _ _ _ _ _ _ hB hB hs hs
  exact bound_congr ((qsub_congr (square_expansion z h B hB) (.eqRefl _)).eqTrans
    (qadd_sub_cancel _ _ (qmul_canonical _ _))).eqSymm (.eqRefl _) (.eqRefl _) product

theorem rate (z h B H : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hh : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded h H) :
    Γ ⊢[PRAAx] independentRate exponentF exponentF (incrementData z h B) (linearData z h B)
      (quadraticErrorGain*H*H) (B*B) := by
  let a := ofGaussian h B
  let b := squareStep z h B
  let v := linearSquare z h B
  let q : PTm n := quadraticCoefficientData
  let c : PTm n := negativeHalf
  let D := B*B
  let G : PTm n := quadraticGain
  let K : PTm n := halfGain
  let E := H*H
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ hB hB
  have ha := constant_regular (Γ := Γ) a
  have hb := constant_regular (Γ := Γ) b
  have hv := constant_regular (Γ := Γ) v
  have hc := constant_regular (Γ := Γ) c
  have hq := quadratic_coefficient_regular (Γ := Γ)
  have hbq := multiply_fast C Q b q hb hq
  have hvq := multiply_fast C Q v q hv hq
  have hp := add_fast C quadraticF a (quadraticOf b) ha hbq
  have hP := add_fast C quadraticF a (quadraticOf v) ha hvq
  have raw := GaussianNamedAddRate.constant_rate b v E D hD (square_error z h B H hB hh)
  have qRate := GaussianNamedMultiplyRate.independent_rate C Q C Q b q v q E D zero one G (U C v) hD (le_refl one)
    hb hq hv hq (all_samples_bounded Q q hq) (all_samples_bounded C v hv) raw (self_rate Q q hq)
  have hQuad : Γ ⊢[PRAAx] independentRate quadraticF quadraticF (quadraticOf b) (quadraticOf v) (G*E) D :=
    rate_parameters_congr _ _ _ _ _ _ _ _ (by unfold GaussianNamedMultiplyRate.leadingNumerator; ipra_ring)
      (by unfold GaussianNamedMultiplyRate.leadingDenominator; ipra_ring) qRate
  have pRate := GaussianNamedAddRate.independent_rate C quadraticF C quadraticF a (quadraticOf b) a (quadraticOf v)
    zero one (G*E) D (le_refl one) hD (self_rate C a ha) hQuad
  have hPoly : Γ ⊢[PRAAx] independentRate polynomialF polynomialF (polynomialOf a b) (polynomialOf a v) (G*E) D :=
    rate_parameters_congr _ _ _ _ _ _ _ _ (by unfold GaussianNamedRateComposition.leadingNumerator; ipra_ring)
      (by unfold GaussianNamedRateComposition.leadingDenominator; ipra_ring) pRate
  have cRate := GaussianNamedMultiplyRate.independent_rate C polynomialF C polynomialF c (polynomialOf a b)
    c (polynomialOf a v) zero one (G*E) D (U polynomialF (polynomialOf a b)) K (le_refl one) hD hc hp hc hP
    (all_samples_bounded polynomialF _ hp) (all_samples_bounded C _ hc) (self_rate C c hc) hPoly
  have hCorr : Γ ⊢[PRAAx] independentRate correctionF correctionF (correctionOf a b) (correctionOf a v) (K*(G*E)) D :=
    rate_parameters_congr _ _ _ _ _ _ _ _ (by unfold GaussianNamedMultiplyRate.leadingNumerator; ipra_ring)
      (by unfold GaussianNamedMultiplyRate.leadingDenominator; ipra_ring) cRate
  have l := multiply_fast C S a (GaussianStirlingConstant.nameData zero) ha (GaussianStirlingConstant.name_regular zero)
  have eRate := GaussianNamedAddRate.independent_rate linearF correctionF linearF correctionF (linearOf a) (correctionOf a b)
    (linearOf a) (correctionOf a v) zero one (K*(G*E)) D (le_refl one) hD (self_rate linearF _ l) hCorr
  exact rate_parameters_congr _ _ _ _ _ _ _ _
    (by dsimp only [K,G,E,quadraticErrorGain,GaussianNamedRateComposition.leadingNumerator]; ipra_ring)
    (by dsimp only [D,GaussianNamedRateComposition.leadingDenominator]; ipra_ring) eRate

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPrefactorExponentEstimate
