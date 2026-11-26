import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalFiniteCenteredExponentialShift
import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalFiniteCentralExponentialBound
import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalWeightedTaylorBall
import IPRADerivations.Analysis.Euler.GaussianEulerNamedPowerScalingPowerFrozen
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedAddRate

/-!
# Weighted Taylor comparison for the literal finite Barnes product

Keep the actual cutoff in the scalar and exponent buffer. The error uses
one bound for every finite central scalar, with the same weighted head
polynomial and displacement ball as the cofinal comparison.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteWeightedTaylorValue

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (add)
open GaussianBarnesCanonicalCenteredExponentialShift (head)
open GaussianBarnesCanonicalCenteredProductRate (headCap head_bound)
open GaussianBarnesCanonicalCorrectedMercatorCofinal (analyticDenominator analytic_denominator_positive)
open GaussianBarnesCanonicalExponentTaylorBallSchedule (precision)
open GaussianBarnesCanonicalExponentTaylorBuffer (buffer buffer_length buffer_zero)
open GaussianBarnesCanonicalExponentTaylorWeightedMass (massCap)
open GaussianBarnesCanonicalFiniteCentralExponential (finiteNameF finiteData finite_regular)
open GaussianBarnesCanonicalFiniteCentralExponentialBound (centralCap central_samples)
open GaussianBarnesCanonicalFiniteExponentTaylor (scheduledNumerator scheduledDenominator)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianBarnesCanonicalTaylorProduct (headPolynomial headDegree)
open GaussianBarnesCanonicalWeightedTaylorBall (headMass head_mass)
open GaussianBarnesCanonicalWeightedTaylorBallSource (input stepDivisor)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianDominantPairAlgebra (radiusPoint)
open GaussianEuclideanDistanceName (fraction pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameBounds (U all_samples_bounded)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedDifferenceRate (rate_parameters_congr self_rate)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedMultiplyRate (sampleBound)
open GaussianNamedRateComposition (leadingDenominator)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (evaluate ofGaussian ofGaussian_canonical positive_product qmul)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalPolynomialDilation (weightedNorm)
open GaussianRationalSyntheticDivision (canonicalCoefficients)
open RationalArgmin (rationalLE)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "C" => constantF
local notation "S" => finiteNameF
local notation "I" => GaussianBarnesCanonicalFiniteExponentTaylor.nameF
local notation "E" => GaussianRadiusExponentialName.nameF I
local notation "V" => GaussianBarnesCanonicalValue.prefixF
local notation "literal" => GaussianBarnesCanonicalProduct.literalData

abbrev nameF : PR 2 := multiplyF S C

def polynomial (p z R B H r M : PTm n) : PTm n :=
  GaussianBarnesCanonicalTaylorProduct.polynomial z R B (buffer (precision p R H) z R B r M) (previous M) (previous M)

def data (p z h R B H r M : PTm n) : PTm n :=
  multiplyData S C (finiteData z R B r) (evaluate (polynomial p z R B H r M) (ofGaussian h B))

def numerator_with_caps (p R B H M P F : PTm n) : PTm n :=
  let D := scheduledDenominator p R B M
  let J := scheduledNumerator p R B H M
  let m := previous M
  let L := massCap R
  let a := GaussianBarnesCanonicalTaylorRecomposition.error J D m L (num 4*H) B two
  let b := (P*pw (num 3) L)*pw (num 4*H) (succ m)
  headCap R*(F*a)+D*(F*b)

def numerator (p z R B H M : PTm n) : PTm n :=
  numerator_with_caps p R B H M (headMass z R B) (centralCap z R B)

def denominator (p R B M : PTm n) : PTm n :=
  GaussianBarnesCanonicalTaylorRecomposition.denominator (scheduledDenominator p R B M) (previous M) B

theorem polynomial_length (p z R B H r M : PTm n) :
    Γ ⊢[PRAAx] length (polynomial p z R B H r M) ≐ succ (previous M) :=
  GaussianRationalPolynomialExponentialProductTruncation.polynomial_length _ _ _ _ _

theorem polynomial_canonical (p z R B H r M : PTm n) :
    Γ ⊢[PRAAx] canonicalCoefficients (polynomial p z R B H r M) :=
  GaussianRationalPolynomialExponentialProductTruncation.polynomial_canonical _ _ _ _ _

theorem regular (p z h R B H r M : PTm n) (hz : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] pointCN nameF (data p z h R B H r M) :=
  multiply_fast _ _ _ _ (finite_regular z R B r hz) (constant_regular _)

private theorem exponent_radius (p R B H M : PTm n) (hh : Γ ⊢[PRAAx] le (num 4*H) B) :
    Γ ⊢[PRAAx] le (scheduledNumerator p R B H M) (two*scheduledDenominator p R B M) := by
  let d := analyticDenominator (previous M) R B
  have a := mul_le_mul_right (unit p) (GaussianBarnesCanonicalExponentTaylorSchedule.analytic_le_one R B H M hh)
  have b : Γ ⊢[PRAAx] le d (d*unit p) :=
    le_congr (one_mul d) (by ipra_ring) (mul_le_mul_right d (unit_positive p))
  exact le_congr (.eqRefl _) (by change Γ ⊢[PRAAx] d*unit p+d*unit p ≐ two*(d*unit p); ipra_ring) (add_le_add₂ a b)

private theorem multiply_left_rate (f g k : PR 2) (x y v M A D : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) (hk : Γ ⊢[PRAAx] pointCN k v)
    (hm : Γ ⊢[PRAAx] sampleBound f x M) (hd : Γ ⊢[PRAAx] le one D)
    (hr : Γ ⊢[PRAAx] independentRate g k y v A D) :
    Γ ⊢[PRAAx] independentRate (multiplyF f g) (multiplyF f k)
      (multiplyData f g x y) (multiplyData f k x v) (M*A) D := by
  have h := GaussianNamedMultiplyRate.independent_rate f g f k x y x v zero one A D (U g y) M
    (le_refl one) hd hf hg hf hk (all_samples_bounded g y hg) hm (self_rate f x hf) hr
  exact rate_parameters_congr _ _ _ _ _ _ _ _
    (by unfold GaussianNamedMultiplyRate.leadingNumerator; ipra_ring)
    (by unfold GaussianNamedMultiplyRate.leadingDenominator; ipra_ring) h

private theorem gather_constants (z h R B r v : PTm n) (hz : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF C nameF) nameF
      (multiplyData C nameF (head z h R B) (multiplyData S C (finiteData z R B r) v))
      (multiplyData S C (finiteData z R B r) (qmul (head z h R B) v)) := by
  let a := head z h R B
  let x := finiteData z R B r
  let q := qmul a v
  have ha := constant_regular (Γ := Γ) a
  have hx := finite_regular z R B r hz
  have hv := constant_regular (Γ := Γ) v
  have hq := constant_regular (Γ := Γ) q
  have split := GaussianNameRingLaws.multiply_associative C S C a x v ha hx hv
  have swap := GaussianNameRingLaws.multiply_commutative C S a x ha hx
  have moved := multiply_cross (multiplyF C S) nameF C C (multiplyData C S a x) (multiplyData S C x a) v v
    (multiply_fast _ _ _ _ ha hx) (multiply_fast _ _ _ _ hx ha) hv hv swap (cross_refl _ _ hv)
  have grouped := GaussianNameRingLaws.multiply_associative S C C x a v hx ha hv
  have bound := GaussianGammaDigammaTwoShiftNamedSize.constant_product (Γ := Γ) a v q (.eqRefl _)
  have collapsed := multiply_cross S S (multiplyF C C) C x x (multiplyData C C a v) q
    hx hx (multiply_fast _ _ _ _ ha hv) hq (cross_refl _ _ hx) bound
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ split)
    (cross_trans _ _ _ _ _ _ moved (cross_trans _ _ _ _ _ _ grouped collapsed))

private theorem recomposition_input (p z h R B H r M : PTm n) (hs : Γ ⊢[PRAAx] input z h R B H M) :
    Γ ⊢[PRAAx] GaussianBarnesCanonicalWeightedTaylorRecomposition.input (buffer (precision p R H) z R B r M)
      (previous M) (previous M) (ofGaussian h B) H B (massCap R) := by
  let q := precision p R H
  let m := previous M
  have hB := hs.andE₁.andE₁.andE₁
  have hm : Γ ⊢[PRAAx] le m (m*m) :=
    le_congr (one_mul m) (.eqRefl _) (mul_le_mul_right m (zero_lt_succ (succ M)))
  have hw := GaussianBarnesCanonicalHeadPolynomialDerivative.step_bound h B H hB hs.andE₁.andE₂.andE₂.andE₁
  have mass := GaussianBarnesCanonicalExponentTaylorWeightedMass.mass q z R B r M hs.andE₁.andE₁
  exact .andI (buffer_length q z R B r M) (.andI (buffer_zero q z R B r M)
    (.andI hm (.andI hB (.andI hs.andE₂.andE₁ (.andI hs.andE₂.andE₂ (.andI mass hw))))))

theorem rate_with_caps (p z h R B H r M A F : PTm n) (hs : Γ ⊢[PRAAx] input z h R B H M)
    (hHead : Γ ⊢[PRAAx] rationalLE (weightedNorm (headPolynomial z R B) (headDegree R) (radiusPoint one (num 4)))
      (fraction A one)) (hcap : Γ ⊢[PRAAx] sampleBound S (finiteData z R B r) F) :
    Γ ⊢[PRAAx] independentRate V nameF (literal (add z h) R B (initial R+r)) (data p z h R B H r M)
      (numerator_with_caps p R B H M A F) (denominator p R B M) := by
  let m := previous M
  let w := ofGaussian h B
  let c := buffer (precision p R H) z R B r M
  let v := GaussianRationalPolynomialExponentialRecomposition.value c m m w
  let K := headCap R
  let L := massCap R
  let D := scheduledDenominator p R B M
  let J := scheduledNumerator p R B H M
  let a := GaussianBarnesCanonicalTaylorRecomposition.error J D m L (num 4*H) B two
  let b := (A*pw (num 3) L)*pw (num 4*H) (succ m)
  let e := pw B (succ m)
  let d := denominator p R B M
  let x := finiteData z R B r
  let y := GaussianBarnesCanonicalFiniteCenteredExponentialShift.incrementExpData z h R B r
  let u := head z h R B
  let j := qmul u v
  let mid := multiplyData S C x j
  have hz := hs.andE₁.andE₁
  have hw := hs.andE₁.andE₂.andE₁
  have hB := hz.andE₁
  have hD : Γ ⊢[PRAAx] le one D :=
    positive_product _ _ (analytic_denominator_positive m R B hB) (unit_positive p)
  have he : Γ ⊢[PRAAx] le one e := GaussianFactorBudget.power_positive B (succ m) hB
  have hd : Γ ⊢[PRAAx] le one d := positive_product D e hD he
  have hc := recomposition_input p z h R B H r M hs
  have hx := finite_regular z R B r hz
  have hy := GaussianBarnesCanonicalFiniteCenteredExponentialShift.increment_exp_regular z h R B r hz hw
  have hv := constant_regular (Γ := Γ) v
  have hu := constant_regular (Γ := Γ) u
  have expRate := GaussianBarnesCanonicalWeightedTaylorRecomposition.named_exponential_rate I
    (GaussianBarnesCanonicalFiniteExponentTaylor.data z h R B r) c m m h H B L J D two
    (GaussianBarnesCanonicalFiniteExponentTaylor.regular z h R B r hz hw) hc hD
    (exponent_radius p R B H M hs.andE₂.andE₁)
    (GaussianBarnesCanonicalFiniteExponentTaylor.scheduled_rate p z h R B H r M hs.andE₁)
  have inner := multiply_left_rate S E C x y v F a d hx hy hv hcap hd expRate
  have outer := multiply_left_rate C (multiplyF S E) nameF u (multiplyData S E x y) (multiplyData S C x v)
    K (F*a) d hu (multiply_fast _ _ _ _ hx hy) (multiply_fast _ _ _ _ hx hv)
    (GaussianEulerNamedPowerScalingPowerFrozen.constant_bound _ _ (head_bound z h R B hw)) hd inner
  have first : Γ ⊢[PRAAx] independentRate V nameF (literal (add z h) R B (initial R+r)) mid (K*(F*a)) d :=
    GaussianNamedRateTransport.transport _ _ _ _ _ _ _ _ _ _ hd outer
      (GaussianBarnesCanonicalFiniteCenteredExponentialShift.literal_shift z h R B r hz hw)
      (cross_symm _ _ _ _ (gather_constants z h R B r v hz))
  have hp := GaussianBarnesCanonicalCenteredHead.polynomial_length (Γ := Γ) z B (initial R)
  have fit : Γ ⊢[PRAAx] le (num 4*H) (one*B) := le_congr (.eqRefl _) (one_mul B).eqSymm hs.andE₂.andE₁
  have rawTail := GaussianRationalPolynomialExponentialWeightedProductTruncation.fixed_radius_tail
    (headPolynomial z R B) c (headDegree R) m m w one (num 4) H B A L hp hc.andE₁ hc.andE₂.andE₂.andE₁
    (le_refl one) (zero_lt_succ _) hB fit (ofGaussian_canonical h B hB)
    hc.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂ hHead
    hc.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
  have tail : Γ ⊢[PRAAx] distanceBounded j (evaluate (polynomial p z R B H r M) w) b e :=
    distance_congr (.eqRefl _) (.eqRefl _) (.eqRefl _)
      (congrAp2 powF (.eqRefl (succ m)) (one_mul B)) rawTail
  have final : Γ ⊢[PRAAx] independentRate nameF nameF mid (data p z h R B H r M) (F*b) e :=
    multiply_left_rate S C C x j _ F b e hx (constant_regular _) (constant_regular _) hcap he
      (GaussianNamedAddRate.constant_rate _ _ _ _ he tail)
  have adjust : Γ ⊢[PRAAx] le ((F*b)*d) ((D*(F*b))*e) :=
    le_of_eq_add (d := zero) (by change Γ ⊢[PRAAx] D*(F*b)*e ≐ (F*b)*(D*e)+zero; ipra_ring)
  exact GaussianNamedRateComposition.same_denominator V nameF nameF (literal (add z h) R B (initial R+r)) mid
    (data p z h R B H r M) _ d _ hd first
    (GaussianNamedRateRadius.weaken _ _ _ _ (F*b) e (D*(F*b)) d he hd adjust final)

theorem rate (p z h R B H r M : PTm n) (hs : Γ ⊢[PRAAx] input z h R B H M) :
    Γ ⊢[PRAAx] independentRate V nameF (literal (add z h) R B (initial R+r)) (data p z h R B H r M)
      (numerator p z R B H M) (denominator p R B M) :=
  rate_with_caps p z h R B H r M (headMass z R B) (centralCap z R B) hs
    (head_mass z R B) (central_samples z R B r hs.andE₁.andE₁)

theorem shared_rate (p z h R B H r M : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hh : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded h H)
    (hsmall : Γ ⊢[PRAAx] le (stepDivisor R*H) B) :
    Γ ⊢[PRAAx] independentRate V nameF (literal (add z h) (R+one) B (initial (R+one)+r))
      (data p z h (R+one) B H r M) (numerator p z (R+one) B H M) (denominator p (R+one) B M) :=
  rate p z h (R+one) B H r M (GaussianBarnesCanonicalWeightedTaylorBallSource.admission z h R B H M hz hh hsmall)

theorem actual_Barnes_finite_weighted_Taylor_value_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (let p := var 0
     let z := var 1
     let h := var 2
     let R := var 3
     let B := var 4
     let H := var 5
     let r := var 6
     let M := var 7
     input z h R B H M ⟶ independentRate V nameF (literal (add z h) R B (initial R+r))
       (data p z h R B H r M) (numerator p z R B H M) (denominator p R B M)) :=
  closeUniv 8 (.impI (rate _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteWeightedTaylorValue
