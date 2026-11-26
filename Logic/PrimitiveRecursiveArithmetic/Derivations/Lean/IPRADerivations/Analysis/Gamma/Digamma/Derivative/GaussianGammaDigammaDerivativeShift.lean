import IPRADerivations.Analysis.Gamma.Digamma.Derivative.GaussianGammaDigammaDifferenceProduct

/-!
# Derivative recurrence of the original Gamma name

The exact fixed-step product rule and independent Euler derivative rates
give Gamma'(x+1) = x Gamma'(x) + Gamma(x) on every positive rational.
The comparison has a fixed rational budget over 2^p.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaDerivativeShift

open_ipra
open ComplexLogarithmRemainder (oneCode)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaDigammaNative (derivativeData derivative_regular minimumDenominator)
open GaussianGammaDigammaStep (stepQuotientData)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast multiplyModulus)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNameRingLaws (three)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qadd qmul)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianStirlingGammaLogarithm (source source_shift gammaData gamma_regular)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "IF" => GaussianEulerLogarithmicImproperName.nameF
local notation "QF" => GaussianNamedDifferenceQuotient.nameF gammaF gammaF

def productF : PR 2 := multiplyF constantF IF
def productData (a b : PTm n) : PTm n := multiplyData constantF IF (fraction a b) (derivativeData a b)
def nameF : PR 2 := addF productF gammaF
def data (a b : PTm n) : PTm n := addData (productData a b) (gammaData a b)

def budget (a b : PTm n) : PTm n :=
  three+two+(three+one)+three*(a+one)+GaussianNameBounds.U IF (derivativeData a b)+two+
    (three+(multiplyModulus constantF IF (fraction a b) (derivativeData a b)+one))

ipra_subst productData

ipra_subst data

ipra_subst budget [three]

theorem product_regular (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    pointCN productF (productData a b) :=
  multiply_fast _ _ _ _ (constant_regular _) (derivative_regular a b hs)

theorem name_regular (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx] pointCN nameF (data a b) :=
  add_fast _ _ _ _ (product_regular a b hs) (gamma_regular a b hs)

private theorem rate_at (p t a b D : PTm n) (hs : Γ ⊢[PRAAx] source a b)
    (hD : Γ ⊢[PRAAx] le (minimumDenominator p a b) D) (ht : Γ ⊢[PRAAx] le (unit p) (unit t)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 QF t (stepQuotientData a b D)) (ap2 IF p (derivativeData a b)) three (unit p) := by
  have hp := unit_positive (Γ := Γ) p
  refine distance_radius_mono _ _ _ _ _ _
    (GaussianNamedInverseRate.denominator_positive (unit p) t p hp) hp ?_
    (GaussianNamedInverseRate.rate_at QF IF _ _ one (unit p) t p (GaussianGammaDigammaStep.step_rate p a b D hs hD))
  unfold GaussianNamedInverseRate.rateNumerator GaussianNamedInverseRate.rateDenominator three
  ipra_le 𝔞 (unit p)*𝔞 (unit p)*sl ht

private theorem late_product_at (p t a b D : PTm n) (hs : Γ ⊢[PRAAx] source a b)
    (hD : Γ ⊢[PRAAx] le (minimumDenominator p a b) D)
    (hBudget : Γ ⊢[PRAAx] le
      ((multiplyModulus constantF QF (GaussianGammaDigammaDifferenceProduct.coefficient a b D)
        (stepQuotientData a b D)+one)*unit p) (unit t)) :
    Γ ⊢[PRAAx] distanceBounded
      (ap2 GaussianGammaDigammaDifferenceProduct.productF t (GaussianGammaDigammaDifferenceProduct.productData a b D))
      (qmul (GaussianGammaDigammaDifferenceProduct.coefficient a b D) (ap2 QF t (stepQuotientData a b D))) one (unit p) := by
  let u := GaussianGammaDigammaDifferenceProduct.coefficient a b D
  let q := stepQuotientData a b D
  refine distance_radius_mono _ _ _ _ _ _ (unit_positive t) (unit_positive p)
    (le_congr (.eqRefl _) (by ipra_ring) hBudget) ?_
  exact distance_congr (.eqRefl _) (qmul_congr (constant_at t u) (.eqRefl _)) (.eqRefl _) (.eqRefl _)
    (GaussianNameRingLaws.multiply_sample_error constantF QF u q t (constant_regular u)
      (GaussianGammaDigammaDifferenceProduct.quotient_regular a b D hs
        (GaussianGammaDigammaStep.denominator_positive p a b D hD)))

private theorem target_sample (p a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data a b))
      (qadd (qmul (fraction a b) (ap2 IF p (derivativeData a b))) (ap2 gammaF p (gammaData a b)))
      (three+(multiplyModulus constantF IF (fraction a b) (derivativeData a b)+one)) (unit p) := by
  have ha := GaussianNameRingLaws.add_sample_error productF gammaF (productData a b) (gammaData a b) p
    (product_regular a b hs) (gamma_regular a b hs)
  have hm := distance_congr (.eqRefl _) (qmul_congr (constant_at p (fraction a b)) (.eqRefl _)) (.eqRefl _) (.eqRefl _)
    (GaussianNameRingLaws.multiply_sample_error constantF IF (fraction a b) (derivativeData a b) p
      (constant_regular _) (derivative_regular a b hs))
  exact distance_triangle_same _ _ _ _ _ _ (unit_positive p) ha
    (GaussianNameRingLaws.sum_left_error _ _ _ _ _ (unit_positive p) hm)


set_option maxHeartbeats 1000000 in
theorem recurrence_at (p a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] distanceBounded (ap2 IF p (derivativeData (a+b) b)) (ap2 nameF p (data a b))
      (budget a b) (unit p) := by
  let D := minimumDenominator p a b+minimumDenominator p (a+b) b+unit p
  let u := GaussianGammaDigammaDifferenceProduct.coefficient a b D
  let v := fraction a b
  let q := stepQuotientData a b D
  let y := gammaData a b
  let e := derivativeData a b
  let L := multiplyModulus constantF QF u q+one
  let t := GaussianFastValueCut.exponent L p
  have hp := unit_positive (Γ := Γ) p
  have h0 : Γ ⊢[PRAAx] le (minimumDenominator p a b) D :=
    le_trans (le_add_right _ _) (le_add_right _ _)
  have h1 : Γ ⊢[PRAAx] le (minimumDenominator p (a+b) b) D :=
    le_trans (le_add_left _ _) (le_add_right _ _)
  have hD : Γ ⊢[PRAAx] le (unit p) D := le_add_left _ _
  have hD₁ := le_trans hp hD
  have hL : Γ ⊢[PRAAx] le one L := le_add_left _ _
  have hClock := GaussianFastValueCut.query_budget (Γ := Γ) L p
  have ht : Γ ⊢[PRAAx] le (unit p) (unit t) :=
    le_trans (le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right (unit p) hL)) hClock
  have hi := source_shift a b hs
  have hu := GaussianGammaDigammaStep.neighbor_coefficient_bound a b D hs.andE₂ hD₁
  have hd := derivative_regular a b hs
  have hg := gamma_regular a b hs
  have gammaNear := GaussianNameEquivalence.point_at gammaF y t p hg
  have gammaNear' := distance_radius_mono _ _ _ _ two (unit p)
    (GaussianRationalHorner.positive_product _ _ (unit_positive t) hp) hp
    (by ipra_le 𝔞 (unit p)*sl ht) gammaNear
  have initial := distance_symmetric _ _ _ _ hp (rate_at p p (a+b) b D hi h1 (le_refl _))
  have cross := GaussianNameEquivalence.cross_at QF GaussianGammaDigammaDifferenceProduct.nameF
    (stepQuotientData (a+b) b D) (GaussianGammaDigammaDifferenceProduct.data a b D) p t
    (GaussianGammaDigammaDifferenceProduct.step_product_rule a b D hs hD₁)
  have cross' := distance_radius_mono _ _ _ _ two (unit p)
    (GaussianRationalHorner.positive_product _ _ hp (unit_positive t)) hp
    (by ipra_le 𝔞 (unit p)*sl ht) cross
  have first := distance_triangle_same _ _ _ _ _ _ hp initial cross'
  have readback := GaussianNameRingLaws.add_sample_error GaussianGammaDigammaDifferenceProduct.productF gammaF
    (GaussianGammaDigammaDifferenceProduct.productData a b D) y t
    (GaussianGammaDigammaDifferenceProduct.product_regular a b D hs hD₁) hg
  have readback' := distance_radius_mono _ _ _ _ three (unit p) (unit_positive t) hp
    (by ipra_le 𝔞 three*sl ht) readback
  have prod := late_product_at p t a b D hs h0 hClock
  have second := distance_triangle_same _ _ _ _ _ _ hp readback'
    (GaussianNameRingLaws.sum_left_error _ _ _ _ _ hp prod)
  have third := GaussianNameRingLaws.sum_left_error _ _ (ap2 gammaF t y) _ _ hp
    (GaussianNamedDifferenceQuotient.scale_distance u _ _ (a+one) three (unit p) hp hu
      (rate_at p t a b D hs h0 ht))
  have diff : Γ ⊢[PRAAx] distanceBounded u v one (unit p) :=
    GaussianRationalReciprocal.bound_congr (GaussianGammaDigammaStep.coefficient_difference a b D hs.andE₂ hD₁).eqSymm
      (.eqRefl _) (.eqRefl _) (GaussianGammaUnitEulerDifference.increment_bound (unit p) D hp hD)
  have dBound := GaussianNameBounds.sample_bound IF e p hd
  have coeff : Γ ⊢[PRAAx] distanceBounded (qmul u (ap2 IF p e)) (qmul v (ap2 IF p e))
      (GaussianNameBounds.U IF e) (unit p) :=
    distance_congr (qmul_commutative _ _) (qmul_commutative _ _) (by ipra_ring) (.eqRefl _)
      (GaussianNamedDifferenceQuotient.scale_distance (ap2 IF p e) u v _ one (unit p) hp dBound diff)
  have fourth := GaussianNameRingLaws.sum_left_error _ _ (ap2 gammaF t y) _ _ hp coeff
  have fifth := GaussianNameRingLaws.sum_right_error (qmul v (ap2 IF p e)) _ _ _ _ hp gammaNear'
  have joined := distance_triangle_same _ _ _ _ _ _ hp
    (distance_triangle_same _ _ _ _ _ _ hp
      (distance_triangle_same _ _ _ _ _ _ hp (distance_triangle_same _ _ _ _ _ _ hp first second) third)
      fourth) fifth
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold budget; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp joined (distance_symmetric _ _ _ _ hp (target_sample p a b hs)))

set_option maxHeartbeats 800000 in
theorem derivative_shift (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    crossEquivalent IF nameF (derivativeData (a+b) b) (data a b) := by
  refine GaussianNameRingLaws.equivalent_of_envelope IF nameF _ _ (budget a b)
    (derivative_regular (a+b) b (source_shift a b hs)) (name_regular a b hs) (.allI ?_)
  have h : (Γ.map Fm.shift) ⊢[PRAAx] source (Syn.shift a) (Syn.shift b) := by simpa only [Fm.shift,Syn.shift,GaussianStirlingGammaLogarithm.subst_source] using hs.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift,GaussianGammaDigammaNative.subst_derivativeData,
    subst_data,subst_budget,PTm.subst_add] using recurrence_at (var 0) (Syn.shift a) (Syn.shift b) h

theorem actual_gamma_derivative_recurrence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (source (var 0) (var 1) ⟶ crossEquivalent IF nameF (derivativeData (var 0+var 1) (var 1)) (data (var 0) (var 1))) :=
  closeUniv 2 (.impI (derivative_shift _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaDerivativeShift
