import IPRADerivations.Analysis.Euler.Integration.Parts.GaussianEulerIntegrationByPartsLinear

/-!
# Actual original power-times-decay first-order remainder

The checked original power and decay increments feed the literal product
residual identity. On a positive compact interval, both quadratic and
sampling errors have constants independent of the time numerator and
step. The step is at most one; no division by that step is used.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIntegrationByPartsProductStep

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerIntegrationByPartsLinear (decay originalProduct productLinear decayLinear)
open GaussianEulerPowerIncrement (point slopeTerm)
open GaussianEulerCompactPowerMajorant (majorant original_power_observation)
open GaussianRationalFirstOrderProductError (error productError decomposedError)
open GaussianRationalHorner (qadd qmul positive_product qmul_canonical)
open GaussianRationalMetric (qsub bounded distanceBounded qnegative)
open GaussianRationalSyntheticDivision (qone qadd_congr qmul_congr qsub_congr)
open GaussianRationalReciprocal (bound_congr bounded_product bounded_sum bounded_negative)
open GaussianRationalPowerDifference (bounded_sum_same)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def source (z R B E T a b c : PTm n) : Fm PTm n :=
  GaussianEulerPowerShiftRate.source z R B E T a b c ⋏ (le one c ⋏ le c b)
def powerCurvature (R E T : PTm n) : PTm n := E*E*
  (GaussianRadiusExponentialLipschitzRate.factor (GaussianEulerPowerShiftRate.radius R E T)*(R+one)+majorant R E T*((R+one)*(R+one)))
def linearBound (R E T : PTm n) : PTm n := majorant R E T*(R+one)*E
def curvature (R E T : PTm n) : PTm n := num 3*powerCurvature R E T+num 3*majorant R E T+num 6*linearBound R E T
def observationCost (R E T : PTm n) : PTm n := num 18+num 20*majorant R E T+num 20*linearBound R E T
def numerator (p R E T b c : PTm n) : PTm n := curvature R E T*c*c*unit p+observationCost R E T*(b*b)
def denominator (p b : PTm n) : PTm n := b*b*unit p

theorem denominator_positive (p b : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx] le one (denominator p b) :=
  positive_product _ _ (positive_product b b hb hb) (unit_positive p)

theorem original_power_error (p z R B E T a b c : PTm n)
    (h : Γ ⊢[PRAAx] source z R B E T a b c) : Γ ⊢[PRAAx]
    bounded (error (point p z B (a+c) b) (point p z B a b) (slopeTerm p z B a b c))
      (powerCurvature R E T*c*c*unit p+num 6*(b*b)) (denominator p b) := by
  have hb := h.andE₁.andE₂.andE₁.andE₁.andE₂
  have hp := unit_positive (Γ := Γ) p
  have raw := GaussianEulerPowerIncrement.compact_power_increment p p z R B E T a b c h.andE₁
  have old := positive_product _ _ (positive_product b b hb hb) (positive_product _ _ hp hp)
  apply bounded_radius_mono _ _ _ _ _ old (denominator_positive p b hb) _ raw
  exact le_of_eq_add (d := zero) (by
    dsimp only [GaussianEulerPowerIncrement.compactNumerator,GaussianEulerPowerIncrement.remainderDenominator,
      GaussianEulerPowerIncrement.curvature,GaussianEulerPowerIncrement.productRemainder,GaussianEulerPowerExponentialShift.coefficient,
      GaussianEulerPowerShiftRate.numerator,powerCurvature,denominator]
    ipra_ring)

theorem original_decay_error (p z R B E T a b c : PTm n)
    (h : Γ ⊢[PRAAx] source z R B E T a b c) : Γ ⊢[PRAAx]
    bounded (error (decay p (a+c) b) (decay p a b) (decayLinear p a b c))
      (num 3*c*c*unit p+num 20*(b*b)) (denominator p b) := by
  have ha := h.andE₁.andE₂.andE₁.andE₁.andE₁
  have hb := h.andE₁.andE₂.andE₁.andE₁.andE₂
  have old := GaussianEulerDecayIncrement.decay_linear_increment a b c b p ha hb h.andE₂.andE₁ hb h.andE₂.andE₂
  have input := (GaussianEulerDecayMesh.observation_numerator_congr (Γ := Γ) _ _ (b*b) p
      (by ipra_ring : Γ ⊢[PRAAx] a*b+c*b ≐ (a+c)*b)).eqTrans
    (GaussianEulerDecayMesh.observation_rescale (a+c) b b p hb hb)
  have canon := GaussianRadiusExponentialName.sample_canonical (Γ := Γ) GaussianGammaCanonicalExponent.constantF
    (GaussianNameBounds.U GaussianGammaCanonicalExponent.constantF (GaussianEulerIntegrandName.decayPoint a b)) p (GaussianEulerIntegrandName.decayPoint a b)
  have rhs : Γ ⊢[PRAAx] qmul (decay p a b) (qadd qone (GaussianEulerIntegrandName.decayPoint c b)) ≐
      qadd (decay p a b) (decayLinear p a b c) :=
    (GaussianRationalCoefficientScaling.qmul_add _ _ _).eqTrans
      (qadd_congr (GaussianReciprocalHorner.qmul_one_right _ canon) (.eqRefl _))
  have near : Γ ⊢[PRAAx] distanceBounded (decay p (a+c) b) (qadd (decay p a b) (decayLinear p a b c))
      (num 3*c*c*unit p+num 20*(b*b)) (denominator p b) :=
    GaussianRationalDistanceOrder.distance_congr input rhs (by unfold GaussianNameRingLaws.three; ipra_ring) (.eqRefl _) old
  exact bound_congr (GaussianEulerPowerShiftRate.displaced_difference _ _ _ (qmul_canonical _ _)).eqSymm (.eqRefl _) (.eqRefl _) near

theorem decay_linear_bound (p a b c : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    bounded (decayLinear p a b c) (num 3*c) b := by
  have time := bound_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point c b hb).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianDominantPairAlgebra.radius_bounded c b hb)
  have neg := bounded_negative _ c b hb time
  exact bound_congr (.eqRefl _) (by unfold GaussianNameRingLaws.three; ipra_ring) (by ipra_ring)
    (bounded_product _ _ _ _ _ _ (le_refl one) hb (GaussianEulerDecayIncrement.decay_observation_uniform_bound a b p ha hb) neg)

theorem original_decay_variation (p z R B E T a b c : PTm n)
    (h : Γ ⊢[PRAAx] source z R B E T a b c) : Γ ⊢[PRAAx]
    bounded (qsub (decay p (a+c) b) (decay p a b)) (num 6*c*b*unit p+num 20*(b*b)) (denominator p b) := by
  let D := denominator p b
  let P := unit p
  let Y := qsub (decay p (a+c) b) (decay p a b)
  let L := decayLinear p a b c
  have hb := h.andE₁.andE₂.andE₁.andE₁.andE₂
  have hD := denominator_positive p b hb
  have lin : Γ ⊢[PRAAx] bounded L (num 3*c*b*P) D := bounded_radius_mono _ _ _ _ _ hb hD
    (le_of_eq_add (d := zero) (by dsimp only [D,P,denominator]; ipra_ring))
    (decay_linear_bound p a b c h.andE₁.andE₂.andE₁.andE₁.andE₁ hb)
  have rem : Γ ⊢[PRAAx] bounded (qsub Y L) (num 3*c*b*P+num 20*(b*b)) D :=
    bounded_radius_mono _ _ _ _ _ hD hD
      (le_congr (by ipra_ring) (by ipra_ring) (add_le_add_right (num 20*(b*b)*D)
        (mul_le_mul_right (num 3*c*P*D) h.andE₂.andE₂))) (original_decay_error p z R B E T a b c h)
  have sum := bounded_sum_same L (qsub Y L) _ _ D hD lin rem
  exact bound_congr (GaussianRationalLinearProduct.add_sub_right L Y (GaussianRationalMetric.qsub_canonical _ _))
    (by ipra_ring) (.eqRefl _) sum

theorem original_power_linear_bound (p z R B E T a b c : PTm n)
    (h : Γ ⊢[PRAAx] source z R B E T a b c) : Γ ⊢[PRAAx]
    bounded (slopeTerm p z B a b c) (linearBound R E T*c) b := by
  have ha := h.andE₁.andE₂.andE₁.andE₁.andE₁
  have hb := h.andE₁.andE₂.andE₁.andE₁.andE₂
  have raw := GaussianEulerPowerExponentIncrement.linear_bound z R B a c h.andE₁.andE₁.andE₁ h.andE₁.andE₁.andE₂.andE₂ ha
  have enlarged : Γ ⊢[PRAAx] bounded (GaussianEulerPowerExponentIncrement.linear z B a c) ((R+one)*E*c) b := bounded_radius_mono _ _ _ _ _ ha hb
    (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right ((R+one)*c) h.andE₁.andE₂.andE₁.andE₂.andE₁)) raw
  exact bound_congr (.eqRefl _) (by unfold linearBound; ipra_ring) (by ipra_ring)
    (bounded_product _ _ _ _ _ _ (le_refl one) hb
      (original_power_observation p z R B E T a b h.andE₁.andE₁ h.andE₁.andE₂.andE₁) enlarged)

/-- The actual original product observations have a genuine uniform
quadratic step residual, with an explicit independent sampling cost. -/
theorem original_product_error (p z R B E T a b c : PTm n)
    (h : Γ ⊢[PRAAx] source z R B E T a b c) : Γ ⊢[PRAAx]
    bounded (productError (point p z B (a+c) b) (point p z B a b) (decay p (a+c) b) (decay p a b)
      (slopeTerm p z B a b c) (decayLinear p a b c)) (numerator p R E T b c) (denominator p b) := by
  let D := denominator p b
  let P := unit p
  let M := majorant R E T
  let L := linearBound R E T
  let K := powerCurvature R E T
  let X := point p z B a b
  let Y := decay p (a+c) b
  let A := slopeTerm p z B a b c
  let V := qsub (decay p (a+c) b) (decay p a b)
  have hb := h.andE₁.andE₂.andE₁.andE₁.andE₂
  have hD := denominator_positive p b hb
  have full := positive_product _ _ hb hD
  have first := bounded_product _ _ _ _ _ _ hD (le_refl one)
    (original_power_error p z R B E T a b c h)
    (GaussianEulerDecayIncrement.decay_observation_uniform_bound (a+c) b p
      (le_trans h.andE₁.andE₂.andE₁.andE₁.andE₁ (le_add_right a c)) hb)
  have f : Γ ⊢[PRAAx] bounded
      (qmul (error (point p z B (a+c) b) X A) Y) ((K*c*c*P+num 6*(b*b))*num 3*b) (b*D) :=
    bounded_radius_mono _ _ _ _ _ (positive_product _ _ hD (le_refl one)) full
      (le_of_eq_add (d := zero) (by unfold GaussianNameRingLaws.three; ipra_ring)) first
  have second := bounded_product _ _ _ _ _ _ (le_refl one) hD
    (original_power_observation p z R B E T a b h.andE₁.andE₁ h.andE₁.andE₂.andE₁)
    (original_decay_error p z R B E T a b c h)
  have g : Γ ⊢[PRAAx] bounded (qmul X (error (decay p (a+c) b) (decay p a b) (decayLinear p a b c)))
      (M*(num 3*c*c*P+num 20*(b*b))*b) (b*D) :=
    bounded_radius_mono _ _ _ _ _ (positive_product _ _ (le_refl one) hD) full
      (le_of_eq_add (d := zero) (by ipra_ring)) second
  have third := bounded_product A V (L*c) b (num 6*c*b*P+num 20*(b*b)) D hb hD
    (original_power_linear_bound p z R B E T a b c h) (original_decay_variation p z R B E T a b c h)
  have sum := bounded_sum_same _ _ _ _ _ full (bounded_sum_same _ _ _ _ _ full f g) third
  have native : Γ ⊢[PRAAx] le
      ((((K*c*c*P+num 6*(b*b))*num 3*b+M*(num 3*c*c*P+num 20*(b*b))*b)+(L*c)*(num 6*c*b*P+num 20*(b*b)))*D)
      (numerator p R E T b c*(b*D)) := by
    dsimp only [numerator,curvature,observationCost,K,L,M,P]
    ipra_le (20*𝔞 (linearBound R E T)*𝔞 b*𝔞 b*𝔞 D)*sl h.andE₂.andE₂
  exact bounded_radius_mono _ _ _ _ _ full hD native
    (bound_congr (GaussianRationalFirstOrderProductError.product_error_identity _ _ _ _ _ _).eqSymm (.eqRefl _) (.eqRefl _) sum)

theorem original_product_increment (p z R B E T a b c : PTm n)
    (h : Γ ⊢[PRAAx] source z R B E T a b c) : Γ ⊢[PRAAx]
    distanceBounded (qsub (originalProduct p z B (a+c) b) (originalProduct p z B a b))
      (productLinear p z B a b c) (numerator p R E T b c) (denominator p b) :=
  original_product_error p z R B E T a b c h

theorem original_Euler_product_uniform_first_order_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      distanceBounded (qsub (originalProduct (var 0) (var 1) (var 3) (var 6+var 8) (var 7))
        (originalProduct (var 0) (var 1) (var 3) (var 6) (var 7)))
        (productLinear (var 0) (var 1) (var 3) (var 6) (var 7) (var 8))
        (numerator (var 0) (var 2) (var 4) (var 5) (var 7) (var 8)) (denominator (var 0) (var 7))) :=
  closeUniv 9 (.impI (original_product_increment _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerIntegrationByPartsProductStep
