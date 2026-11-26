import IPRADerivations.Analysis.Euler.PositiveAxis.LowerBounds.LowTime.GaussianEulerLowTimeReciprocalReference
import IPRADerivations.Analysis.RationalArithmetic.Norms.GaussianSquaredNormUpper

/-!
# Every original lower-time power observation has radius 1/t

The actual reciprocal-square reference is transported through the
original square-name order. The genuine square-to-norm comparison runs
at its real later query, and one finite Euclidean gap removes only that
auxiliary query. The original power observation precision is unchanged.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLowTimePowerBound

open_ipra
open GaussianEulerLowerPowerOrder (source)
open GaussianEulerIntegrandName (powerF powerData powerExponentF powerExponentData powerRadius)
open GaussianEulerUpperPowerCompatibility (squareF squareData)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalReciprocal (bound_congr)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def query (t z B a b : PTm n) : PTm n := GaussianExponentialRealPart.squarePrecision powerF (t+t) (powerData z B a b)
def observation (p z B a b : PTm n) : PTm n := ap2 powerF p (powerData z B a b)
def numerator (p a b : PTm n) : PTm n := b*unit p+a
def denominator (p a : PTm n) : PTm n := a*unit p

theorem squared_order (z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) : Γ ⊢[PRAAx]
    GaussianNamedPositiveExponentialOrder.realOrder squareF GaussianGammaCanonicalExponent.constantF
      (squareData z B a b) (GaussianHarmonicIntegerExponential.rationalPower b a two) :=
  GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _
    (GaussianNameEquivalence.cross_refl squareF _ (GaussianExponentialRealPart.square_regular powerF _
      (GaussianEulerIntegrandName.power_regular z B a b (GaussianEulerLowerPowerComparison.old_source z R B A a b h))))
    (GaussianEulerLowTimeReciprocalReference.exponential_reciprocal_square R a b h.andE₂)
    (GaussianEulerLowTimePowerOrder.original_square_order z R B A a b h)

theorem squared_budget (p t z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) : Γ ⊢[PRAAx]
    GaussianNamedRealOrderTransport.upperSlack (fstT (ap2 squareF p (squareData z B a b)))
      (RationalNonnegativePowers.power b a two) one (unit p) one t := by
  have order := GaussianNamedPositiveExponentialOrder.real_order_at _ _ _ _ p t (squared_order z R B A a b h)
  have right := (congrFst (GaussianGammaCanonicalExponent.constant_at (Γ := Γ) t
    (GaussianHarmonicIntegerExponential.rationalPower b a two))).eqTrans
      ((fst_pair _ _).eqTrans (RationalNormalForm.normalize_fixed_point _
        (RationalNonnegativePowers.power_canonical b a two h.andE₂.andE₁.andE₁)))
  exact RationalValueBounds.upper_congr (.eqRefl _) right (by ipra_ring) (.eqRefl _) order

theorem original_squared_upper (p z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (GaussianRationalMetric.qnormSq
      (ap2 powerF (GaussianExponentialRealPart.squarePrecision powerF p (powerData z B a b)) (powerData z B a b)))
      (RationalNonnegativePowers.power b a two) one (unit p) :=
  RationalValueBounds.upper_congr (GaussianEulerUpperPowerCompatibility.actual_squared_norm_sample p z B a b) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianNamedRealOrderTransport.remove_upper_slack _ _ _ _ one
      (squared_budget p (GaussianNamedRealOrderTransport.precision (fstT (ap2 squareF p (squareData z B a b)))
        (RationalNonnegativePowers.power b a two) (unit p) one) z R B A a b h))

theorem cofinal_bound (t z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) : Γ ⊢[PRAAx]
    bounded (observation (query t z B a b) z B a b) (numerator t a b) (denominator t a) := by
  have s := original_squared_upper (t+t) z R B A a b h
  have e : Γ ⊢[PRAAx] RationalNonnegativePowers.power b a two ≐ RationalNonnegativePowers.power b a (two*one) :=
    (RationalNonnegativePowers.power_at b a two).eqSymm.eqTrans
      ((congrAp3 RationalNonnegativePowers.powerF (.eqRefl _) (.eqRefl _) (by ipra_ring)).eqTrans
        (RationalNonnegativePowers.power_at b a (two*one)))
  have old := GaussianSquaredNormUpper.bound_of_power_squared_upper _ b a one t h.andE₂.andE₁.andE₁
    (RationalValueBounds.upper_congr (.eqRefl _) e (.eqRefl _) (.eqRefl _) s)
  exact bound_congr (.eqRefl _) (congrAdd (congrMul (pw_one b) (.eqRefl _)) (pw_one a))
    (congrMul (pw_one a) (.eqRefl _)) old

theorem original_to_cofinal (p t z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) : Γ ⊢[PRAAx]
    distanceBounded (observation p z B a b) (observation (query t z B a b) z B a b)
      (unit p+unit t) (unit p*unit t) := by
  let s := query t z B a b
  have later : Γ ⊢[PRAAx] le t s := le_trans (le_add_right t t) (le_add_right _ _)
  have growth := GaussianExponentialReference.unit_monotone later
  have old := GaussianNameEquivalence.point_at powerF (powerData z B a b) p s
    (GaussianEulerIntegrandName.power_regular z B a b (GaussianEulerLowerPowerComparison.old_source z R B A a b h))
  have budget : Γ ⊢[PRAAx] le ((unit p+unit s)*(unit p*unit t)) ((unit p+unit t)*(unit p*unit s)) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (add_le_add_right (unit p*unit s*unit t) (mul_le_mul_right (unit p*unit p) growth))
  exact distance_radius_mono _ _ _ _ _ _ (GaussianRationalHorner.positive_product _ _ (unit_positive p) (unit_positive s))
    (GaussianRationalHorner.positive_product _ _ (unit_positive p) (unit_positive t)) budget old

theorem actual_sample_slack (p t z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (observation p z B a b) (numerator p a b) (denominator p a) two t := by
  have den := GaussianRationalHorner.positive_product (Γ := Γ) _ _ h.andE₂.andE₁.andE₁ (unit_positive t)
  have metricden := GaussianRationalHorner.positive_product (Γ := Γ) _ _ (unit_positive p) (unit_positive t)
  have sum := GaussianRationalReciprocal.bounded_sum _ _ _ _ _ _ den metricden
    (cofinal_bound t z R B A a b h) (original_to_cofinal p t z R B A a b h)
  have e := GaussianRationalLinearProduct.add_sub_right (Γ := Γ) (observation (query t z B a b) z B a b)
    (observation p z B a b) (GaussianRadiusExponentialName.sample_canonical powerExponentF (powerRadius z B a b) p (powerExponentData z B a b))
  apply GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (GaussianRationalHorner.positive_product _ _ den metricden)
    (GaussianRationalHorner.positive_product _ _ (GaussianRationalHorner.positive_product _ _ h.andE₂.andE₁.andE₁ (unit_positive p)) (unit_positive t)) _
    (bound_congr e (.eqRefl _) (.eqRefl _) sum)
  exact le_of_eq_add (d := zero) (by unfold numerator denominator unit; ipra_ring)

/-- Every unchanged original power observation has norm at most 1/t+eps. -/
theorem original_power_bound (p z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) : Γ ⊢[PRAAx]
    bounded (ap2 powerF p (powerData z B a b)) (b*unit p+a) (a*unit p) :=
  GaussianRationalSlackRemoval.slack_removal_at _ _ _ two
    (GaussianRationalHorner.positive_product _ _ h.andE₂.andE₁.andE₁ (unit_positive p))
    (actual_sample_slack p (GaussianRationalSlackRemoval.precision (observation p z B a b)
      (numerator p a b) (denominator p a) two) z R B A a b h)

theorem original_low_time_reciprocal_power_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      bounded (ap2 powerF (var 0) (powerData (var 1) (var 3) (var 5) (var 6)))
        ((var 6)*unit (var 0)+(var 5)) ((var 5)*unit (var 0))) :=
  closeUniv 7 (.impI (original_power_bound _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerLowTimePowerBound
