import IPRADerivations.Analysis.Euler.PositiveAxis.LowerBounds.GaussianEulerLowerRationalPowerReference
import IPRADerivations.Analysis.RationalArithmetic.Norms.GaussianSquaredNormUpper

/-!
# Sharp original lower-time power bound at t=(a/b)^A

The actual original power square is ordered below its proved rational
reference (b/a)^(2 pred A). The checked finite square-to-norm comparison
is used at the genuine later square clock, then original power-name
regularity and one finite Euclidean gap query preserve every requested
original precision p. No transformed input or target magnitude law is
assumed as a premise.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLowerTransformedPower

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerLowerPowerOrder (source)
open GaussianEulerLowerPowerRebasing (exponent)
open GaussianEulerIntegrandName (powerF powerExponentF powerExponentData powerRadius)
open GaussianEulerUpperPowerCompatibility (squareF squareData)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalReciprocal (bound_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (z B A a b : PTm n) : PTm n := GaussianEulerIntegrandName.powerData z B (pw a A) (pw b A)
def observation (p z B A a b : PTm n) : PTm n := ap2 powerF p (data z B A a b)
def query (t z B A a b : PTm n) : PTm n := GaussianExponentialRealPart.squarePrecision powerF (t+t) (data z B A a b)
def numerator (p A a b : PTm n) : PTm n := pw b (pred A)*unit p+pw a (pred A)
def denominator (p A a : PTm n) : PTm n := pw a (pred A)*unit p
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (z B A a b : PTm n) :
    Syn.subst σ (data z B A a b) = data (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ a) (Syn.subst σ b) := by simp [data]
@[simp] theorem subst_observation {m : ℕ} (σ : Fin n → PTm m) (p z B A a b : PTm n) :
    Syn.subst σ (observation p z B A a b) = observation (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ a) (Syn.subst σ b) := by simp [observation]
@[simp] theorem subst_query {m : ℕ} (σ : Fin n → PTm m) (t z B A a b : PTm n) :
    Syn.subst σ (query t z B A a b) = query (Syn.subst σ t) (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ a) (Syn.subst σ b) := by simp [query]

theorem reference_source (z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) : Γ ⊢[PRAAx]
    GaussianEulerLowerRationalPowerReference.source A a b := .andI h.andE₁.andE₁ h.andE₂

theorem powered_source (z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) : Γ ⊢[PRAAx]
    source z R B A (pw a A) (pw b A) :=
  .andI h.andE₁ (GaussianEulerLowerRationalPowerReference.powered_time_source A a b (reference_source z R B A a b h))

theorem old_source (z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) : Γ ⊢[PRAAx]
    GaussianEulerIntegrandName.source z B (pw a A) (pw b A) :=
  GaussianEulerLowerPowerComparison.old_source z R B A _ _ (powered_source z R B A a b h)

theorem squared_order (z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) : Γ ⊢[PRAAx]
    GaussianNamedPositiveExponentialOrder.realOrder squareF GaussianGammaCanonicalExponent.constantF
      (squareData z B (pw a A) (pw b A)) (GaussianHarmonicIntegerExponential.rationalPower b a (exponent A)) :=
  GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _
    (GaussianNameEquivalence.cross_refl squareF _ (GaussianExponentialRealPart.square_regular powerF _
      (GaussianEulerIntegrandName.power_regular z B _ _ (old_source z R B A a b h))))
    (GaussianEulerLowerRationalPowerReference.exponential_rational_power R A a b (reference_source z R B A a b h))
    (GaussianEulerLowerPowerComparison.original_square_order z R B A _ _ (powered_source z R B A a b h))

theorem squared_budget (p t z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) : Γ ⊢[PRAAx]
    GaussianNamedRealOrderTransport.upperSlack (fstT (ap2 squareF p (squareData z B (pw a A) (pw b A))))
      (RationalNonnegativePowers.power b a (exponent A)) one (unit p) one t := by
  have order := GaussianNamedPositiveExponentialOrder.real_order_at _ _ _ _ p t (squared_order z R B A a b h)
  have right := (congrFst (GaussianGammaCanonicalExponent.constant_at (Γ := Γ) t
    (GaussianHarmonicIntegerExponential.rationalPower b a (exponent A)))).eqTrans
      ((fst_pair _ _).eqTrans (RationalNormalForm.normalize_fixed_point _
        (RationalNonnegativePowers.power_canonical b a (exponent A) h.andE₂.andE₁.andE₁)))
  exact RationalValueBounds.upper_congr (.eqRefl _) right (by ipra_ring) (.eqRefl _) order

theorem original_squared_upper (p z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (GaussianRationalMetric.qnormSq
      (ap2 powerF (GaussianExponentialRealPart.squarePrecision powerF p (data z B A a b)) (data z B A a b)))
      (RationalNonnegativePowers.power b a (two*pred A)) one (unit p) :=
  RationalValueBounds.upper_congr (GaussianEulerUpperPowerCompatibility.actual_squared_norm_sample p z B (pw a A) (pw b A)) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianNamedRealOrderTransport.remove_upper_slack _ _ _ _ one
      (squared_budget p (GaussianNamedRealOrderTransport.precision (fstT (ap2 squareF p (squareData z B (pw a A) (pw b A))))
        (RationalNonnegativePowers.power b a (exponent A)) (unit p) one) z R B A a b h))

theorem denominator_positive (p A a : PTm n) (ha : Γ ⊢[PRAAx] le one a) : Γ ⊢[PRAAx] le one (denominator p A a) :=
  GaussianRationalHorner.positive_product _ _ (RationalNonnegativePowers.denominator_positive a (pred A) ha) (unit_positive p)

theorem query_later (t z B A a b : PTm n) : Γ ⊢[PRAAx] le t (query t z B A a b) :=
  le_trans (le_add_right t t) (le_add_right _ _)

theorem cofinal_bound (t z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) : Γ ⊢[PRAAx]
    bounded (observation (query t z B A a b) z B A a b) (numerator t A a b) (denominator t A a) :=
  GaussianSquaredNormUpper.bound_of_power_squared_upper _ b a (pred A) t h.andE₂.andE₁.andE₁
    (original_squared_upper (t+t) z R B A a b h)

theorem original_to_cofinal (p t z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) : Γ ⊢[PRAAx]
    distanceBounded (observation p z B A a b) (observation (query t z B A a b) z B A a b)
      (unit p+unit t) (unit p*unit t) := by
  let s := query t z B A a b
  have growth := GaussianExponentialReference.unit_monotone (query_later (Γ := Γ) t z B A a b)
  have old := GaussianNameEquivalence.point_at powerF (data z B A a b) p s
    (GaussianEulerIntegrandName.power_regular z B _ _ (old_source z R B A a b h))
  have budget : Γ ⊢[PRAAx] le ((unit p+unit s)*(unit p*unit t)) ((unit p+unit t)*(unit p*unit s)) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (add_le_add_right (unit p*unit s*unit t) (mul_le_mul_right (unit p*unit p) growth))
  exact distance_radius_mono _ _ _ _ _ _ (GaussianRationalHorner.positive_product _ _ (unit_positive p) (unit_positive s))
    (GaussianRationalHorner.positive_product _ _ (unit_positive p) (unit_positive t)) budget old

theorem actual_sample_slack (p t z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (observation p z B A a b) (numerator p A a b) (denominator p A a) two t := by
  have den := denominator_positive t A a h.andE₂.andE₁.andE₁
  have metricden := GaussianRationalHorner.positive_product (Γ := Γ) _ _ (unit_positive p) (unit_positive t)
  have sum := GaussianRationalReciprocal.bounded_sum _ _ _ _ _ _ den metricden
    (cofinal_bound t z R B A a b h) (original_to_cofinal p t z R B A a b h)
  have e := GaussianRationalLinearProduct.add_sub_right (Γ := Γ) (observation (query t z B A a b) z B A a b)
    (observation p z B A a b) (GaussianRadiusExponentialName.sample_canonical powerExponentF (powerRadius z B (pw a A) (pw b A)) p
      (powerExponentData z B (pw a A) (pw b A)))
  apply GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (GaussianRationalHorner.positive_product _ _ den metricden)
    (GaussianRationalHorner.positive_product _ _ (denominator_positive p A a h.andE₂.andE₁.andE₁) (unit_positive t)) _
    (bound_congr e (.eqRefl _) (.eqRefl _) sum)
  exact le_of_eq_add (d := zero) (by unfold numerator denominator unit; ipra_ring)

/-- At t=(a/b)^A, every original Euler power observation has norm at
most (b/a)^(A-1)+2^-p, with its original requested precision preserved. -/
theorem original_power_bound (p z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) : Γ ⊢[PRAAx]
    bounded (ap2 powerF p (GaussianEulerIntegrandName.powerData z B (pw a A) (pw b A)))
      (pw b (pred A)*unit p+pw a (pred A)) (pw a (pred A)*unit p) :=
  GaussianRationalSlackRemoval.slack_removal_at _ _ _ two (denominator_positive p A a h.andE₂.andE₁.andE₁)
    (actual_sample_slack p (GaussianRationalSlackRemoval.precision (observation p z B A a b) (numerator p A a b)
      (denominator p A a) two) z R B A a b h)

theorem original_lower_tail_transformed_power_norm_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      bounded (ap2 powerF (var 0) (GaussianEulerIntegrandName.powerData (var 1) (var 3) (pw (var 5) (var 4)) (pw (var 6) (var 4))))
        (pw (var 6) (pred (var 4))*unit (var 0)+pw (var 5) (pred (var 4))) (pw (var 5) (pred (var 4))*unit (var 0))) :=
  closeUniv 7 (.impI (original_power_bound _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerLowerTransformedPower
