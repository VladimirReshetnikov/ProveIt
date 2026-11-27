import IPRADerivations.Analysis.Euler.PositiveAxis.UpperBounds.GaussianEulerUpperPowerCompatibility
import IPRADerivations.Analysis.RationalArithmetic.Norms.GaussianBounds.GaussianSquaredNormUpper

/-!
# The actual upper-time Euler power has the paper norm majorant

The checked squared comparison is first used at the genuine square-name
clock of precision t+t. Original power-name regularity compares this
sample with ANY requested original sample p. One computed finite
Euclidean gap query removes the auxiliary t error, leaving precisely
t^R+2^-p at the unchanged original observation p.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUpperPowerBound

open_ipra
open GaussianEulerUpperPowerOrder (source)
open GaussianEulerIntegrandName (powerF powerData powerExponentF powerExponentData powerRadius)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalReciprocal (bound_congr)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def query (t z B a b : PTm n) : PTm n := GaussianExponentialRealPart.squarePrecision powerF (t+t) (powerData z B a b)
def observation (p z B a b : PTm n) : PTm n := ap2 powerF p (powerData z B a b)
def numerator (p R a b : PTm n) : PTm n := pw a R*unit p+pw b R
def denominator (p R b : PTm n) : PTm n := pw b R*unit p
ipra_subst query
ipra_subst observation
ipra_subst numerator
ipra_subst denominator

theorem denominator_positive (p R b : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    le one (denominator p R b) := GaussianRationalHorner.positive_product _ _
      (RationalNonnegativePowers.denominator_positive b R hb) (unit_positive p)

theorem query_later (t z B a b : PTm n) : Γ ⊢[PRAAx] le t (query t z B a b) :=
  le_trans (le_add_right t t) (le_add_right _ _)

theorem cofinal_bound (t z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    bounded (observation (query t z B a b) z B a b) (numerator t R a b) (denominator t R b) :=
  GaussianSquaredNormUpper.bound_of_power_squared_upper _ a b R t h.andE₂.andE₁.andE₂
    (GaussianEulerUpperPowerCompatibility.original_power_squared_upper (t+t) z R B a b h)

theorem original_to_cofinal (p t z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    distanceBounded (observation p z B a b) (observation (query t z B a b) z B a b)
      (unit p+unit t) (unit p*unit t) := by
  let s := query t z B a b
  have growth := GaussianExponentialReference.unit_monotone (query_later (Γ := Γ) t z B a b)
  have old := GaussianNameEquivalence.point_at powerF (powerData z B a b) p s
    (GaussianEulerIntegrandName.power_regular z B a b (GaussianEulerUpperPowerCompatibility.old_source z R B a b h))
  have budget : Γ ⊢[PRAAx] le ((unit p+unit s)*(unit p*unit t)) ((unit p+unit t)*(unit p*unit s)) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (add_le_add_right (unit p*unit s*unit t) (mul_le_mul_right (unit p*unit p) growth))
  exact distance_radius_mono _ _ _ _ _ _ (GaussianRationalHorner.positive_product _ _ (unit_positive p) (unit_positive s))
    (GaussianRationalHorner.positive_product _ _ (unit_positive p) (unit_positive t)) budget old

theorem actual_sample_slack (p t z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (observation p z B a b) (numerator p R a b) (denominator p R b) two t := by
  have den := denominator_positive t R b h.andE₂.andE₁.andE₂
  have metricden := GaussianRationalHorner.positive_product (Γ := Γ) _ _ (unit_positive p) (unit_positive t)
  have sum := GaussianRationalReciprocal.bounded_sum _ _ _ _ _ _ den metricden
    (cofinal_bound t z R B a b h) (original_to_cofinal p t z R B a b h)
  have e := GaussianRationalLinearProduct.add_sub_right (Γ := Γ) (observation (query t z B a b) z B a b)
    (observation p z B a b) (GaussianRadiusExponentialName.sample_canonical powerExponentF (powerRadius z B a b) p (powerExponentData z B a b))
  apply GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (GaussianRationalHorner.positive_product _ _ den metricden)
    (GaussianRationalHorner.positive_product _ _ (denominator_positive p R b h.andE₂.andE₁.andE₂) (unit_positive t)) _
    (bound_congr e (.eqRefl _) (.eqRefl _) sum)
  exact le_of_eq_add (d := zero) (by unfold numerator denominator unit; ipra_ring)

/-- Every unchanged original power observation satisfies the exact paper
upper-time magnitude with its one permitted observation error. -/
theorem original_power_bound (p z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    bounded (observation p z B a b) (pw a R*unit p+pw b R) (pw b R*unit p) :=
  GaussianRationalSlackRemoval.slack_removal_at _ _ _ two (denominator_positive p R b h.andE₂.andE₁.andE₂)
    (actual_sample_slack p (GaussianRationalSlackRemoval.precision (observation p z B a b) (numerator p R a b)
      (denominator p R b) two) z R B a b h)

theorem original_upper_tail_actual_power_norm_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      bounded (ap2 powerF (var 0) (powerData (var 1) (var 3) (var 4) (var 5)))
        (pw (var 4) (var 2)*unit (var 0)+pw (var 5) (var 2)) (pw (var 5) (var 2)*unit (var 0))) :=
  closeUniv 6 (.impI (original_power_bound _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerUpperPowerBound
