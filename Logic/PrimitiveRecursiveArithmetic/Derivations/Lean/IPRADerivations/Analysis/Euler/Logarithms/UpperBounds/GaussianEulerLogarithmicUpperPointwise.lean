import IPRADerivations.Analysis.Euler.Logarithms.GaussianEulerLogarithmicHalfDecay
import IPRADerivations.Analysis.Euler.Logarithms.GaussianEulerLogarithmicCompactName
import IPRADerivations.Analysis.Euler.Integration.Parts.GaussianEulerIntegrationByPartsObservation
import IPRADerivations.Analysis.Euler.PositiveAxis.UpperBounds.GaussianEulerUpperTailPointwise

/-!
# Original logarithmic Euler rows above time one

The actual compact logarithmic evaluator is bounded by the unchanged
nonnegative half-decay reference, with degree R+j and its exact factorial
coefficient. All auxiliary observation losses are removed by one finite
rational gap. The requested evaluator and reference precisions remain
independent, and no derivative-integral or upper-tail output law is used.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicUpperPointwise

open_ipra
open GaussianEulerIntegrandName (powerF powerData decayF decayData)
open GaussianEulerWeightedHalfDecay (majorant halfSample)
open GaussianEulerLogarithmicHalfDecay (powerAndLog powerAllowance halfAllowance weightedSample)
open GaussianEulerUpperTailPointwise (referenceTop referenceBottom majorantTop majorantBottom
  reference_bottom_positive majorant_bottom_positive)
open GaussianEulerHalfDecayReference (scalar numerator denominator denominator_positive reference_norm decay_reference_error)
open GaussianEulerLogarithmicMultiplier (logarithmicPower)
open GaussianEulerCompactPowerMajorant (original_power_observation)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalReciprocal (bounded_product bound_congr)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_radius_mono distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianReciprocalHorner (qmul_associative)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianReconstructionRoots (norm_from_distance)
open GaussianRationalSlackRemoval (slack slack_removal_at)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

abbrev powerMajorant (R E T : PTm n) : PTm n := GaussianEulerCompactPowerMajorant.majorant R E T

def source (z R B E T a b : PTm n) : Fm PTm n :=
  GaussianEulerLogarithmicMultiplier.source z R B E T a b ⋏ le b a
def splitRow (p j z B a b : PTm n) : PTm n := qmul (weightedSample p j z B a b) (halfSample p a b)
def splittingCost (j R E T a : PTm n) : PTm n := pw (a+one) j*(num 15*powerMajorant R E T+num 4)
def referenceCost (q j R a b : PTm n) : PTm n := majorant (R+j)+
  halfAllowance a (R+j) (powerAllowance j R a)*(referenceTop q a b+one)
def rawCost (q j R E T a b : PTm n) : PTm n := referenceCost q j R a b+splittingCost j R E T a
def observationCost (q j R E T a b : PTm n) : PTm n :=
  GaussianEulerLogarithmicMultiplier.observationCost j R E T+rawCost q j R E T a b

theorem upper_source (z R B E T a b : PTm n) (h : Γ ⊢[PRAAx] source z R B E T a b) :
    Γ ⊢[PRAAx] GaussianEulerUpperPowerOrder.source z R B a b :=
  .andI (.andI h.andE₁.andE₁.andE₁ h.andE₁.andE₁.andE₂.andE₂)
    (.andI h.andE₁.andE₂.andE₁ h.andE₂)

private theorem exchange (x y z : PTm n) : Γ ⊢[PRAAx] qmul (qmul x y) z ≐ qmul (qmul x z) y :=
  (qmul_associative x y z).eqTrans
    ((qmul_congr (.eqRefl _) (qmul_commutative y z)).eqTrans (qmul_associative x z y).eqSymm)

theorem half_square_error (p a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] distanceBounded (ap2 decayF p (decayData a b))
      (qmul (halfSample p a b) (halfSample p a b)) (num 14) (unit p) :=
  distance_congr (congrAp2 decayF (.eqRefl p) (GaussianEulerHalfDecayProduct.doubled_decay_input a b hb))
    (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianEulerDecayIncrement.decay_product_observation a (two*b) a (two*b) p ha
      (positive_product _ _ (le_succ_self one) hb) ha (positive_product _ _ (le_succ_self one) hb))

/-- The full normalized Euler factor is compared with literal old power
and two half-decay observations, at the same original precision. -/
theorem original_split_error (p j z R B E T a b : PTm n)
    (h : Γ ⊢[PRAAx] source z R B E T a b) : Γ ⊢[PRAAx]
    distanceBounded (GaussianEulerLogarithmicMultiplier.sample p j z B a b)
      (splitRow p j z B a b) (splittingCost j R E T a) (unit p) := by
  let P := ap2 powerF p (powerData z B a b)
  let L := logarithmicPower p j a b
  let D := ap2 decayF p (decayData a b)
  let H := halfSample p a b
  let J := pw (a+one) j
  let M := powerMajorant R E T
  have up := unit_positive (Γ := Γ) p
  have lb : Γ ⊢[PRAAx] bounded L J one :=
    GaussianRationalPowerDifference.bounded_power_integer _ _ j
      (GaussianUpperTimeLogarithmPower.original_uniform_bound p a b h.andE₁.andE₂.andE₁ h.andE₂)
  have pb : Γ ⊢[PRAAx] bounded P M one :=
    original_power_observation p z R B E T a b h.andE₁.andE₁ h.andE₁.andE₂
  have euler : Γ ⊢[PRAAx] distanceBounded (GaussianEulerIntegrandName.sample p z B a b)
      (qmul P D) (M+num 4) (unit p) :=
    distance_congr (.eqRefl _) (.eqRefl _)
      (by unfold GaussianEulerIntegrationByPartsObservation.factor; dsimp only [M,powerMajorant]; ipra_ring)
      (.eqRefl _) (GaussianEulerIntegrationByPartsObservation.original_diagonal p z R B E T a b h.andE₁)
  have first := GaussianApproximateInverseDistance.multiply_distance L (GaussianEulerIntegrandName.sample p z B a b)
    (qmul P D) J (M+num 4) (unit p) up lb euler
  have first' : Γ ⊢[PRAAx] distanceBounded (GaussianEulerLogarithmicMultiplier.sample p j z B a b)
      (qmul (qmul P L) D) (J*(M+num 4)) (unit p) :=
    distance_congr (qmul_commutative _ _) ((qmul_commutative L _).eqTrans (exchange P D L))
      (.eqRefl _) (.eqRefl _) first
  have coeff : Γ ⊢[PRAAx] bounded (qmul P L) (M*J) one :=
    bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring)
      (bounded_product P L M one J one (le_refl one) (le_refl one) pb lb)
  have second := GaussianApproximateInverseDistance.multiply_distance (qmul P L) D (qmul H H)
    (M*J) (num 14) (unit p) up coeff
    (half_square_error p a b h.andE₁.andE₂.andE₁.andE₁ h.andE₁.andE₂.andE₁.andE₂)
  have second' : Γ ⊢[PRAAx] distanceBounded (qmul (qmul P L) D)
      (splitRow p j z B a b) (M*J*num 14) (unit p) :=
    distance_congr (.eqRefl _) (qmul_associative (qmul P L) H H).eqSymm (.eqRefl _) (.eqRefl _) second
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold splittingCost; dsimp only [J,M]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ up first' second')

theorem half_reference_bound (q p a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] bounded (halfSample p a b)
      (referenceTop q a b*unit p+referenceBottom q a b) (referenceBottom q a b*unit p) := by
  have den : Γ ⊢[PRAAx] le one (unit q*unit p) := positive_product _ _ (unit_positive q) (unit_positive p)
  have near := distance_symmetric _ _ _ _ den (decay_reference_error q p a b hb)
  have estimate := norm_from_distance _ _ _ _ (numerator q a b) (denominator q a b)
    den (denominator_positive q a b) near (reference_norm q a b)
  exact bound_congr (.eqRefl _) (by unfold referenceTop referenceBottom; ipra_ring)
    (by unfold referenceBottom; ipra_ring) estimate

theorem approximate_reference_product (x y M K N D U : PTm n)
    (hd : Γ ⊢[PRAAx] le one D) (hu : Γ ⊢[PRAAx] le one U)
    (hx : Γ ⊢[PRAAx] bounded x (M*U+K) U)
    (hy : Γ ⊢[PRAAx] bounded y (N*U+D) (D*U)) : Γ ⊢[PRAAx]
    bounded (qmul x y) (M*N*U+(M+K*(N+one))*D) (D*U) := by
  have du := positive_product _ _ hd hu
  have compare : Γ ⊢[PRAAx] le ((M*U+K)*(N*U+D)) ((M*N*U+(M+K*(N+one))*D)*U) := by
    ipra_le (𝔞 K*𝔞 N*𝔞 U)*sl hd+(𝔞 K*𝔞 D)*sl hu
  have reorder : Γ ⊢[PRAAx] ((M*N*U+(M+K*(N+one))*D)*U)*(D*U) ≐
      (M*N*U+(M+K*(N+one))*D)*(U*(D*U)) := by ipra_ring
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ hu du) du
    (le_congr (.eqRefl _) reorder (mul_le_mul_right (D*U) compare))
    (bounded_product x y _ _ _ _ hu du hx hy)

theorem original_raw_envelope (p q j z R B E T a b : PTm n)
    (h : Γ ⊢[PRAAx] source z R B E T a b) : Γ ⊢[PRAAx]
    bounded (GaussianEulerLogarithmicMultiplier.sample p j z B a b)
      (majorant (R+j)*referenceTop q a b*unit p+rawCost q j R E T a b*referenceBottom q a b)
      (referenceBottom q a b*unit p) := by
  let M := majorant (R+j)
  let N := referenceTop q a b
  let D := referenceBottom q a b
  let K := referenceCost q j R a b
  let C := splittingCost j R E T a
  let U := unit p
  have du : Γ ⊢[PRAAx] le one (D*U) := positive_product _ _ (reference_bottom_positive q a b) (unit_positive p)
  have split : Γ ⊢[PRAAx] bounded (splitRow p j z B a b) (M*N*U+K*D) (D*U) :=
    approximate_reference_product _ _ M (halfAllowance a (R+j) (powerAllowance j R a)) N D U
      (reference_bottom_positive q a b) (unit_positive p)
      (GaussianEulerLogarithmicHalfDecay.original_weighted_half_decay_bound p j z R B a b (upper_source z R B E T a b h))
      (half_reference_bound q p a b h.andE₁.andE₂.andE₁.andE₂)
  have bound := norm_from_distance _ _ C U (M*N*U+K*D) (D*U) (unit_positive p) du
    (original_split_error p j z R B E T a b h) split
  have compare : Γ ⊢[PRAAx] le ((C*(D*U)+(M*N*U+K*D)*U)*(D*U))
      ((M*N*U+(K+C)*D)*(U*(D*U))) :=
    le_of_eq_add (d := zero) (by ipra_ring)
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ (unit_positive p) du) du compare bound

theorem original_observation_slack (p q s j z R B E T a b : PTm n)
    (h : Γ ⊢[PRAAx] source z R B E T a b) : Γ ⊢[PRAAx]
    slack (GaussianEulerLogarithmicCompactName.sample p j R E T z B a b)
      (majorantTop p q (R+j) a b) (majorantBottom p q a b) (observationCost q j R E T a b) s := by
  let P := GaussianEulerLogarithmicCompactName.query p j R E T
  let U := unit p
  let V := unit s
  let W := unit P
  let D := referenceBottom q a b
  let A := majorant (R+j)*referenceTop q a b
  let H := GaussianEulerLogarithmicMultiplier.observationCost j R E T
  let K := rawCost q j R E T a b
  have up := unit_positive (Γ := Γ) p
  have us := unit_positive (Γ := Γ) s
  have uP := unit_positive (Γ := Γ) P
  have same : Γ ⊢[PRAAx] GaussianEulerExponentCompactBounds.input z R B E T a b a b zero one :=
    .andI h.andE₁.andE₁ (.andI h.andE₁.andE₂ (.andI h.andE₁.andE₂
      (.andI (le_refl one) (GaussianRationalPowerDifference.distance_refl_zero _ one (le_refl one)))))
  have raw := GaussianEulerLogarithmicMultiplier.original_variation P s j z R B E T a b a b zero one same
  have raw' : Γ ⊢[PRAAx] distanceBounded (GaussianEulerLogarithmicCompactName.sample p j R E T z B a b)
      (GaussianEulerLogarithmicMultiplier.sample s j z B a b) (H*(W+V)) (W*V) :=
    distance_congr (.eqRefl _) (.eqRefl _)
      (by unfold GaussianEulerLogarithmicMultiplier.numerator; dsimp only [H,W,V]; ipra_ring)
      (by unfold GaussianNamedInverseRate.rateDenominator; dsimp only [W,V]; ipra_ring) raw
  have old : Γ ⊢[PRAAx] le one (W*V) := positive_product _ _ uP us
  have next : Γ ⊢[PRAAx] le one (U*V) := positive_product _ _ up us
  have near : Γ ⊢[PRAAx] distanceBounded (GaussianEulerLogarithmicCompactName.sample p j R E T z B a b)
      (GaussianEulerLogarithmicMultiplier.sample s j z B a b) (V+H*U) (U*V) :=
    distance_radius_mono _ _ _ _ _ _ old next
      (by dsimp only [H,U,V,W,P]
          ipra_le (𝔞(unit s)*𝔞(unit s))*sl (GaussianEulerLogarithmicCompactName.query_budget (Γ := Γ) p j R E T)) raw'
  have base : Γ ⊢[PRAAx] bounded (GaussianEulerLogarithmicMultiplier.sample s j z B a b)
      (A*V+K*D) (D*V) := original_raw_envelope s q j z R B E T a b h
  have dv := positive_product _ _ (reference_bottom_positive q a b) us
  have bound := norm_from_distance _ _ (V+H*U) (U*V) (A*V+K*D) (D*V) next dv near base
  have finalden := positive_product _ _ (majorant_bottom_positive p q a b) us
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ next dv) finalden
    (le_of_eq_add (d := zero) (by
      unfold majorantTop majorantBottom observationCost
      dsimp only [A,D,U,V,H,K]
      unfold unit
      ipra_ring)) bound

/-- The genuine compact log-power evaluator has the same sharp half-decay
coefficient, with only its requested observation error remaining. -/
theorem original_upper_pointwise (p q j z R B E T a b : PTm n)
    (h : Γ ⊢[PRAAx] source z R B E T a b) : Γ ⊢[PRAAx]
    bounded (GaussianEulerLogarithmicCompactName.sample p j R E T z B a b)
      (majorantTop p q (R+j) a b) (majorantBottom p q a b) :=
  slack_removal_at _ _ _ (observationCost q j R E T a b) (majorant_bottom_positive p q a b)
    (original_observation_slack p q _ j z R B E T a b h)

theorem original_logarithmic_Euler_upper_pointwise_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (source (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ⟶
      bounded (GaussianEulerLogarithmicCompactName.sample (var 0) (var 2) (var 4) (var 6) (var 7) (var 3) (var 5) (var 8) (var 9))
        (majorantTop (var 0) (var 1) (var 4+var 2) (var 8) (var 9)) (majorantBottom (var 0) (var 1) (var 8) (var 9))) :=
  closeUniv 10 (.impI (original_upper_pointwise _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicUpperPointwise
