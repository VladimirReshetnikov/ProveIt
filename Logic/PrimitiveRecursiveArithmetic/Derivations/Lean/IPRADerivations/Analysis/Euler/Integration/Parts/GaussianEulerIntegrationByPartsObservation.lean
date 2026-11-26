import IPRADerivations.Analysis.Euler.Integration.Parts.GaussianEulerIntegrationByPartsLinear
import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerDecayQuadraturePrecision

/-!
# Original normalized Euler observations versus literal power times decay

The actual multiplication query is retained. Original power and decay
regularity compare that query to the requested raw product observation.
The existing exponential-addition identity compares the normalized
product with the unchanged Euler evaluator. An auxiliary precision is
removed by a finite rational gap, leaving explicit independent errors
with a constant uniform on the original compact time interval.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIntegrationByPartsObservation

open_ipra
open GaussianEulerIntegrationByPartsLinear (originalProduct decay)
open GaussianEulerIntegrandName (powerF powerData decayF decayData productF productData nameF data sample)
open GaussianEulerCompactPowerMajorant (majorant original_power_observation)
open GaussianCompactLogarithmBounds (domain)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (positive_product qmul qmul_canonical)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def source (z R B E T a b : PTm n) : Fm PTm n := GaussianEulerExponentCompactBounds.source z R B E ⋏ domain a b E T
def factor (R E T : PTm n) : PTm n := majorant R E T+num 3
def query (t z B a b : PTm n) : PTm n := GaussianFastValueCut.exponent
  (GaussianNameArithmetic.multiplyModulus powerF decayF (powerData z B a b) (decayData a b)) t
def numerator (p q R E T : PTm n) : PTm n := factor R E T*unit q+unit p
def denominator (p q : PTm n) : PTm n := unit p*unit q
def auxiliaryCost (R E T : PTm n) : PTm n := factor R E T+one

theorem original_product_at (t z B a b : PTm n) : Γ ⊢[PRAAx]
    ap2 productF t (productData z B a b) ≐ originalProduct (query t z B a b) z B a b :=
  (GaussianNameArithmetic.multiply_at powerF decayF _ _ t).eqTrans
    (GaussianExponentialReference.recode_fixed _ (qmul_canonical _ _))

/-- The original multiplication clock is never replaced by the requested
clock. CN compares them using their actual independent dyadic errors. -/
theorem normalized_product_observation (p t z R B E T a b : PTm n)
    (h : Γ ⊢[PRAAx] source z R B E T a b) : Γ ⊢[PRAAx]
    distanceBounded (originalProduct p z B a b) (ap2 productF t (productData z B a b))
      (factor R E T*(unit p+unit t)) (unit p*unit t) := by
  let s := query t z B a b
  let P := unit p
  let U := unit t
  let S := unit s
  let M := majorant R E T
  have hs := unit_positive (Γ := Γ) s
  have hp := unit_positive (Γ := Γ) p
  have ht := unit_positive (Γ := Γ) t
  have old := positive_product _ _ hs hp
  have next := positive_product _ _ hp ht
  have power := GaussianEulerIntegrandName.power_regular z B a b (.andI h.andE₁.andE₁ h.andE₂.andE₁)
  have decayCN := GaussianEulerDecayQuadraturePrecision.observation_regular (Γ := Γ) a b
  have powerNear := GaussianNameEquivalence.point_at powerF (powerData z B a b) s p power
  have decayNear := GaussianNameEquivalence.point_at decayF (decayData a b) s p decayCN
  have bounds := GaussianNameArithmetic.product_distance _ _ _ _ _ _ _ GaussianNameRingLaws.three M old powerNear decayNear
    (GaussianEulerDecayIncrement.decay_observation_uniform_bound a b s h.andE₂.andE₁.andE₁ h.andE₂.andE₁.andE₂)
    (original_power_observation p z R B E T a b h.andE₁ h.andE₂)
  have grow : Γ ⊢[PRAAx] le U S := GaussianExponentialReference.unit_monotone (le_add_right _ _)
  have native : Γ ⊢[PRAAx] le (((S+P)*GaussianNameRingLaws.three+M*(S+P))*(P*U))
      ((factor R E T*(P+U))*(S*P)) := by
    unfold factor GaussianNameRingLaws.three
    ipra_le ((𝔞 M+3)*𝔞 P*𝔞 P)*sl grow
  have near := distance_radius_mono _ _ _ _ _ _ old next native bounds
  exact distance_congr (.eqRefl _) (original_product_at t z B a b).eqSymm (.eqRefl _) (.eqRefl _)
    (distance_symmetric _ _ _ _ next near)

theorem original_auxiliary_slack (p q t z R B E T a b : PTm n)
    (h : Γ ⊢[PRAAx] source z R B E T a b) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (qsub (originalProduct p z B a b) (sample q z B a b))
      (numerator p q R E T) (denominator p q) (auxiliaryCost R E T) t := by
  let P := unit p
  let Q := unit q
  let U := unit t
  let D := P*Q*U
  have hp := unit_positive (Γ := Γ) p
  have hq := unit_positive (Γ := Γ) q
  have ht := unit_positive (Γ := Γ) t
  have dp := positive_product _ _ hp ht
  have dq := positive_product _ _ ht hq
  have dd := positive_product _ _ (positive_product _ _ hp hq) ht
  have first := distance_radius_mono _ _ _ _ (factor R E T*(P+U)*Q) D dp dd
    (le_of_eq_add (d := zero) (by dsimp only [D,P,Q,U]; ipra_ring))
    (normalized_product_observation p t z R B E T a b h)
  have near := GaussianNameEquivalence.cross_at _ _ _ _ t q
    (GaussianEulerIntegrandName.original_power_times_decay z B a b (.andI h.andE₁.andE₁ h.andE₂.andE₁))
  have second := distance_radius_mono _ _ _ _ ((U+Q)*P) D dq dd
    (le_of_eq_add (d := zero) (by dsimp only [D,P,Q,U]; ipra_ring)) near
  have joined := distance_triangle_same _ _ _ _ _ _ dd first second
  exact GaussianRationalReciprocal.bound_congr
    (GaussianRationalSyntheticDivision.qsub_congr (.eqRefl _) (GaussianEulerIntegrandName.sample_at q z B a b)).eqSymm
    (by dsimp only [numerator,denominator,auxiliaryCost,factor,P,Q,U]; unfold unit; ipra_ring) (.eqRefl _) joined

/-- The same original p and q observations survive the finite gap.
Only the auxiliary multiplication/exponential comparison is removed. -/
theorem original_observations (p q z R B E T a b : PTm n)
    (h : Γ ⊢[PRAAx] source z R B E T a b) : Γ ⊢[PRAAx]
    distanceBounded (originalProduct p z B a b) (sample q z B a b)
      (numerator p q R E T) (denominator p q) :=
  GaussianRationalSlackRemoval.slack_removal_at _ _ _ (auxiliaryCost R E T)
    (positive_product _ _ (unit_positive p) (unit_positive q))
    (original_auxiliary_slack p q _ z R B E T a b h)

theorem original_diagonal (p z R B E T a b : PTm n)
    (h : Γ ⊢[PRAAx] source z R B E T a b) : Γ ⊢[PRAAx]
    distanceBounded (sample p z B a b) (originalProduct p z B a b) (factor R E T+one) (unit p) := by
  have hp := unit_positive (Γ := Γ) p
  have raw := distance_symmetric _ _ _ _ (positive_product _ _ hp hp) (original_observations p p z R B E T a b h)
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hp hp) hp
    (le_of_eq_add (d := zero) (by dsimp only [numerator,denominator]; ipra_ring)) raw

theorem actual_original_normalized_Euler_independent_product_observations_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
      (source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
        distanceBounded (originalProduct (var 0) (var 2) (var 4) (var 7) (var 8))
          (sample (var 1) (var 2) (var 4) (var 7) (var 8)) (numerator (var 0) (var 1) (var 3) (var 5) (var 6))
          (denominator (var 0) (var 1))) :=
  closeUniv 9 (.impI (original_observations _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerIntegrationByPartsObservation
