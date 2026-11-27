import IPRADerivations.Analysis.Euler.Integration.Parts.Endpoints.GaussianEulerIntegrationByPartsEndpointBudget
import IPRADerivations.Analysis.Euler.Integration.Parts.Recurrences.GaussianEulerIntegrationByPartsParameterShiftObservation
import IPRADerivations.Analysis.Gamma.Integrals.GaussianEulerIntegralGammaIdentification

/-!
# Vanishing external boundaries on the original regular endpoint programs

Both endpoint programs are the original shifted Euler PR2 name at the
true unscaled cutoff times. The cutoff is fixed during each finite gap
argument. A computed original observation query pays all its endpoint
rescaling and parameter-shift costs, leaving the requested endpoint
observation error and the prescribed cutoff error only.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIntegrationByPartsNamedEndpoints

open_ipra
open GaussianEulerIntegralGammaIdentification (source)
open GaussianEulerIntegrationByPartsLinear (primitive)
open GaussianEulerIntegrationByPartsParameterShiftObservation (primitiveCost)
open GaussianEulerIntegrationByPartsEndpointBudget (cutoff minimumObservation)
open GaussianEulerIntegrandName (nameF data sample sample_at)
open GaussianGammaEulerHeadShift (shifted)
open GaussianGammaIntegralCutoffs (etaDen top eta_den_positive top_positive)
open GaussianGammaCompactQuadratureBoundary (width)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same distance_radius_mono_same)
open GaussianNameEquivalence (point_at)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianRationalSlackRemoval (slack slack_removal_at precision)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def lowerData (z R B A k : PTm n) : PTm n := data (shifted z B) B one (etaDen k A R)
def upperData (z R B A k : PTm n) : PTm n := data (shifted z B) B (top k A R) one
def rawLower (p z R B A k : PTm n) : PTm n := primitive p z B (one*one) (etaDen k A R*one)
def rawUpper (p z R B A k : PTm n) : PTm n := primitive p z B (one*one+width k A R*one) (etaDen k A R*one)
def sampleCost (R A k : PTm n) : PTm n := num 6*top k A R+primitiveCost R (etaDen k A R) (top k A R)
def cost (R A k : PTm n) : PTm n := one+sampleCost R A k
def clock (m t R A k : PTm n) : PTm n := minimumObservation t k A R+GaussianFastValueCut.exponent (cost R A k) m

ipra_subst lowerData [etaDen, GaussianGammaIntegralCutoffs.height, GaussianGammaIntegralCutoffs.tailCoefficient]
ipra_subst upperData [top, GaussianGammaIntegralCutoffs.height, GaussianGammaIntegralCutoffs.tailCoefficient]

theorem endpoint_regular (z R B A k : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    GaussianEuclideanDistanceName.pointCN nameF (lowerData z R B A k) ⋏
      GaussianEuclideanDistanceName.pointCN nameF (upperData z R B A k) :=
  .andI (GaussianEulerIntegrandName.name_regular _ _ _ _
    (.andI h.andE₁.andE₂.andE₁.andE₁ (.andI (le_refl one) (eta_den_positive k A R))))
    (GaussianEulerIntegrandName.name_regular _ _ _ _
      (.andI h.andE₁.andE₂.andE₁.andE₁ (.andI (top_positive k A R) (le_refl one))))

private theorem endpoint_sources (z R B A k : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    GaussianEulerIntegrationByPartsObservation.source z R B (etaDen k A R) (top k A R) one (etaDen k A R) ⋏
      GaussianEulerIntegrationByPartsObservation.source z R B (etaDen k A R) (top k A R) (top k A R) one := by
  let E := etaDen k A R
  let T := top k A R
  have he := eta_den_positive (Γ := Γ) k A R
  have ht := top_positive (Γ := Γ) k A R
  have input : Γ ⊢[PRAAx] GaussianEulerExponentCompactBounds.source z R B E :=
    .andI h.andE₁.andE₂.andE₁.andE₁ (.andI he h.andE₁.andE₂.andE₁.andE₂)
  have lowerLow : Γ ⊢[PRAAx] le E (E*one) := le_congr (.eqRefl _) (by ipra_ring) (le_refl E)
  have lowerHigh : Γ ⊢[PRAAx] le one (T*E) := positive_product _ _ ht he
  have upperLow : Γ ⊢[PRAAx] le one (E*T) := positive_product _ _ he ht
  have upperHigh : Γ ⊢[PRAAx] le T (T*one) := le_congr (.eqRefl _) (by ipra_ring) (le_refl T)
  exact .andI (.andI input (.andI (.andI (le_refl one) he) (.andI lowerLow lowerHigh)))
    (.andI input (.andI (.andI ht (le_refl one)) (.andI upperLow upperHigh)))

/-- Actual original endpoint observations are close to the literal raw
endpoints appearing in the already checked finite telescope. -/
theorem endpoint_raw_distance (p z R B A k : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (lowerData z R B A k)) (rawLower p z R B A k) (sampleCost R A k) (unit p) ⋏
      distanceBounded (ap2 nameF p (upperData z R B A k)) (rawUpper p z R B A k) (sampleCost R A k) (unit p) := by
  let E := etaDen k A R
  let T := top k A R
  let K := primitiveCost R E T
  have hp := unit_positive (Γ := Γ) p
  have timeSource := endpoint_sources z R B A k h
  have left := GaussianEulerIntegrationByPartsParameterShiftObservation.original_primitive_observation p z R B E T one E timeSource.andE₁
  have right := GaussianEulerIntegrationByPartsParameterShiftObservation.original_primitive_observation p z R B E T T one timeSource.andE₂
  have rescale := GaussianEulerIntegrationByPartsEndpointRescale.original_affine_cutoff_endpoints p z R B k A one
    h.andE₁.andE₂.andE₁.andE₁ (le_refl one)
  have leftFull := distance_triangle_same _ _ _ _ _ _ hp left (distance_symmetric _ _ _ _ hp rescale.andE₁)
  have rightFull := distance_triangle_same _ _ _ _ _ _ hp right (distance_symmetric _ _ _ _ hp rescale.andE₂)
  have grow : Γ ⊢[PRAAx] le (K+num 6) (sampleCost R A k) :=
    le_congr (.eqRefl _) (by unfold sampleCost; dsimp only [T,K,E]; ipra_ring)
      (add_le_add₂ (le_refl K) (le_congr (by ipra_ring) (.eqRefl _) (mul_le_mul_right (num 6) (top_positive k A R))))
  exact .andI
    (distance_congr (sample_at p _ _ _ _) (.eqRefl _) (.eqRefl _) (.eqRefl _)
      (distance_radius_mono_same hp grow leftFull))
    (distance_congr (sample_at p _ _ _ _) (.eqRefl _) (by unfold sampleCost; ipra_ring) (.eqRefl _) rightFull)

private theorem add_query_error (q p x v C : PTm n)
    (hr : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN nameF x)
    (h : Γ ⊢[PRAAx] distanceBounded (ap2 nameF p x) v C (unit p)) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF q x) v (unit p+(one+C)*unit q) (unit q*unit p) := by
  have hqp := positive_product (Γ := Γ) _ _ (unit_positive q) (unit_positive p)
  have first := point_at nameF x q p hr
  have second := distance_radius_mono _ _ _ _ (C*unit q) (unit q*unit p) (unit_positive p) hqp
    (le_of_eq_add (d := zero) (by ipra_ring)) h
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hqp first second)

theorem endpoint_observations (q p z R B A k : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF q (lowerData z R B A k)) (rawLower p z R B A k)
      (unit p+cost R A k*unit q) (unit q*unit p) ⋏
      distanceBounded (ap2 nameF q (upperData z R B A k)) (rawUpper p z R B A k)
        (unit p+cost R A k*unit q) (unit q*unit p) :=
  .andI (add_query_error _ _ _ _ _ (endpoint_regular z R B A k h).andE₁ (endpoint_raw_distance p z R B A k h).andE₁)
    (add_query_error _ _ _ _ _ (endpoint_regular z R B A k h).andE₂ (endpoint_raw_distance p z R B A k h).andE₂)

theorem clock_raw (m t R A k : PTm n) : Γ ⊢[PRAAx] le (minimumObservation t k A R) (clock m t R A k) := le_add_right _ _
theorem clock_budget (m t R A k : PTm n) : Γ ⊢[PRAAx] le (cost R A k*unit m) (unit (clock m t R A k)) :=
  le_trans (GaussianFastValueCut.query_budget _ _) (GaussianExponentialReference.unit_monotone (le_add_left _ _))

private theorem slack_from_raw (q t m p z v C : PTm n)
    (h : Γ ⊢[PRAAx] distanceBounded z v (unit p+C*unit q) (unit q*unit p))
    (hv : Γ ⊢[PRAAx] bounded v one (unit t))
    (hc : Γ ⊢[PRAAx] le (C*unit m) (unit p)) : Γ ⊢[PRAAx]
    slack z (unit q+unit t) (unit q*unit t) one m := by
  have hqp := positive_product (Γ := Γ) _ _ (unit_positive q) (unit_positive p)
  have total := GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _ hqp (unit_positive t) h hv
  change Γ ⊢[PRAAx] bounded z ((unit q+unit t)*unit m+one*(unit q*unit t)) ((unit q*unit t)*unit m)
  apply bounded_radius_mono _ _ _ _ _ (positive_product _ _ hqp (unit_positive t))
    (positive_product _ _ (positive_product _ _ (unit_positive q) (unit_positive t)) (unit_positive m)) _ total
  ipra_le (𝔞(unit q)*𝔞(unit q)*𝔞(unit t)*𝔞(unit t))*sl hc

theorem endpoint_slacks (q t m z R B A k : PTm n) (h : Γ ⊢[PRAAx] source z R B A)
    (hk : Γ ⊢[PRAAx] le (cutoff t R) k) : Γ ⊢[PRAAx]
    slack (ap2 nameF q (lowerData z R B A k)) (unit q+unit t) (unit q*unit t) one m ⋏
      slack (ap2 nameF q (upperData z R B A k)) (unit q+unit t) (unit q*unit t) one m := by
  let p := clock m t R A k
  have near := endpoint_observations q p z R B A k h
  have raw := GaussianEulerIntegrationByPartsEndpointBudget.original_encoded_endpoints_small t p z R B k A one
    h.andE₁ (le_refl one) hk (clock_raw m t R A k)
  have budget := clock_budget (Γ := Γ) m t R A k
  exact .andI (slack_from_raw q t m p _ _ _ near.andE₁ raw.andE₁ budget)
    (slack_from_raw q t m p _ _ _ near.andE₂ raw.andE₂ budget)

/-- Each original regular shifted endpoint observation retains exactly
its own tolerance plus the prescribed external cutoff tolerance. -/
theorem original_endpoint_bounds (q t z R B A k : PTm n) (h : Γ ⊢[PRAAx] source z R B A)
    (hk : Γ ⊢[PRAAx] le (cutoff t R) k) : Γ ⊢[PRAAx]
    bounded (ap2 nameF q (lowerData z R B A k)) (unit q+unit t) (unit q*unit t) ⋏
      bounded (ap2 nameF q (upperData z R B A k)) (unit q+unit t) (unit q*unit t) := by
  have hd := positive_product (Γ := Γ) _ _ (unit_positive q) (unit_positive t)
  have low := endpoint_slacks q t (precision (ap2 nameF q (lowerData z R B A k)) (unit q+unit t) (unit q*unit t) one) z R B A k h hk
  have high := endpoint_slacks q t (precision (ap2 nameF q (upperData z R B A k)) (unit q+unit t) (unit q*unit t) one) z R B A k h hk
  exact .andI (slack_removal_at _ _ _ one hd low.andE₁) (slack_removal_at _ _ _ one hd high.andE₂)

theorem actual_original_named_external_Euler_endpoints_small_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((source (var 2) (var 3) (var 4) (var 5) ⋏ le (cutoff (var 1) (var 3)) (var 6)) ⟶
      bounded (ap2 nameF (var 0) (lowerData (var 2) (var 3) (var 4) (var 5) (var 6)))
        (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1)) ⋏
      bounded (ap2 nameF (var 0) (upperData (var 2) (var 3) (var 4) (var 5) (var 6)))
        (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 7 (.impI (original_endpoint_bounds _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerIntegrationByPartsNamedEndpoints
