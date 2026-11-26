import IPRADerivations.Analysis.Beta.Primitives.GaussianBetaPrimitiveUniformBound
import IPRADerivations.Analysis.Beta.Primitives.GaussianBetaPrimitiveEndpointEncoding

/-!
# Degree-independent lower beta endpoint at its original raw grid encoding

The original time J/(etaDen(k)*J), endpoint program and replacement clock
are unchanged. The actual primitive bound 3A replaces the prior computed
coefficient mass. The cutoff and observation budgets are uniform in N.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaPrimitiveUniformLowerEndpoint

open_ipra
open GaussianEulerLowerPowerCoefficients (source)
open GaussianGammaIntegralCutoffs (height etaDen eta_den_positive)
open GaussianBetaPrimitiveLowerEndpoint (rootDen root_den_positive scale_endpoint_bound dyadic_bound_of_eta_bound)
open GaussianBetaPrimitiveEndpointEncoding (endpoint scaledEndpoint clockScaledEndpoint encoded_endpoint_bound_of_primitive retime_dyadic_bound)
open GaussianBetaPrimitiveLinearStep (argument)
open GaussianEulerBetaPolynomialPrimitive (primitive)
open GaussianEulerCompactProductComparison (clock)
open GaussianRationalHorner (evaluate positive_product)
open GaussianRationalMetric (bounded)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def budget (A : PTm n) : PTm n := (LeanProofs.IPRA.PTm.num 3)*A
def numerator (p k A R : PTm n) : PTm n := budget A*(pw (rootDen k A R) (LeanProofs.IPRA.PTm.pred A)*unit p+one)
def denominator (p k A R N : PTm n) : PTm n := N*etaDen k A R*unit p
def precision (t A : PTm n) : PTm n := GaussianFastValueCut.exponent (budget A) (succ t)
ipra_subst budget
ipra_subst precision

theorem encoded_primitive_bound (z R B A k N J : PTm n) (h : Γ ⊢[PRAAx] source z R B A)
    (hN : Γ ⊢[PRAAx] le one N) (hJ : Γ ⊢[PRAAx] le one J) : Γ ⊢[PRAAx]
    bounded (evaluate (primitive z B N) (argument J (etaDen k A R*J) N)) (budget A) one :=
  GaussianBetaPrimitiveUniformBound.original_primitive_bound z B A N J (etaDen k A R*J)
    (.andI h.andE₂.andE₁.andE₁ (.andI h.andE₁ h.andE₂.andE₂))
    (positive_product _ _ (eta_den_positive k A R) hJ) hN
    (le_congr (one_mul J) (.eqRefl _) (mul_le_mul_right J (eta_den_positive k A R)))

theorem encoded_lower_endpoint_bound (p z R B A k N J : PTm n) (h : Γ ⊢[PRAAx] source z R B A)
    (hN : Γ ⊢[PRAAx] le one N) (hJ : Γ ⊢[PRAAx] le one J) : Γ ⊢[PRAAx]
    bounded (endpoint p z B k A R N J) (numerator p k A R) (denominator p k A R N) :=
  encoded_endpoint_bound_of_primitive p z R B A k N J (budget A) h hN hJ
    (encoded_primitive_bound z R B A k N J h hN hJ)

theorem encoded_scaled_endpoint_bound (p z R B A k N J : PTm n) (h : Γ ⊢[PRAAx] source z R B A)
    (hN : Γ ⊢[PRAAx] le one N) (hJ : Γ ⊢[PRAAx] le one J) : Γ ⊢[PRAAx]
    bounded (scaledEndpoint p z B k A R N J) (numerator p k A R) (etaDen k A R*unit p) :=
  scale_endpoint_bound p k A R N _ _ hN (encoded_lower_endpoint_bound p z R B A k N J h hN hJ)

theorem encoded_dyadic_bound (p z R B A k N J : PTm n) (h : Γ ⊢[PRAAx] source z R B A)
    (hN : Γ ⊢[PRAAx] le one N) (hJ : Γ ⊢[PRAAx] le one J) : Γ ⊢[PRAAx]
    bounded (scaledEndpoint p z B k A R N J) (budget A*unit p+budget A*rootDen k A R)
      (rootDen k A R*unit p) :=
  dyadic_bound_of_eta_bound p k A R _ _ h.andE₁ (encoded_scaled_endpoint_bound p z R B A k N J h hN hJ)

/-- Actual argument-dependent grid clock, with the requested outer p
retained in its error budget. -/
theorem original_clock_scaled_endpoint_bound (p z R B A k N J : PTm n) (h : Γ ⊢[PRAAx] source z R B A)
    (hN : Γ ⊢[PRAAx] le one N) (hJ : Γ ⊢[PRAAx] le one J) : Γ ⊢[PRAAx]
    bounded (clockScaledEndpoint p z B k A R N J) (budget A*unit p+budget A*rootDen k A R)
      (rootDen k A R*unit p) := by
  let q := clock p z B J (etaDen k A R*J)
  exact retime_dyadic_bound p q k A R _ (budget A) (GaussianEulerCompactProductComparison.clock_later p z B J (etaDen k A R*J))
    (encoded_dyadic_bound q z R B A k N J h hN hJ)

/-- Both the cutoff k and the actual outer grid precision p may be any
finer values than the SAME degree-independent computed threshold. -/
theorem constructive_endpoint_small_at (t k p z R B A N J : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A) (hN : Γ ⊢[PRAAx] le one N) (hJ : Γ ⊢[PRAAx] le one J)
    (hk : Γ ⊢[PRAAx] le (precision t A) k) (hp : Γ ⊢[PRAAx] le (precision t A) p) : Γ ⊢[PRAAx]
    bounded (clockScaledEndpoint p z B k A R N J) one (unit t) := by
  let q := precision t A
  let d := rootDen k A R
  let M := budget A
  let P := unit (succ t)
  have later : Γ ⊢[PRAAx] le k (height k A R) :=
    le_of_eq_add (d := A+GaussianGammaIntegralCutoffs.tailCoefficient R+LeanProofs.IPRA.PTm.num 10)
      (by unfold height; ipra_ring)
  have cutoff : Γ ⊢[PRAAx] le (unit q) d := GaussianExponentialReference.unit_monotone (le_trans hk later)
  have query : Γ ⊢[PRAAx] le (M*P) (unit q) := GaussianFastValueCut.query_budget _ _
  have finer : Γ ⊢[PRAAx] le (unit q) (unit p) := GaussianExponentialReference.unit_monotone hp
  have first : Γ ⊢[PRAAx] le (M*P*unit p) (d*unit p) := mul_le_mul_right (unit p) (le_trans query cutoff)
  have last : Γ ⊢[PRAAx] le (M*P*d) (unit p*d) := mul_le_mul_right d (le_trans query finer)
  have compare : Γ ⊢[PRAAx] le ((M*unit p+M*d)*P) (two*(d*unit p)) :=
    le_congr (by ipra_ring) (by ipra_ring) (add_le_add₂ first last)
  have small : Γ ⊢[PRAAx] bounded (clockScaledEndpoint p z B k A R N J) two P :=
    bounded_radius_mono _ _ _ _ _ (positive_product _ _ (root_den_positive k A R) (unit_positive p))
      (unit_positive (succ t)) compare (original_clock_scaled_endpoint_bound p z R B A k N J h hN hJ)
  exact bounded_radius_mono _ _ _ _ _ (unit_positive (succ t)) (unit_positive t)
    (le_of_eq_add (d := zero) ((congrMul (.eqRefl one) (pw_succ two t)).eqTrans (by unfold unit; ipra_ring))) small

theorem original_degree_independent_lower_endpoint_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((source (var 1) (var 2) (var 3) (var 4) ⋏ le one (var 6) ⋏ le one (var 7)) ⟶
      bounded (clockScaledEndpoint (var 0) (var 1) (var 3) (var 5) (var 4) (var 2) (var 6) (var 7))
        (budget (var 4)*unit (var 0)+budget (var 4)*rootDen (var 5) (var 4) (var 2))
        (rootDen (var 5) (var 4) (var 2)*unit (var 0))) :=
  closeUniv 8 (.impI (original_clock_scaled_endpoint_bound _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))
theorem original_degree_independent_endpoint_constructively_small_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    ((source (var 3) (var 4) (var 5) (var 6) ⋏ le one (var 7) ⋏ le one (var 8) ⋏
      le (precision (var 0) (var 6)) (var 1) ⋏ le (precision (var 0) (var 6)) (var 2)) ⟶
      bounded (clockScaledEndpoint (var 2) (var 3) (var 5) (var 1) (var 6) (var 4) (var 7) (var 8)) one (unit (var 0))) :=
  closeUniv 9 (.impI (constructive_endpoint_small_at _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBetaPrimitiveUniformLowerEndpoint
