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
open GaussianBetaPrimitiveLowerEndpoint (rootDen root_den_positive eta_factorization)
open GaussianBetaPrimitiveEndpointEncoding (endpoint scaledEndpoint clockScaledEndpoint encoded_power_bound argument_encoding)
open GaussianBetaPrimitiveLinearStep (argument)
open GaussianEulerBetaPolynomialPrimitive (primitive)
open GaussianEulerCompactProductComparison (clock)
open GaussianRationalHorner (qmul evaluate positive_product)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalNaturalScale (naturalPoint)
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
    bounded (endpoint p z B k A R N J) (numerator p k A R) (denominator p k A R N) := by
  have hd := positive_product (Γ := Γ) _ _ (eta_den_positive k A R) hN
  have argumentBound : Γ ⊢[PRAAx] bounded (argument J (etaDen k A R*J) N) one (etaDen k A R*N) :=
    bound_congr (argument_encoding k A R N J hN hJ).eqSymm (.eqRefl _) (.eqRefl _)
      (bound_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point one (etaDen k A R*N) hd).eqSymm
        (.eqRefl _) (.eqRefl _) (GaussianDominantPairAlgebra.radius_bounded one _ hd))
  have poly := bounded_product _ _ (budget A) one one (etaDen k A R*N) (le_refl one) hd
    (encoded_primitive_bound z R B A k N J h hN hJ) argumentBound
  have result := bounded_product _ _ _ _ _ _ (unit_positive p) (positive_product _ _ (le_refl one) hd)
    (encoded_power_bound p z R B A k J h hJ) poly
  exact bound_congr (.eqRefl _) (by unfold numerator; ipra_ring) (by unfold denominator; ipra_ring) result

theorem encoded_scaled_endpoint_bound (p z R B A k N J : PTm n) (h : Γ ⊢[PRAAx] source z R B A)
    (hN : Γ ⊢[PRAAx] le one N) (hJ : Γ ⊢[PRAAx] le one J) : Γ ⊢[PRAAx]
    bounded (scaledEndpoint p z B k A R N J) (numerator p k A R) (etaDen k A R*unit p) := by
  have hd := positive_product (Γ := Γ) _ _ (positive_product _ _ hN (eta_den_positive k A R)) (unit_positive p)
  have natural : Γ ⊢[PRAAx] bounded (naturalPoint N) N one :=
    bound_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point N one (le_refl one)).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianDominantPairAlgebra.radius_bounded N one (le_refl one))
  have result := bounded_product _ _ N one _ _ (le_refl one) hd natural (encoded_lower_endpoint_bound p z R B A k N J h hN hJ)
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ (le_refl one) hd)
    (positive_product _ _ (eta_den_positive k A R) (unit_positive p))
    (le_of_eq_add (d := zero) (by ipra_ring)) result

theorem encoded_dyadic_bound (p z R B A k N J : PTm n) (h : Γ ⊢[PRAAx] source z R B A)
    (hN : Γ ⊢[PRAAx] le one N) (hJ : Γ ⊢[PRAAx] le one J) : Γ ⊢[PRAAx]
    bounded (scaledEndpoint p z B k A R N J) (budget A*unit p+budget A*rootDen k A R)
      (rootDen k A R*unit p) := by
  let d := rootDen k A R
  let E := etaDen k A R
  let M := budget A
  let P := unit p
  have compare : Γ ⊢[PRAAx] le ((M*(pw d (pred A)*P+one))*(d*P)) ((M*P+M*d)*(E*P)) := by
    have e := natEq (eta_factorization (Γ := Γ) k A R h.andE₁)
    have growth : Γ ⊢[PRAAx] le (M*d*P) (M*d*P*E) :=
      le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (M*d*P) (eta_den_positive (Γ := Γ) k A R))
    have g := natEq (eq_add_of_le growth)
    apply le_of_eq_add (d := LeanProofs.IPRA.PTm.monus (M*d*P*E) (M*d*P))
    apply deriveNat
    dsimp only [E,d] at g ⊢
    ipra_simps
    rw [e] at g ⊢
    linear_combination g
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ (eta_den_positive k A R) (unit_positive p))
    (positive_product _ _ (root_den_positive k A R) (unit_positive p)) compare
    (encoded_scaled_endpoint_bound p z R B A k N J h hN hJ)

/-- Actual argument-dependent grid clock, with the requested outer p
retained in its error budget. -/
theorem original_clock_scaled_endpoint_bound (p z R B A k N J : PTm n) (h : Γ ⊢[PRAAx] source z R B A)
    (hN : Γ ⊢[PRAAx] le one N) (hJ : Γ ⊢[PRAAx] le one J) : Γ ⊢[PRAAx]
    bounded (clockScaledEndpoint p z B k A R N J) (budget A*unit p+budget A*rootDen k A R)
      (rootDen k A R*unit p) := by
  let q := clock p z B J (etaDen k A R*J)
  let M := budget A
  let d := rootDen k A R
  have grow := GaussianExponentialReference.unit_monotone (GaussianEulerCompactProductComparison.clock_later (Γ := Γ) p z B J (etaDen k A R*J))
  have compare : Γ ⊢[PRAAx] le ((M*unit q+M*d)*(d*unit p)) ((M*unit p+M*d)*(d*unit q)) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (add_le_add_right (M*unit q*d*unit p) (mul_le_mul_right (M*d*d) grow))
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ (root_den_positive k A R) (unit_positive q))
    (positive_product _ _ (root_den_positive k A R) (unit_positive p)) compare
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
