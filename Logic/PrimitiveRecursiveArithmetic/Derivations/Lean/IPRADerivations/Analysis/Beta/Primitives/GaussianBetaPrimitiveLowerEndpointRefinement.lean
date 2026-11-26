import IPRADerivations.Analysis.Beta.Primitives.GaussianBetaPrimitiveEndpointEncoding

/-!
# Finer original evaluation at a fixed constructive lower cutoff

The cutoff stays at the original computed q. Any outer grid evaluation
precision p>=q retains the same exact endpoint bound. The two original
numerical clock budgets control the fixed cutoff and the finer actual
observation separately; no rounded sample equality is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaPrimitiveLowerEndpointRefinement

open_ipra
open GaussianEulerLowerPowerCoefficients (source)
open GaussianBetaPrimitiveLowerEndpoint (precision budget rootDen root_den_positive)
open GaussianBetaPrimitiveEndpointEncoding (clockScaledEndpoint original_clock_scaled_endpoint_bound)
open GaussianGammaIntegralCutoffs (height)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The original eta cutoff q is unchanged, while the original outer
quadrature precision p may be any finer numerical precision. -/
theorem constructive_endpoint_small_at (t p z R B A N J : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A) (hN : Γ ⊢[PRAAx] le one N)
    (hJ : Γ ⊢[PRAAx] le one J) (hp : Γ ⊢[PRAAx] le (precision t z B N) p) : Γ ⊢[PRAAx]
    bounded (clockScaledEndpoint p z B (precision t z B N) A R N J) one (unit t) := by
  let q := precision t z B N
  let d := rootDen q A R
  let M := budget z B N
  let P := unit (succ t)
  have later : Γ ⊢[PRAAx] le q (height q A R) :=
    le_of_eq_add (d := A+GaussianGammaIntegralCutoffs.tailCoefficient R+LeanProofs.IPRA.PTm.num 10)
      (by unfold height; ipra_ring)
  have cutoff : Γ ⊢[PRAAx] le (unit q) d := GaussianExponentialReference.unit_monotone later
  have query : Γ ⊢[PRAAx] le (M*P) (unit q) := GaussianFastValueCut.query_budget _ _
  have finer : Γ ⊢[PRAAx] le (unit q) (unit p) := GaussianExponentialReference.unit_monotone hp
  have first : Γ ⊢[PRAAx] le (M*P*unit p) (d*unit p) :=
    mul_le_mul_right (unit p) (le_trans query cutoff)
  have last : Γ ⊢[PRAAx] le (M*P*d) (unit p*d) :=
    mul_le_mul_right d (le_trans query finer)
  have compare : Γ ⊢[PRAAx] le ((M*unit p+M*d)*P) (two*(d*unit p)) :=
    le_congr (by ipra_ring) (by ipra_ring) (add_le_add₂ first last)
  have small : Γ ⊢[PRAAx] bounded (clockScaledEndpoint p z B q A R N J) two P :=
    bounded_radius_mono _ _ _ _ _ (positive_product _ _ (root_den_positive q A R) (unit_positive p))
      (unit_positive (succ t)) compare (original_clock_scaled_endpoint_bound p z R B A q N J h hN hJ)
  exact bounded_radius_mono _ _ _ _ _ (unit_positive (succ t)) (unit_positive t)
    (le_of_eq_add (d := zero) ((congrMul (.eqRefl one) (pw_succ two t)).eqTrans (by unfold unit; ipra_ring))) small

theorem original_fixed_lower_cutoff_finer_grid_endpoint_small_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((source (var 2) (var 3) (var 4) (var 5) ⋏ le one (var 6) ⋏ le one (var 7) ⋏
      le (precision (var 0) (var 2) (var 4) (var 6)) (var 1)) ⟶
      bounded (clockScaledEndpoint (var 1) (var 2) (var 4) (precision (var 0) (var 2) (var 4) (var 6))
        (var 5) (var 3) (var 6) (var 7)) one (unit (var 0))) :=
  closeUniv 8 (.impI (constructive_endpoint_small_at _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBetaPrimitiveLowerEndpointRefinement
