import IPRADerivations.Analysis.Gamma.Integrals.GaussianGammaIntegralCutoffs
import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerDecayFactorBounds
import IPRADerivations.Analysis.Polynomials.RootFinding.Adequacy.GaussianRootAdequacySchedule

/-!
# The actual endpoint majorants at the Euler-integral cutoffs

The dyadic witness for the positive A-th root of the left endpoint
gives the exact lower majorant value. Evaluate the right majorant with
the original Euler decay name at half the prescribed upper endpoint.
One computed observation precision pays for its dyadic error. This
checks the combined numerical budget of the two endpoint majorants.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaIntegralTailBudget

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaIntegralCutoffs (etaDen tailCoefficient height exact_eta_root_power omitted_tail_budget)
open GaussianEulerIntegrandName (decayF decayData)
open GaussianEulerDecayFactorBounds (original_integer_decay_bound)
open GaussianDominantPairAlgebra (radiusPoint radius_power radius_congr radius_bounded)
open GaussianRationalHorner (qadd qmul positive_product)
open GaussianRationalReciprocal (power bounded_product bounded_sum bound_congr)
open GaussianRationalMetric (bounded)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianRootSchedule (binaryLength)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def lowerRoot (p A R : PTm n) : PTm n := radiusPoint one (unit (height p A R))
def lowerValue (p A R : PTm n) : PTm n := radiusPoint A (unit (height p A R))
def observation (p R : PTm n) : PTm n := p+num 6+binaryLength (two*tailCoefficient R)
def upperValue (p A R : PTm n) : PTm n :=
  qmul (radiusPoint (tailCoefficient R) one) (ap2 decayF (observation p R) (decayData (height p A R) one))
def endpointValues (p A R : PTm n) : PTm n := qadd (lowerValue p A R) (upperValue p A R)

theorem actual_left_root (p A R : PTm n) :
    Γ ⊢[PRAAx] power (lowerRoot p A R) A ≐ radiusPoint one (etaDen p A R) :=
  (radius_power one (unit (height p A R)) A (unit_positive _)).eqTrans
    (radius_congr (GaussianPolynomialPerturbation.one_power A) (exact_eta_root_power p A R))

theorem actual_left_majorant (p A R : PTm n) :
    Γ ⊢[PRAAx] qmul (radiusPoint A one) (lowerRoot p A R) ≐ lowerValue p A R :=
  (GaussianDominantPairAlgebra.radius_multiply A one one (unit (height p A R))
    (le_refl one) (unit_positive _)).eqTrans (radius_congr (by ipra_ring) (one_mul _))

theorem endpoint_observation_budget (p A R : PTm n) :
    Γ ⊢[PRAAx] bounded (endpointValues p A R) two (unit (p+num 6)) := by
  let H := height p A R
  let D := tailCoefficient R
  let U := unit H
  let V := unit (observation p R)
  let W := unit (p+num 6)
  let Z := U*V
  have hp : Γ ⊢[PRAAx] le one U := unit_positive _
  have hq : Γ ⊢[PRAAx] le one V := unit_positive _
  have hZ : Γ ⊢[PRAAx] le one Z := positive_product _ _ hp hq
  have low : Γ ⊢[PRAAx] bounded (lowerValue p A R) (A*V) Z :=
    bounded_radius_mono _ _ _ _ _ hp hZ (le_of_eq_add (d := zero) (by dsimp only [Z]; ipra_ring))
      (radius_bounded A U hp)
  have high : Γ ⊢[PRAAx] bounded (upperValue p A R) (D*(V+two*U)) Z :=
    bound_congr (.eqRefl _) (.eqRefl _) (one_mul _)
      (bounded_product (radiusPoint D one) (ap2 decayF (observation p R) (decayData H one))
        D one (V+two*U) Z (le_refl one) hZ (radius_bounded D one (le_refl one))
        (original_integer_decay_bound H (observation p R)))
  have added := GaussianRationalPowerDifference.bounded_sum_same (lowerValue p A R) (upperValue p A R)
    (A*V) (D*(V+two*U)) Z hZ low high
  have raw : Γ ⊢[PRAAx] bounded (endpointValues p A R) ((A+D)*V+two*D*U) Z :=
    bound_congr (.eqRefl _) (by ipra_ring) (.eqRefl _) added
  have tails : Γ ⊢[PRAAx] le ((A+D)*W) U := le_of_lt (omitted_tail_budget p A R)
  have err : Γ ⊢[PRAAx] le (two*D*W) V := GaussianRootAdequacySchedule.binary_power_budget (two*D) (p+num 6)
  exact bounded_radius_mono _ _ _ _ _ hZ (unit_positive _)
    (le_congr (by ipra_ring) (by dsimp only [Z]; ipra_ring)
      (add_le_add₂ (mul_le_mul_right V tails) (mul_le_mul_right U err))) raw

theorem original_Euler_left_endpoint_dyadic_root_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (power (lowerRoot (var 0) (var 1) (var 2)) (var 1) ≐ radiusPoint one (etaDen (var 0) (var 1) (var 2))) :=
  closeUniv 3 (actual_left_root _ _ _)

theorem original_Euler_observed_endpoint_majorants_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (bounded (endpointValues (var 0) (var 1) (var 2)) two (unit (var 0+num 6))) :=
  closeUniv 3 (endpoint_observation_budget _ _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaIntegralTailBudget
