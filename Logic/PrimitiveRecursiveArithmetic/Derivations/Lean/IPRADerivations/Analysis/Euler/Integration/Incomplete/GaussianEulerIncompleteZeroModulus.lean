import IPRADerivations.Analysis.Euler.Integration.Incomplete.GaussianEulerIncompleteSmallRationalEndpoint

/-!
# A primitive recursive modulus at the zero split of incomplete Gamma

For each requested endpoint tolerance, compute a positive dyadic
threshold. Every original positive rational split within that threshold
obeys the requested endpoint error and its own observation allowances.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIncompleteZeroModulus

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianGammaIntegralCutoffs (etaDen height)
open GaussianEulerIncompleteName (lowerF upperF data)
open GaussianGammaReciprocalInverse (gammaF gammaData)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianNamedInverseRate (rateNumerator rateDenominator rate_at denominator_positive)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def cutoffIndex (r A : PTm n) : PTm n := GaussianFastValueCut.exponent A r
def splitDenominator (r A R : PTm n) : PTm n := etaDen (cutoffIndex r A) A R
def source (r z R B A a b : PTm n) : Fm PTm n :=
  GaussianEulerIncompleteCofinalRate.source z R B A a b ⋏ le (a*splitDenominator r A R) b

theorem cutoff_budget (r A R : PTm n) : Γ ⊢[PRAAx]
    le (A*unit r) (unit (height (cutoffIndex r A) A R)) := by
  have clock : Γ ⊢[PRAAx] le (cutoffIndex r A) (height (cutoffIndex r A) A R) :=
    le_of_eq_add (d := A+GaussianGammaIntegralCutoffs.tailCoefficient R+num 10) (by unfold height; ipra_ring)
  exact le_trans (GaussianFastValueCut.query_budget A r) (GaussianExponentialReference.unit_monotone clock)

theorem original_lower_zero_modulus (r p z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source r z R B A a b) :
    Γ ⊢[PRAAx] bounded (ap2 lowerF p (data z R B A a b)) (unit p+unit r) (unit r*unit p) := by
  let k := cutoffIndex r A
  let H := unit (height k A R)
  let U := unit r
  let P := unit p
  have estimate := GaussianEulerIncompleteSmallRationalEndpoint.original_lower_small_rational_bound p z R B A k a b h
  have budget : Γ ⊢[PRAAx] le (A*U) H := cutoff_budget r A R
  exact bounded_radius_mono _ (A*P+H) (H*P) (P+U) (U*P)
    (positive_product _ _ (unit_positive _) (unit_positive p)) (positive_product _ _ (unit_positive r) (unit_positive p))
    (by dsimp only [H,U,P]
        ipra_le (𝔞(unit p)*𝔞(unit p))*sl budget) estimate

theorem original_upper_zero_modulus (r p q z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source r z R B A a b) :
    Γ ⊢[PRAAx] distanceBounded (ap2 upperF p (data z R B A a b)) (ap2 gammaF q (gammaData z R B A))
      (rateNumerator one (unit r) p q) (rateDenominator (unit r) p q) := by
  let k := cutoffIndex r A
  let H := unit (height k A R)
  let U := unit r
  have rate := GaussianEulerIncompleteSmallRationalEndpoint.original_upper_small_rational_rate z R B A k a b h
  have budget : Γ ⊢[PRAAx] le (A*U) H := cutoff_budget r A R
  exact GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _
    (denominator_positive H p q (unit_positive _)) (denominator_positive U p q (unit_positive r))
    (by dsimp only [H,U,rateNumerator,rateDenominator]
        ipra_le (𝔞(unit p)*𝔞(unit q)*𝔞(unit p)*𝔞(unit q))*sl budget)
    (rate_at _ _ _ _ _ _ p q rate)

theorem actual_original_incomplete_Euler_zero_modulus_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (source (var 0) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      (bounded (ap2 lowerF (var 1) (data (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)))
        (unit (var 1)+unit (var 0)) (unit (var 0)*unit (var 1)) ⋏
       distanceBounded (ap2 upperF (var 1) (data (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)))
        (ap2 gammaF (var 2) (gammaData (var 3) (var 4) (var 5) (var 6)))
        (rateNumerator one (unit (var 0)) (var 1) (var 2)) (rateDenominator (unit (var 0)) (var 1) (var 2)))) :=
  closeUniv 9 (.impI (.andI (original_lower_zero_modulus _ _ _ _ _ _ _ _ Prf.hyp0)
    (original_upper_zero_modulus _ _ _ _ _ _ _ _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianEulerIncompleteZeroModulus
