import IPRADerivations.Analysis.Euler.Integration.Decay.Increments.GaussianEulerDecayAddition
import IPRADerivations.Analysis.Stirling.Binet.Laplace.Integrands.GaussianBinetLaplaceScalarMajorant

/-!
# Global linear remainder for the original real decay sampler

The local quadratic estimate covers exponents at most one. For
larger nonnegative exponents the unit norm bound and the linear term
give a quadratic estimate with a fixed constant. Both cases apply to
the original decay observation at arbitrary precision.
-/

set_option autoImplicit false
set_option maxHeartbeats 750000

namespace LeanProofs.IPRA.Analysis.GaussianEulerDecayGlobalTaylor

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEulerIntegrandName (decayF decayData decayPoint)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalHorner (qadd positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (qone qone_bounded bound_congr bounded_sum bounded_difference)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

private theorem linear_norm (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] bounded (qadd qone (decayPoint a b)) (b+a) b :=
  bound_congr (.eqRefl _) (by ipra_ring) (one_mul _)
    (bounded_sum qone (decayPoint a b) one one a b (le_refl one) hb qone_bounded
      (GaussianEulerDecayAddition.decay_point_bounded a b hb))

private theorem large_remainder (a b p : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hba : Γ ⊢[PRAAx] le b a) :
    Γ ⊢[PRAAx] distanceBounded (ap2 decayF p (decayData a b)) (qadd qone (decayPoint a b))
      (num 3*(a*a)*unit p+two*(b*b)) (b*b*unit p) := by
  let U := unit p
  let x := ap2 decayF p (decayData a b)
  let y := qadd qone (decayPoint a b)
  have hu := unit_positive (Γ := Γ) p
  have hbb := positive_product _ _ hb hb
  have raw : Γ ⊢[PRAAx] distanceBounded x y ((U+one)*b+(b+a)*U) (U*b) :=
    bounded_difference _ _ _ _ _ _ hu hb
      (GaussianBinetLaplaceScalarMajorant.original_decay_unit_bound p a b hb) (linear_norm a b hb)
  have first : Γ ⊢[PRAAx] le (a+b+b) (num 3*a) := by
    ipra_le 2*sl hba
  have second : Γ ⊢[PRAAx] le ((a+b+b)*b) (num 3*(a*a)) :=
    le_congr (.eqRefl _) (by ipra_ring) (le_mul_mono first hba)
  apply distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hu hb) (positive_product _ _ hbb hu) ?_ raw
  ipra_le 𝔞(b)*𝔞(U)*𝔞(U)*sl second+𝔞(b)*𝔞(b)*𝔞(b)*𝔞(U)

/-- For every nonnegative rational exponent, the exact linear
approximation is within three times its square plus observation slack. -/
theorem original_decay_linear_remainder (a b p : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] distanceBounded (ap2 decayF p (decayData a b)) (qadd qone (decayPoint a b))
      (num 3*(a*a)*unit p+two*(b*b)) (b*b*unit p) := by
  refine (le_total a b).orE ?_ (large_remainder a b p hb.wk Prf.hyp0)
  have hD : le a b :: Γ ⊢[PRAAx] le one (b*b*unit p) :=
    positive_product _ _ (positive_product _ _ hb.wk hb.wk) (unit_positive p)
  apply distance_radius_mono _ _ _ _ _ _ hD hD ?_
    (GaussianEulerDecayAddition.original_decay_linear_remainder a b p hb.wk Prf.hyp0)
  ipra_le 2*𝔞(a)*𝔞(a)*𝔞(unit p)*𝔞(b)*𝔞(b)*𝔞(unit p)

theorem actual_global_original_decay_linear_remainder_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ distanceBounded (ap2 decayF (var 2) (decayData (var 0) (var 1)))
      (qadd qone (decayPoint (var 0) (var 1)))
      (num 3*(var 0*var 0)*unit (var 2)+two*(var 1*var 1)) (var 1*var 1*unit (var 2))) :=
  closeUniv 3 (.impI (original_decay_linear_remainder _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerDecayGlobalTaylor
