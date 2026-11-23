import IPRADerivations.Analysis.GaussianEulerFixedCutoffApproximation

/-!
# Actual Euler observations at any later fixed cutoff

The unchanged improper observation at p and original fixed-cutoff name
observation at q are within 2^-p+2^-t whenever k>=t and q>=t+1.
The exact omitted-tail budget and native dyadic arithmetic absorb only
the old fixed observation error and the finite tail. No observation,
cutoff program, or name data are replaced by a surrogate.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLaterCutoffObservation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerCutoffCauchyComparison (combined observation)
open GaussianEulerImproperName (source nameF data)
open GaussianGammaIntegralCutoffs (height omitted_tail_budget)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNamedInverseRate (rateNumerator rateDenominator)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalHorner (positive_product)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

private theorem unit_successor (t : PTm n) : Γ ⊢[PRAAx] unit (succ t) ≐ two*unit t :=
  (pw_succ two t).eqTrans (mul_comm _ _)

/-- The true omitted tail is already below half the requested tolerance
at every numerical later cutoff k>=t. -/
theorem later_tail_budget (t k A R : PTm n) (htk : Γ ⊢[PRAAx] le t k) : Γ ⊢[PRAAx]
    le (combined A R*unit (succ t)) (unit (height k A R)) := by
  have first : Γ ⊢[PRAAx] le (succ t) (succ k) :=
    le_congr (by ipra_ring) (by ipra_ring) (add_le_add_right one htk)
  have extra : Γ ⊢[PRAAx] le (succ k) (k+num 6) := le_of_eq_add (d := num 5) (by ipra_ring)
  have growth := GaussianExponentialReference.unit_monotone (Γ := Γ) (le_trans first extra)
  have scaled : Γ ⊢[PRAAx] le (combined A R*unit (succ t)) (combined A R*unit (k+num 6)) :=
    le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right (combined A R) growth)
  exact le_trans scaled (le_of_lt (omitted_tail_budget k A R))

/-- Exact scalar budget: the two half-tolerances combine without any
rounding, division, or positive-tail assumption. -/
private theorem absorb_two_halves (C H Q T : PTm n)
    (hTail : Γ ⊢[PRAAx] le (C*(two*T)) H) (hQuery : Γ ⊢[PRAAx] le (two*T) Q) : Γ ⊢[PRAAx]
    le (C*Q*T+H*T) (H*Q) := by
  have doubled : Γ ⊢[PRAAx] le (two*(C*Q*T+H*T)) (two*(H*Q)) := by
    ipra_le (𝔞 Q)*sl hTail+(𝔞 H)*sl hQuery
  exact RationalValueBounds.positive_cancel (zero_lt_succ one) doubled

/-- Both original observations are literal: p is untouched, q is fixed
once sufficient, and every k>=t is allowed. -/
theorem later_cutoff_observations (p q t z R B A k : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A) (htk : Γ ⊢[PRAAx] le t k) (htq : Γ ⊢[PRAAx] le (succ t) q) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data z R B A)) (observation q z R B k A)
      (unit p+unit t) (unit p*unit t) := by
  let C := combined A R
  let H := unit (height k A R)
  let P := unit p
  let Q := unit q
  let T := unit t
  have tail : Γ ⊢[PRAAx] le (C*(two*T)) H :=
    le_congr (congrMul (.eqRefl C) (unit_successor t)) (.eqRefl H) (later_tail_budget t k A R htk)
  have query : Γ ⊢[PRAAx] le (two*T) Q :=
    le_congr (unit_successor t) (.eqRefl Q) (GaussianExponentialReference.unit_monotone htq)
  have scalar := absorb_two_halves C H Q T tail query
  have native := add_le_add_right (H*P*Q*T) (mul_le_mul_right (P*P) scalar)
  have compare : Γ ⊢[PRAAx] le
      (rateNumerator C H p q*(P*T)) ((P+T)*rateDenominator H p q) :=
    le_congr (by dsimp only [rateNumerator,P,Q,T]; ipra_ring) (by dsimp only [rateDenominator,P,Q,T]; ipra_ring) native
  exact GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _
    (GaussianNamedInverseRate.denominator_positive H p q (unit_positive _))
    (positive_product _ _ (unit_positive p) (unit_positive t)) compare
    (GaussianEulerFixedCutoffApproximation.original_observations p q z R B A k h)

theorem successor_precision_observations (p t z R B A k : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A) (htk : Γ ⊢[PRAAx] le t k) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data z R B A)) (observation (succ t) z R B k A)
      (unit p+unit t) (unit p*unit t) :=
  later_cutoff_observations p (succ t) t z R B A k h htk (le_refl _)

def output (p q t z R B A k : PTm n) : PTm n := pairT (ap2 nameF p (data z R B A))
  (pairT (observation q z R B k A) (pairT (unit p+unit t) (unit p*unit t)))
def outputF : PR 8 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
def run (p q t z R B A k : PTm n) : PTm n := PTm.app outputF ![p,q,t,z,R,B,A,k]
theorem program_at (p q t z R B A k : PTm n) : Γ ⊢[PRAAx] run p q t z R B A k ≐ output p q t z R B A k := by
  simpa [run,outputF,output] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) : PTm 8) ![p,q,t,z,R,B,A,k]

theorem actual_original_later_Euler_tail_half_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 0) (var 1) ⟶ le (combined (var 2) (var 3)*unit (succ (var 0))) (unit (height (var 1) (var 2) (var 3)))) :=
  closeUniv 4 (.impI (later_tail_budget _ _ _ _ Prf.hyp0))
theorem original_later_fixed_Euler_observations_dyadic_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((source (var 3) (var 4) (var 5) (var 6) ⋏ le (var 2) (var 7) ⋏ le (succ (var 2)) (var 1)) ⟶
      distanceBounded (ap2 nameF (var 0) (data (var 3) (var 4) (var 5) (var 6)))
        (observation (var 1) (var 3) (var 4) (var 5) (var 7) (var 6))
        (unit (var 0)+unit (var 2)) (unit (var 0)*unit (var 2))) :=
  closeUniv 8 (.impI (later_cutoff_observations _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))
theorem original_successor_precision_fixed_Euler_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((source (var 2) (var 3) (var 4) (var 5) ⋏ le (var 1) (var 6)) ⟶
      distanceBounded (ap2 nameF (var 0) (data (var 2) (var 3) (var 4) (var 5)))
        (observation (succ (var 1)) (var 2) (var 3) (var 4) (var 6) (var 5))
        (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 7 (.impI (successor_precision_observations _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))
theorem actual_original_later_Euler_observation_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) :=
  closeUniv 8 (program_at _ _ _ _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianEulerLaterCutoffObservation
