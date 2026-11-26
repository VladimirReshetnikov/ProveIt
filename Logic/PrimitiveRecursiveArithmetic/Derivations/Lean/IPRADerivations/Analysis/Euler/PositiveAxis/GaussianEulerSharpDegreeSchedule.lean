import IPRADerivations.Analysis.Euler.Integration.GaussianEulerDecayFactorBounds
import IPRADerivations.Analysis.Integration.GaussianMonomialDecayQuadrature
import IPRADerivations.Analysis.Integration.GaussianCompactRiemannSplit

/-!
# Literal finite-degree schedule for the sharp Euler integral estimate

The requested degree is exactly 4(C_R+D_R+p+10)2^(p+4).
Both coefficient budgets are proved in numerical arithmetic. The actual
decay sampler at N/4 equals its integer-time sampler at H=N/4; its
original observation error is retained before an explicit retiming.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerSharpDegreeSchedule

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded qnegative)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianDominantPairAlgebra (radiusPoint radius_bounded)
open GaussianEulerIntegrandName (decayF decayData decayPoint)
open GaussianGammaCanonicalExponent (constantF)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def coefficient (R : PTm n) : PTm n := one+GaussianMonomialDecayQuadrature.cap (R+two)
def tailCoefficient (R : PTm n) : PTm n := GaussianGammaIntegralCutoffs.tailCoefficient R
def size (p R : PTm n) : PTm n := coefficient R+tailCoefficient R+p+num 10
def height (p R : PTm n) : PTm n := size p R*unit (p+num 4)
def degree (p R : PTm n) : PTm n := num 4*size p R*unit (p+num 4)
def observationClock (p R : PTm n) : PTm n := GaussianFastValueCut.exponent (two*tailCoefficient R) (p+num 4)
def weightedDecay (p R q : PTm n) : PTm n := qmul (radiusPoint (tailCoefficient R) one)
  (ap2 decayF q (decayData (degree p R) (num 4)))
@[simp] theorem subst_coefficient {m : ℕ} (σ : Fin n → PTm m) (R : PTm n) :
    Syn.subst σ (coefficient R) = coefficient (Syn.subst σ R) := by
  simp [coefficient,GaussianMonomialDecayQuadrature.cap,GaussianGammaIntegralCutoffs.tailCoefficient]
@[simp] theorem subst_tailCoefficient {m : ℕ} (σ : Fin n → PTm m) (R : PTm n) :
    Syn.subst σ (tailCoefficient R) = tailCoefficient (Syn.subst σ R) := by
  simp [tailCoefficient,GaussianGammaIntegralCutoffs.tailCoefficient]
@[simp] theorem subst_size {m : ℕ} (σ : Fin n → PTm m) (p R : PTm n) :
    Syn.subst σ (size p R) = size (Syn.subst σ p) (Syn.subst σ R) := by simp [size]
@[simp] theorem subst_height {m : ℕ} (σ : Fin n → PTm m) (p R : PTm n) :
    Syn.subst σ (height p R) = height (Syn.subst σ p) (Syn.subst σ R) := by simp [height]
@[simp] theorem subst_degree {m : ℕ} (σ : Fin n → PTm m) (p R : PTm n) :
    Syn.subst σ (degree p R) = degree (Syn.subst σ p) (Syn.subst σ R) := by simp [degree]

theorem four_positive : Γ ⊢[PRAAx] le one (num 4 : PTm n) :=
  le_of_eq_add (d := num 3) (by ipra_ring)
theorem size_positive (p R : PTm n) : Γ ⊢[PRAAx] le one (size p R) := by
  unfold size
  ipra_le 𝔞(coefficient R)+𝔞(tailCoefficient R)+𝔞 p+9
theorem height_positive (p R : PTm n) : Γ ⊢[PRAAx] le one (height p R) :=
  positive_product _ _ (size_positive p R) (unit_positive _)
theorem degree_is_four_height (p R : PTm n) : Γ ⊢[PRAAx] degree p R ≐ num 4*height p R := by
  unfold degree height
  ipra_ring
theorem degree_positive (p R : PTm n) : Γ ⊢[PRAAx] le one (degree p R) :=
  le_congr (.eqRefl _) (degree_is_four_height p R).eqSymm
    (positive_product _ _ four_positive (height_positive p R))

/-- Exact natural clearing of C_R/N <= 2^-(p+3). -/
theorem coefficient_budget (p R : PTm n) : Γ ⊢[PRAAx]
    le (coefficient R*unit (p+num 3)) (degree p R) := by
  have cs : Γ ⊢[PRAAx] le (coefficient R) (size p R) :=
    le_of_eq_add (d := tailCoefficient R+p+num 10) (by unfold size; ipra_ring)
  have sf : Γ ⊢[PRAAx] le (size p R) (num 4*size p R) :=
    le_of_eq_add (d := num 3*size p R) (by ipra_ring)
  have grow := GaussianExponentialReference.unit_monotone (Γ := Γ)
    (le_of_eq_add (a := p+num 3) (b := p+num 4) (d := one) (by ipra_ring))
  exact AnalyticNumberTheory.PhiLower.le_mul_mono (le_trans cs sf) grow

theorem original_coefficient_fraction_bound (p R : PTm n) : Γ ⊢[PRAAx]
    bounded (fraction (coefficient R) (degree p R)) one (unit (p+num 3)) :=
  bound_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point _ _ (degree_positive p R)).eqSymm (.eqRefl _) (.eqRefl _)
    (bounded_radius_mono _ _ _ _ _ (degree_positive p R) (unit_positive _)
      (le_congr (.eqRefl _) (one_mul _).eqSymm (coefficient_budget p R))
      (radius_bounded (coefficient R) (degree p R) (degree_positive p R)))

/-- The arithmetic leaves a further dyadic bit for the actual sampler. -/
theorem tail_budget (p R : PTm n) : Γ ⊢[PRAAx]
    le (tailCoefficient R*unit (p+num 4)) (unit (height p R)) := by
  have power := LeanProofs.IPRA.AnalyticNumberTheory.ZetaFiniteContract.le_pow_self (Γ := Γ) (tailCoefficient R)
  have first : Γ ⊢[PRAAx] le (tailCoefficient R*unit (p+num 4)) (unit (p+num 4+tailCoefficient R)) :=
    le_congr (.eqRefl _) ((mul_comm _ _).eqTrans (pw_add two (p+num 4) (tailCoefficient R)).eqSymm)
      (mul_le_mul_right (unit (p+num 4)) power)
  have small : Γ ⊢[PRAAx] le (p+num 4+tailCoefficient R) (size p R) := by
    unfold size
    ipra_le 𝔞(coefficient R)+6
  have grow : Γ ⊢[PRAAx] le (size p R) (height p R) :=
    le_congr (one_mul _) (by unfold height; ipra_ring) (mul_le_mul_right (size p R) (unit_positive (p+num 4)))
  exact le_trans first (GaussianExponentialReference.unit_monotone (le_trans small grow))

theorem original_quarter_degree_fraction (p R : PTm n) : Γ ⊢[PRAAx]
    fraction (degree p R) (num 4) ≐ fraction (height p R) one :=
  (GaussianCompactRiemannName.fraction_congr _ _ _ _ (degree_is_four_height p R) (by ipra_ring : Γ ⊢[PRAAx] (num 4 : PTm n) ≐ num 4*one)).eqTrans
    (GaussianCompactRiemannSplit.fraction_cancel (num 4) (height p R) one four_positive (le_refl one))

/-- This is equality of the literal original decay data and samples,
including their internally computed radii. -/
theorem original_quarter_degree_sample (p R q : PTm n) : Γ ⊢[PRAAx]
    ap2 decayF q (decayData (degree p R) (num 4)) ≐ ap2 decayF q (decayData (height p R) one) := by
  have same := Prf.eqCongr (Γ := Γ) (Ax := PRAAx)
    (GaussianGammaFiniteApproximantName.exponentialInputData constantF (qnegative (var 0)) : PTm 1)
    (σ := ![fraction (degree p R) (num 4)]) (σ' := ![fraction (height p R) one])
    (fun i => by fin_cases i; exact original_quarter_degree_fraction p R)
  exact congrAp2 decayF (.eqRefl q) (by
    simpa [decayData,decayPoint,GaussianGammaFiniteApproximantName.exponentialInputData] using same)

/-- D_R exp(-N/4) <= 2^-(p+4) + 2D_R 2^-q, at the
unchanged original q-th exponential observation. -/
theorem original_weighted_decay_bound (p R q : PTm n) : Γ ⊢[PRAAx]
    bounded (weightedDecay p R q) (unit q+two*tailCoefficient R*unit (p+num 4)) (unit (p+num 4)*unit q) := by
  have raw := bounded_product (Γ := Γ) (radiusPoint (tailCoefficient R) one) _ _ one _ _ (le_refl one)
    (positive_product _ _ (unit_positive (height p R)) (unit_positive q))
    (radius_bounded (tailCoefficient R) one (le_refl one))
    (GaussianEulerDecayFactorBounds.original_integer_decay_bound (height p R) q)
  have actual := bound_congr (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) (original_quarter_degree_sample p R q)).eqSymm
    (.eqRefl _) (one_mul _) raw
  apply bounded_radius_mono _ _ _ _ _ (positive_product _ _ (unit_positive _) (unit_positive q))
    (positive_product _ _ (unit_positive _) (unit_positive q)) _ actual
  ipra_le (𝔞(unit q)*𝔞(unit q))*sl (tail_budget p R)

theorem observation_budget (p R : PTm n) : Γ ⊢[PRAAx]
    le (two*tailCoefficient R*unit (p+num 4)) (unit (observationClock p R)) :=
  GaussianFastValueCut.query_budget _ _

/-- A computed original observation meets the requested sharp tail
budget itself, after paying the genuine observation error. -/
theorem original_fast_decay_bound (p R : PTm n) : Γ ⊢[PRAAx]
    bounded (weightedDecay p R (observationClock p R)) one (unit (p+num 3)) := by
  have next : Γ ⊢[PRAAx] unit (p+num 4) ≐ two*unit (p+num 3) :=
    ((congrAp2 powF (by ipra_ring : Γ ⊢[PRAAx] p+num 4 ≐ ConciseIPRA.PTm.succ (p+num 3)) (.eqRefl two)).eqTrans
      (pw_succ two (p+num 3))).eqTrans (mul_comm _ _)
  apply bounded_radius_mono _ _ _ _ _ (positive_product _ _ (unit_positive _) (unit_positive _)) (unit_positive _) _
    (original_weighted_decay_bound p R (observationClock p R))
  have gap := mul_le_mul_right (unit (p+num 3)) (observation_budget (Γ := Γ) p R)
  have both := add_le_add_right (unit (observationClock p R)*unit (p+num 3)) gap
  exact le_congr (by ipra_ring) (by
    apply deriveNat
    have e := natEq next
    ipra_simps
    rw [e]
    ring) both

theorem original_sharp_Euler_degree_coefficient_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (coefficient (var 1)*unit ((var 0)+num 3)) (degree (var 0) (var 1))) := closeUniv 2 (coefficient_budget _ _)
theorem original_sharp_Euler_degree_decay_observation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (bounded (weightedDecay (var 0) (var 1) (observationClock (var 0) (var 1))) one (unit ((var 0)+num 3))) :=
  closeUniv 2 (original_fast_decay_bound _ _)
theorem original_sharp_Euler_degree_decay_slack_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (bounded (weightedDecay (var 0) (var 1) (var 2))
      (unit (var 2)+two*tailCoefficient (var 1)*unit ((var 0)+num 4)) (unit ((var 0)+num 4)*unit (var 2))) :=
  closeUniv 3 (original_weighted_decay_bound _ _ _)
theorem original_sharp_Euler_quarter_degree_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap2 decayF (var 2) (decayData (degree (var 0) (var 1)) (num 4)) ≐
      ap2 decayF (var 2) (decayData (height (var 0) (var 1)) one)) :=
  closeUniv 3 (original_quarter_degree_sample _ _ _)

end LeanProofs.IPRA.Analysis.GaussianEulerSharpDegreeSchedule
