import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaNegativeIntervalDigammaRate
import IPRADerivations.Analysis.Gamma.CriticalPoints.GaussianGammaNegativeCriticalLocationZero

/-!
# The original normalized unit-step quotients at the negative critical location

Each observation uses the actual negative Gamma quotient at the selected
rational location and the original reciprocal Gamma at that same input.
An explicit inner precision for the location and a separate denominator
for the increment make the normalized quotient (2^{-p})-close to zero.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalCriticalQuotientZero

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianFastValueCut (exponent query_budget)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianGammaNegativeCriticalCorrection (guard)
open GaussianGammaNegativeCriticalGrid (denominator locationF location_at)
open GaussianGammaNegativeCriticalLocation (lower lower_guard location_regular)
open GaussianGammaNegativeCriticalLocationZero (inner)
open GaussianGammaNegativeIntervalDigammaRate (quotientF quotientData cost minimumDenominator original_rate)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNamedInverseRate (diagonal_rate)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qzero positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "SF" => GaussianGammaNegativeCriticalEndpoints.nameF
local notation "SD" => GaussianGammaNegativeCriticalEndpoints.nameData

def stage (p : PTm n) : PTm n := succ (succ p)
def locationClock (p N : PTm n) : PTm n := inner (stage p) N
def argumentNumerator (p N : PTm n) : PTm n := lower (locationClock p N) N
def argumentDenominator (p N : PTm n) : PTm n := denominator (locationClock p N) N
def demand (p N : PTm n) : PTm n := exponent (cost (argumentNumerator p N) (argumentDenominator p N) N) (stage p)
def step (p N : PTm n) : PTm n := minimumDenominator (demand p N) (argumentNumerator p N) (argumentDenominator p N)
def value (p N : PTm n) : PTm n :=
  ap2 quotientF (succ (stage p)) (quotientData (argumentNumerator p N) (argumentDenominator p N) N (step p N))
def nameF : PR 2 := PTm.toPR (value (var 0) (var 1))

@[simp] theorem subst_stage {k : ℕ} (σ : Fin n → PTm k) (p : PTm n) :
    Syn.subst σ (stage p) = stage (Syn.subst σ p) := by simp [stage]
@[simp] theorem subst_locationClock {k : ℕ} (σ : Fin n → PTm k) (p N : PTm n) :
    Syn.subst σ (locationClock p N) = locationClock (Syn.subst σ p) (Syn.subst σ N) := by simp [locationClock]
@[simp] theorem subst_argumentNumerator {k : ℕ} (σ : Fin n → PTm k) (p N : PTm n) :
    Syn.subst σ (argumentNumerator p N) = argumentNumerator (Syn.subst σ p) (Syn.subst σ N) := by simp [argumentNumerator]
@[simp] theorem subst_argumentDenominator {k : ℕ} (σ : Fin n → PTm k) (p N : PTm n) :
    Syn.subst σ (argumentDenominator p N) = argumentDenominator (Syn.subst σ p) (Syn.subst σ N) := by simp [argumentDenominator]
@[simp] theorem subst_demand {k : ℕ} (σ : Fin n → PTm k) (p N : PTm n) :
    Syn.subst σ (demand p N) = demand (Syn.subst σ p) (Syn.subst σ N) := by
  simp [demand,cost,GaussianGammaNegativeIntervalDerivativeRate.cost,
    GaussianGammaNegativeIntervalDerivativeRate.firstCost,GaussianGammaNegativeIntervalDerivativeRate.secondCost,
    GaussianGammaNegativeIntervalDerivativeRate.eulerCap,GaussianGammaNegativeIntervalInverseStepCoefficient.inverseCap,
    GaussianGammaNegativeIntervalDerivativeTarget.reciprocalData,GaussianGammaNegativeIntervalNative.argument,
    GaussianNameRingLaws.three]
@[simp] theorem subst_step {k : ℕ} (σ : Fin n → PTm k) (p N : PTm n) :
    Syn.subst σ (step p N) = step (Syn.subst σ p) (Syn.subst σ N) := by simp [step,minimumDenominator]
@[simp] theorem subst_value {k : ℕ} (σ : Fin n → PTm k) (p N : PTm n) :
    Syn.subst σ (value p N) = value (Syn.subst σ p) (Syn.subst σ N) := by
  simp [value,quotientData,GaussianGammaNegativeIntervalStep.data,GaussianGammaNegativeIntervalStep.denominator,
    GaussianGammaDigammaStep.neighborNumerator,GaussianGammaNegativeIntervalDerivativeTarget.reciprocalData,
    GaussianGammaNegativeIntervalNative.data,GaussianGammaNegativeIntervalNative.argument]

theorem selected_argument (p N : PTm n) : Γ ⊢[PRAAx] ap2 locationF (locationClock p N) N ≐
    qsub (fraction (argumentNumerator p N) (argumentDenominator p N)) (fraction (succ N) one) :=
  location_at (locationClock p N) N

theorem name_at (p N : PTm n) : Γ ⊢[PRAAx] ap2 nameF p N ≐ value p N := by
  simpa only [nameF,ap2,subst_value,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    (toPR_eq (Γ := Γ) (value (var 0) (var 1) : PTm 2) ![p,N])

theorem shifted_value_error (p N : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (value p N) (GaussianGammaNegativeCriticalLocationZero.value (stage p) N)
      two (unit (stage p)) := by
  let a := argumentNumerator p N
  let b := argumentDenominator p N
  let s := stage p
  let t := succ s
  let P := unit (demand p N)
  let U := unit s
  let V := unit t
  let C := cost a b N
  let D := step p N
  have h : Γ ⊢[PRAAx] guard a b := lower_guard (locationClock p N) N
  have hp := unit_positive (Γ := Γ) (demand p N)
  have hq := unit_positive (Γ := Γ) t
  have hu := unit_positive (Γ := Γ) s
  have bound : Γ ⊢[PRAAx] le (C*U) P := query_budget C s
  have e := natEq (show Γ ⊢[PRAAx] V ≐ U*two from pw_succ two s)
  have r := original_rate (demand p N) a b N D h (le_refl D)
  have diag := diagonal_rate quotientF SF (quotientData a b N D) (SD a b N) C P t hp r
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hp hq) hu
    (by change Γ ⊢[PRAAx] le ((C*V+two*P)*U) (two*(P*V))
        ipra_le 𝔞(V)*sl bound using rw [e]; ring) diag

private theorem stage_unit (p : PTm n) : Γ ⊢[PRAAx] unit (stage p) ≐ num 4*unit p :=
  (pw_succ two (succ p)).eqTrans ((congrMul (pw_succ two p) (.eqRefl _)).eqTrans (by unfold unit; ipra_ring))

theorem value_bound (p N : PTm n) : Γ ⊢[PRAAx] distanceBounded (value p N) qzero one (unit p) := by
  let s := stage p
  have h := unit_positive (Γ := Γ) s
  have e := natEq (stage_unit (Γ := Γ) p)
  have joined := distance_triangle_same _ _ _ _ _ _ h (shifted_value_error p N)
    (GaussianGammaNegativeCriticalLocationZero.value_bound s N)
  exact distance_radius_mono _ _ _ _ _ _ h (unit_positive p)
    (by ipra_le 𝔞(unit p) using rw [e]; ring) joined

theorem name_regular (N : PTm n) : Γ ⊢[PRAAx] pointCN nameF N := by
  refine .allI (.allI ?_)
  let W := Syn.shift (Syn.shift N)
  let p : PTm (n+2) := var 1
  let q : PTm (n+2) := var 0
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have bp := value_bound (Γ := Δ) p W
  have bq := value_bound (Γ := Δ) q W
  have joined := GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ (unit_positive p) (unit_positive q)
    bp (distance_symmetric _ _ _ _ (unit_positive q) bq)
  change Δ ⊢[PRAAx] distanceBounded (ap2 nameF p W) (ap2 nameF q W) (unit p+unit q) (unit p*unit q)
  exact distance_congr (name_at p W).eqSymm (name_at q W).eqSymm (by ipra_ring) (.eqRefl _) joined

theorem zero_cross (N : PTm n) : Γ ⊢[PRAAx] crossEquivalent nameF constantF N qzero := by
  refine .allI (.allI ?_)
  let W := Syn.shift (Syn.shift N)
  let p : PTm (n+2) := var 1
  let q : PTm (n+2) := var 0
  let Z : PTm (n+2) := qzero
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have dp := value_bound (Γ := Δ) p W
  have joined := distance_radius_mono _ _ _ _ (unit p+unit q) (unit p*unit q)
    (unit_positive p) (positive_product _ _ (unit_positive p) (unit_positive q))
    (by ipra_le Groth.ι (Q.mk Δ (unit p))^2) dp
  simpa only [p,q,W,Z,Syn.shift,GaussianRationalHorner.subst_qzero] using
    distance_congr (name_at p W).eqSymm (constant_at q Z).eqSymm (.eqRefl _) (.eqRefl _) joined

theorem actual_original_negative_Gamma_critical_quotient_zero_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
      (pointCN locationF (var 0) ⋏ (pointCN nameF (var 0) ⋏ crossEquivalent nameF constantF (var 0) qzero)) :=
  closeUniv 1 (.andI (location_regular _) (.andI (name_regular _) (zero_cross _)))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalCriticalQuotientZero
