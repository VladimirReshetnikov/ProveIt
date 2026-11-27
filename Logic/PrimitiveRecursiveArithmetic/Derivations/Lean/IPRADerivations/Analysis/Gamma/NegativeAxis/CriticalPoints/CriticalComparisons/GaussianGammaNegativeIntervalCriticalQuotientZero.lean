import IPRADerivations.Analysis.Gamma.Digamma.NegativeAxis.GaussianGammaNegativeIntervalDigammaRate
import IPRADerivations.Analysis.Gamma.CriticalPoints.NegativeIntervals.Location.GaussianGammaNegativeCriticalLocationZero

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

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianFastValueCut (exponent query_budget)
open GaussianGammaCanonicalExponent (constantF)
open GaussianGammaNegativeCriticalCorrection (guard)
open GaussianGammaNegativeCriticalGrid (denominator locationF location_at)
open GaussianGammaNegativeCriticalLocation (lower lower_guard location_regular)
open GaussianGammaNegativeCriticalLocationZero (regular_zero_of_sample_error inner)
open GaussianGammaNegativeIntervalDigammaRate (quotientF quotientData cost minimumDenominator original_rate)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNamedInverseRate (diagonal_rate)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (qzero positive_product)
open GaussianRationalMetric (distanceBounded qsub)

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

ipra_subst stage
ipra_subst locationClock
ipra_subst argumentNumerator
ipra_subst argumentDenominator
ipra_subst demand [cost, GaussianGammaNegativeIntervalDerivativeRate.cost, GaussianGammaNegativeIntervalDerivativeRate.firstCost, GaussianGammaNegativeIntervalDerivativeRate.secondCost, GaussianGammaNegativeIntervalDerivativeRate.eulerCap, GaussianGammaNegativeIntervalInverseStepCoefficient.inverseCap, GaussianGammaNegativeIntervalDerivativeTarget.reciprocalData, GaussianGammaNegativeIntervalNative.argument, GaussianNameRingLaws.three]
ipra_subst step [minimumDenominator]
ipra_subst value [quotientData, GaussianGammaNegativeIntervalStep.data, GaussianGammaNegativeIntervalStep.denominator, GaussianGammaDigammaStep.neighborNumerator, GaussianGammaNegativeIntervalDerivativeTarget.reciprocalData, GaussianGammaNegativeIntervalNative.data, GaussianGammaNegativeIntervalNative.argument]

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

/-- Two error units through the quotient model and one to zero fit within the
original precision budget after the common two-step clock shift. -/
theorem zero_error_from_stage (p x y : PTm n)
    (hxy : Γ ⊢[PRAAx] distanceBounded x y two (unit (stage p)))
    (hy : Γ ⊢[PRAAx] distanceBounded y qzero one (unit (stage p))) :
    Γ ⊢[PRAAx] distanceBounded x qzero one (unit p) := by
  have h := unit_positive (Γ := Γ) (stage p)
  have e := natEq (stage_unit (Γ := Γ) p)
  exact distance_radius_mono _ _ _ _ _ _ h (unit_positive p)
    (by ipra_le 𝔞(unit p) using rw [e]; ring)
    (distance_triangle_same _ _ _ _ _ _ h hxy hy)

theorem value_bound (p N : PTm n) : Γ ⊢[PRAAx] distanceBounded (value p N) qzero one (unit p) :=
  zero_error_from_stage p _ _ (shifted_value_error p N)
    (GaussianGammaNegativeCriticalLocationZero.value_bound (stage p) N)

theorem name_regular (N : PTm n) : Γ ⊢[PRAAx] pointCN nameF N :=
  (regular_zero_of_sample_error nameF N _ (fun p => name_at p _) (fun p => value_bound p _)).andE₁

theorem zero_cross (N : PTm n) : Γ ⊢[PRAAx] crossEquivalent nameF constantF N qzero :=
  (regular_zero_of_sample_error nameF N _ (fun p => name_at p _) (fun p => value_bound p _)).andE₂

theorem actual_original_negative_Gamma_critical_quotient_zero_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
      (pointCN locationF (var 0) ⋏ (pointCN nameF (var 0) ⋏ crossEquivalent nameF constantF (var 0) qzero)) :=
  closeUniv 1 (.andI (location_regular _) (.andI (name_regular _) (zero_cross _)))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalCriticalQuotientZero
