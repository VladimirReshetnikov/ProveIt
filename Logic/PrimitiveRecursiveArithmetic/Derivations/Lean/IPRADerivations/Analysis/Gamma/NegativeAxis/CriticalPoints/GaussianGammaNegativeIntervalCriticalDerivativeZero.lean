import IPRADerivations.Analysis.Gamma.NegativeAxis.CriticalPoints.GaussianGammaNegativeIntervalCriticalQuotientZero
import IPRADerivations.Analysis.Gamma.NegativeAxis.Values.GaussianGammaNegativeIntervalUniformBounds
import IPRADerivations.Analysis.RationalArithmetic.Representations.GaussianRationalReconstruction

/-!
# Original Gamma unit-step quotients at the negative critical location

The derivative target is the actual negative Gamma times the shifted
digamma. A Gamma bound depending only on the interval and the selected
location's independent shifted residual give a uniform small bound on
that product. The original unscaled unit-step quotients then converge
to zero at the explicit primitive recursive schedule.
-/

set_option autoImplicit false
set_option maxHeartbeats 1700000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalCriticalDerivativeZero

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEuclideanDistanceName (pointCN)
open GaussianFastValueCut (exponent exponent_unit normalizer query_budget)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianGammaNegativeCriticalCorrection (guard)
open GaussianGammaNegativeCriticalGrid (denominator locationF location_at)
open GaussianGammaNegativeCriticalLocation (lower lower_guard location_regular denominator_positive)
open GaussianGammaNegativeCriticalLocationResidual (residualCost original_residual_at)
open GaussianGammaNegativeCriticalLocationZero (inner clock_budget)
open GaussianGammaNegativeIntervalCriticalQuotientZero (stage)
open GaussianGammaNegativeIntervalDigammaRate (minimumDenominator original_derivative_rate)
open GaussianGammaNegativeIntervalUniformBounds (cap grid_bounded)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianNameArithmetic (multiplyModulus multiply_at add_canonical)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNamedInverseRate (diagonal_rate)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qmul qmul_canonical qzero positive_product canonical_congr)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalReciprocal (bounded_product bound_congr)
open GaussianRationalReconstruction (qsub_zero_right)
open RationalValueBounds (positive_cancel)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "QF" => GaussianNamedDifferenceQuotient.nameF gammaF gammaF
local notation "QD" => GaussianGammaNegativeIntervalStep.data
local notation "TF" => GaussianGammaNegativeIntervalDerivativeTarget.nameF
local notation "TD" => GaussianGammaNegativeIntervalDerivativeTarget.data
local notation "SF" => GaussianGammaNegativeCriticalEndpoints.nameF
local notation "SD" => GaussianGammaNegativeCriticalEndpoints.nameData
local notation "GD" => GaussianGammaNegativeIntervalNative.data
local notation "cost" => GaussianGammaNegativeIntervalDerivativeRate.cost

def evaluationClock (p N : PTm n) : PTm n := exponent (cap N) (stage p)
def locationClock (p N : PTm n) : PTm n := inner (evaluationClock p N) N
def argumentNumerator (p N : PTm n) : PTm n := lower (locationClock p N) N
def argumentDenominator (p N : PTm n) : PTm n := denominator (locationClock p N) N
def quotientClock (p N : PTm n) : PTm n := succ (evaluationClock p N)
def demand (p N : PTm n) : PTm n := exponent (cost (argumentNumerator p N) (argumentDenominator p N) N) (stage p)
def step (p N : PTm n) : PTm n := minimumDenominator (demand p N) (argumentNumerator p N) (argumentDenominator p N)
def value (p N : PTm n) : PTm n :=
  ap2 QF (quotientClock p N) (QD (argumentNumerator p N) (argumentDenominator p N) N (step p N))
def nameF : PR 2 := PTm.toPR (value (var 0) (var 1))

@[simp] theorem subst_evaluationClock {k : ℕ} (σ : Fin n → PTm k) (p N : PTm n) :
    Syn.subst σ (evaluationClock p N) = evaluationClock (Syn.subst σ p) (Syn.subst σ N) := by simp [evaluationClock]
@[simp] theorem subst_locationClock {k : ℕ} (σ : Fin n → PTm k) (p N : PTm n) :
    Syn.subst σ (locationClock p N) = locationClock (Syn.subst σ p) (Syn.subst σ N) := by simp [locationClock]
@[simp] theorem subst_argumentNumerator {k : ℕ} (σ : Fin n → PTm k) (p N : PTm n) :
    Syn.subst σ (argumentNumerator p N) = argumentNumerator (Syn.subst σ p) (Syn.subst σ N) := by simp [argumentNumerator]
@[simp] theorem subst_argumentDenominator {k : ℕ} (σ : Fin n → PTm k) (p N : PTm n) :
    Syn.subst σ (argumentDenominator p N) = argumentDenominator (Syn.subst σ p) (Syn.subst σ N) := by simp [argumentDenominator]
@[simp] theorem subst_quotientClock {k : ℕ} (σ : Fin n → PTm k) (p N : PTm n) :
    Syn.subst σ (quotientClock p N) = quotientClock (Syn.subst σ p) (Syn.subst σ N) := by simp [quotientClock]
@[simp] theorem subst_demand {k : ℕ} (σ : Fin n → PTm k) (p N : PTm n) :
    Syn.subst σ (demand p N) = demand (Syn.subst σ p) (Syn.subst σ N) := by
  simp [demand,GaussianGammaNegativeIntervalDerivativeRate.cost,
    GaussianGammaNegativeIntervalDerivativeRate.firstCost,GaussianGammaNegativeIntervalDerivativeRate.secondCost,
    GaussianGammaNegativeIntervalDerivativeRate.eulerCap,GaussianGammaNegativeIntervalInverseStepCoefficient.inverseCap,
    GaussianNameRingLaws.three]
@[simp] theorem subst_step {k : ℕ} (σ : Fin n → PTm k) (p N : PTm n) :
    Syn.subst σ (step p N) = step (Syn.subst σ p) (Syn.subst σ N) := by simp [step,minimumDenominator]
@[simp] theorem subst_value {k : ℕ} (σ : Fin n → PTm k) (p N : PTm n) :
    Syn.subst σ (value p N) = value (Syn.subst σ p) (Syn.subst σ N) := by
  simp [value,GaussianGammaNegativeIntervalStep.data,GaussianGammaNegativeIntervalStep.denominator,
    GaussianGammaDigammaStep.neighborNumerator,GaussianGammaNegativeIntervalNative.data,
    GaussianGammaNegativeIntervalNative.argument]

theorem selected_argument (p N : PTm n) : Γ ⊢[PRAAx] ap2 locationF (locationClock p N) N ≐
    qsub (fraction (argumentNumerator p N) (argumentDenominator p N)) (fraction (succ N) one) :=
  location_at (locationClock p N) N

theorem name_at (p N : PTm n) : Γ ⊢[PRAAx] ap2 nameF p N ≐ value p N := by
  simpa only [nameF,ap2,subst_value,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    (toPR_eq (Γ := Γ) (value (var 0) (var 1) : PTm 2) ![p,N])

private theorem unit_le_exponent (L p : PTm n) : Γ ⊢[PRAAx] le (unit p) (unit (exponent L p)) :=
  le_congr (.eqRefl _) (exponent_unit L p).eqSymm
    (by ipra_le 𝔞(unit p)*sl (unit_positive (normalizer L)))

private theorem stage_unit (p : PTm n) : Γ ⊢[PRAAx] unit (stage p) ≐ num 4*unit p :=
  (pw_succ two (succ p)).eqTrans ((congrMul (pw_succ two p) (.eqRefl _)).eqTrans (by unfold unit; ipra_ring))

theorem shifted_small (p q N : PTm n) (hq : Γ ⊢[PRAAx] le (two*unit (evaluationClock p N)) (unit q)) :
    Γ ⊢[PRAAx] bounded (ap2 SF q (SD (argumentNumerator p N) (argumentDenominator p N) N))
      one (unit (evaluationClock p N)) := by
  let L := evaluationClock p N
  let k := locationClock p N
  let B := argumentDenominator p N
  let a := argumentNumerator p N
  let U := unit L
  let V := unit q
  let C := residualCost N
  let y := ap2 SF q (SD a B N)
  have hb : Γ ⊢[PRAAx] le one B := denominator_positive k N
  have hv := unit_positive (Γ := Γ) q
  have hu := unit_positive (Γ := Γ) L
  have hL : Γ ⊢[PRAAx] le (two*C*U) B := clock_budget L N
  have hQ : Γ ⊢[PRAAx] le (two*U) V := hq
  have hr := distance_radius_mono y qzero _ _ one U (positive_product _ _ hb hv) hu
    (by change Γ ⊢[PRAAx] le ((C*V+B)*U) (one*(B*V))
        apply positive_cancel (c := two) (by ipra_le 1)
        ipra_le 𝔞(V)*sl hL+𝔞(B)*sl hQ) (original_residual_at k q N)
  have e := qsub_zero_right (Γ := Γ) y (add_canonical GaussianGammaDigammaNative.nameF constantF _ _ q)
  exact bound_congr e (.eqRefl _) (.eqRefl _) hr

theorem target_small (p N : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (ap2 TF (quotientClock p N) (TD (argumentNumerator p N) (argumentDenominator p N) N))
      qzero one (unit (stage p)) := by
  let a := argumentNumerator p N
  let b := argumentDenominator p N
  let k := locationClock p N
  let L := evaluationClock p N
  let t := quotientClock p N
  let x := GD a b N
  let y := SD a b N
  let M := multiplyModulus gammaF SF x y
  let j := exponent M t
  let g := ap2 gammaF j x
  let ψ := ap2 SF j y
  let z := ap2 TF t (TD a b N)
  let R := cap N
  let U := unit L
  let S := unit (stage p)
  have hu := unit_positive (Γ := Γ) L
  have ht : Γ ⊢[PRAAx] unit t ≐ two*U := (pw_succ two L).eqTrans (mul_comm _ _)
  have hj : Γ ⊢[PRAAx] le (two*U) (unit j) :=
    le_congr ht (.eqRefl _) (unit_le_exponent M t)
  have hψ : Γ ⊢[PRAAx] bounded ψ one U := shifted_small p j N hj
  have hg : Γ ⊢[PRAAx] bounded g R one := grid_bounded k j N
  have normalized : Γ ⊢[PRAAx] bounded (qmul g ψ) (R*one) (one*U) :=
    bounded_product _ _ _ _ _ _ (le_refl one) hu hg hψ
  have hRate : Γ ⊢[PRAAx] le (R*S) U := query_budget R (stage p)
  have small := bounded_radius_mono (qmul g ψ) (R*one) (one*U) one S
    (le_congr (.eqRefl _) (one_mul _).eqSymm hu) (unit_positive _) (by ipra_le sl hRate) normalized
  have hc := qmul_canonical (Γ := Γ) g ψ
  have read : Γ ⊢[PRAAx] z ≐ qmul g ψ :=
    (multiply_at gammaF SF x y t).eqTrans (GaussianExponentialReference.recode_fixed _ hc)
  have hzero := qsub_zero_right z (canonical_congr read hc)
  exact bound_congr (read.eqSymm.eqTrans hzero.eqSymm) (.eqRefl _) (.eqRefl _) small

theorem target_error (p N : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (value p N) (ap2 TF (quotientClock p N) (TD (argumentNumerator p N) (argumentDenominator p N) N))
      two (unit (stage p)) := by
  let a := argumentNumerator p N
  let b := argumentDenominator p N
  let s := stage p
  let L := evaluationClock p N
  let t := quotientClock p N
  let U := unit s
  let V := unit t
  let P := unit (demand p N)
  let C := cost a b N
  let D := step p N
  have h : Γ ⊢[PRAAx] guard a b := lower_guard (locationClock p N) N
  have hp := unit_positive (Γ := Γ) (demand p N)
  have hq := unit_positive (Γ := Γ) t
  have hu := unit_positive (Γ := Γ) s
  have demandBound : Γ ⊢[PRAAx] le (C*U) P := query_budget C s
  have grow : Γ ⊢[PRAAx] le U (unit L) := unit_le_exponent (cap N) s
  have e : Γ ⊢[PRAAx] V ≐ unit L*two := pw_succ two L
  have clockBound : Γ ⊢[PRAAx] le (two*U) V :=
    le_congr (.eqRefl _) e.eqSymm (by ipra_le 2*sl grow)
  have r := original_derivative_rate (demand p N) a b N D h (le_refl D)
  have diag := diagonal_rate QF TF (QD a b N D) (TD a b N) C P t hp r
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hp hq) hu
    (by change Γ ⊢[PRAAx] le ((C*V+two*P)*U) (two*(P*V))
        ipra_le 𝔞(V)*sl demandBound+𝔞(P)*sl clockBound) diag

theorem value_bound (p N : PTm n) : Γ ⊢[PRAAx] distanceBounded (value p N) qzero one (unit p) := by
  let s := stage p
  have h := unit_positive (Γ := Γ) s
  have e := natEq (stage_unit (Γ := Γ) p)
  have joined := distance_triangle_same _ _ _ _ _ _ h (target_error p N) (target_small p N)
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

theorem actual_original_negative_Gamma_critical_derivative_zero_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
      (pointCN locationF (var 0) ⋏ (pointCN nameF (var 0) ⋏ crossEquivalent nameF constantF (var 0) qzero)) :=
  closeUniv 1 (.andI (location_regular _) (.andI (name_regular _) (zero_cross _)))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalCriticalDerivativeZero
