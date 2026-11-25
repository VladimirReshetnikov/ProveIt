import IPRADerivations.Analysis.GaussianLogGammaEulerChartAgreement
import IPRADerivations.Analysis.GaussianLogGammaEulerNamed
import IPRADerivations.Analysis.GaussianLogGammaEulerRecurrence
import IPRADerivations.Analysis.GaussianLogGammaEulerShiftedChart
import IPRADerivations.Analysis.GaussianNamedDifferenceRate
import IPRADerivations.Analysis.GaussianNamedRateComposition
import IPRADerivations.Analysis.GaussianRightHalfPlaneLogarithmNamed

/-!
# The original unit-shift identity for named log-Gamma

Freeze the two cofinal log-Gamma evaluations and the canonical logarithm
at a shared input observation. The actual shifted name reads the same
original observation as the base chart, at the addition clock. The
checked rational recurrence then identifies the named values exactly.
-/

set_option autoImplicit false
set_option maxHeartbeats 330000

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerNamedRecurrence

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEulerNamedShiftInput (shiftF shiftData clock_later)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCompactCutoffAlignment (cross_data_congr)
open GaussianLogGammaEulerCofinal (canonicalData canonical_regular)
open GaussianLogGammaEulerNamed (rationalMap source late_rational_rate)
open GaussianLogGammaEulerShiftedChart (late_samples shift_source shiftedPoint)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm)
open GaussianNameRingLaws (equivalent_of_envelope)
open GaussianNamedInverseRate (independentRate diagonal_rate)
open GaussianNamedRightHalfPlane (radius)
open GaussianNamedRightHalfPlaneSigned (certificate realNumerator imagNumerator denominator sign)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalHorner (ofGaussian_canonical positive_product)
open GaussianRationalMetric (distanceBounded)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "C" => GaussianLogGammaEulerCofinal.nameF
local notation "Log" => GaussianRightHalfPlaneLogarithm.nameF
local notation "logF" => GaussianRightHalfPlaneLogarithmNamed.nameF
local notation "logData" => GaussianRightHalfPlaneLogarithmNamed.data
local notation "gammaF" => GaussianLogGammaEulerNamed.nameF
local notation "gammaData" => GaussianLogGammaEulerNamed.data
local notation "dat" => GaussianLogGammaEulerNamed.pointData
local notation "diffF" => GaussianNamedDifference.nameF
local notation "diffData" => GaussianNamedDifference.data
local notation "clockΓ" => GaussianNamedRightHalfPlaneLift.clock rationalMap
local notation "clockLog" => GaussianRightHalfPlaneLogarithmNamed.clock
local notation "shiftClock" => GaussianEulerNamedShiftInput.clock

def nameF (f : PR 2) : PR 2 := diffF (gammaF (shiftF f)) (gammaF f)

def data (x M R S : PTm n) : PTm n := diffData (gammaData (shiftData x) M S) (gammaData x M R)

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (x M R S : PTm n) :
    Syn.subst σ (data x M R S) = data (Syn.subst σ x) (Syn.subst σ M) (Syn.subst σ R) (Syn.subst σ S) := by
  simp [data]

private theorem rational_regular (q R K : PTm n) (h : Γ ⊢[PRAAx] certificate q R K) : Γ ⊢[PRAAx] pointCN C (dat q) :=
  canonical_regular _ _ _ _ h.andE₁.andE₁

private theorem freeze_chart (f : PR 2) (t k x M R z : PTm n)
    (h : Γ ⊢[PRAAx] source f x M R) (hk : Γ ⊢[PRAAx] le (clockΓ t M R) k)
    (hz : Γ ⊢[PRAAx] crossEquivalent C C z (dat (ap2 f k x))) : Γ ⊢[PRAAx]
    independentRate (gammaF f) C (gammaData x M R) z one (unit t) := by
  let q := ap2 f k x
  have aligned := cross_data_congr C C z z (dat q) _ (.eqRefl _) (GaussianLogGammaEulerNamed.rational_data_at q).eqSymm hz
  exact GaussianNamedRateTransport.transport _ _ _ _ _ _ _ _ _ _ (unit_positive t)
    (late_rational_rate f t k x M R h hk)
    (cross_refl _ _ (GaussianLogGammaEulerNamed.name_regular f x M R h)) aligned

private theorem shifted_gamma_chart (q r R S K : PTm n)
    (hq : Γ ⊢[PRAAx] certificate q R K) (hr : Γ ⊢[PRAAx] certificate r S K)
    (hshift : Γ ⊢[PRAAx] r ≐ shiftedPoint q) : Γ ⊢[PRAAx]
    crossEquivalent C C (canonicalData (realNumerator q+denominator q) (imagNumerator q) (denominator q) (sign q)) (dat r) := by
  let A := realNumerator q+denominator q
  let B := imagNumerator q
  let D := denominator q
  let s := sign q
  have src : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source A D s :=
    .andI (.andI (le_trans hq.andE₁.andE₁.andE₁.andE₁ (le_add_right _ _)) hq.andE₁.andE₁.andE₁.andE₂) hq.andE₁.andE₁.andE₂
  have fix := GaussianExponentialReference.recode_fixed (shiftedPoint q)
    (ofGaussian_canonical (GaussianLogGammaEulerResidualDomain.native A B s) D src.andE₂)
  have same := hr.andE₂.andE₂.eqTrans ((GaussianNameArithmetic.recode_congr hshift).eqTrans fix)
  exact GaussianLogGammaEulerChartAgreement.canonical_agreement A B D s
    (realNumerator r) (imagNumerator r) (denominator r) (sign r) src hr.andE₁.andE₁ same.eqSymm

theorem observation (f : PR 2) (t x M R S : PTm n) (h : Γ ⊢[PRAAx] source f x M R)
    (hS : Γ ⊢[PRAAx] le (radius (shiftF f) (shiftData x)) S) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (nameF f) t (data x M R S)) (ap2 (logF f) t (logData x M R)) (num 5) (unit t) := by
  let g := shiftF f
  let y := shiftData x
  let p := (clockΓ t M R+clockΓ t M S)+clockLog t M R
  let k := shiftClock p
  let q := ap2 f k x
  let r := ap2 g p y
  let A := realNumerator q
  let B := imagNumerator q
  let D := denominator q
  let s := sign q
  let a := canonicalData (A+D) B D s
  let b := dat q
  let c := GaussianRightHalfPlaneLogarithmNamed.pointData q
  let U := unit t
  have hU : Γ ⊢[PRAAx] le one U := unit_positive t
  have h₁ : Γ ⊢[PRAAx] le (clockΓ t M R) k :=
    le_trans (le_trans (le_add_right _ _) (le_add_right _ _ : Γ ⊢[PRAAx] le (clockΓ t M R+clockΓ t M S) p)) (clock_later p)
  have h₂ : Γ ⊢[PRAAx] le (clockΓ t M S) p := le_trans (le_add_left _ _) (le_add_right _ _)
  have h₃ : Γ ⊢[PRAAx] le (clockLog t M R) k := le_trans (le_add_left _ _) (clock_later p)
  have hh := late_samples f x M R S p h hS (le_trans (GaussianNamedRightHalfPlaneLift.clock_margin rationalMap t M S) h₂)
  have hq : Γ ⊢[PRAAx] certificate q R (two*M) := hh.andE₁
  have hr : Γ ⊢[PRAAx] certificate r S (two*M) := hh.andE₂.andE₁
  have hg := shift_source f x M R S h hS
  have shifted := shifted_gamma_chart q r R S (two*M) hq hr hh.andE₂.andE₂
  have base := freeze_chart f t k x M R b h h₁ (cross_refl C b (rational_regular _ _ _ hq))
  have next := freeze_chart g t p y M S a hg h₂ shifted
  have hA : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source (A+D) D s :=
    .andI (.andI (le_trans hq.andE₁.andE₁.andE₁.andE₁ (le_add_right _ _)) hq.andE₁.andE₁.andE₁.andE₂) hq.andE₁.andE₁.andE₂
  have hf := GaussianLogGammaEulerNamed.name_regular f x M R h
  have hs := GaussianLogGammaEulerNamed.name_regular g y M S hg
  have left := GaussianNamedDifferenceRate.original_rate (gammaF g) (gammaF f) C C
    (gammaData y M S) (gammaData x M R) a b one U one U
    (.andI (.andI hU hU) (.andI (.andI hs hf) (.andI (.andI (canonical_regular _ _ _ _ hA) (rational_regular _ _ _ hq))
      (.andI next base))))
  have diff := GaussianNamedRateRadius.weaken (nameF f) (diffF C C) (data x M R S) (diffData a b)
    _ (U*U) two U (positive_product _ _ hU hU) hU
    (by unfold GaussianNamedDifferenceRate.leadingNumerator; ipra_le 0) left
  have rational := GaussianLogGammaEulerRecurrence.recurrence A B D s hq.andE₁.andE₁
  have asLog := GaussianNamedRateTransport.transport (nameF f) (diffF C C) (nameF f) Log
    (data x M R S) (diffData a b) (data x M R S) c two U hU diff
    (cross_refl _ _ (GaussianNamedDifference.name_regular (gammaF g) (gammaF f) (gammaData y M S) (gammaData x M R) hs hf))
    (cross_symm _ _ _ _ rational)
  have log := GaussianNamedRateComposition.symmetric (logF f) Log (logData x M R) c one U hU
    (GaussianRightHalfPlaneLogarithmNamed.late_rational_rate f t k x M R h h₃)
  have composed := GaussianNamedRateComposition.same_denominator _ _ _ _ _ _ two U one hU asLog log
  exact distance_radius_mono _ _ _ _ (num 5) U (positive_product _ _ hU hU) hU
    (by ipra_le 0) (diagonal_rate _ _ _ _ (two+one) U t hU composed)

theorem recurrence (f : PR 2) (x M R S : PTm n) (h : Γ ⊢[PRAAx] source f x M R)
    (hS : Γ ⊢[PRAAx] le (radius (shiftF f) (shiftData x)) S) : Γ ⊢[PRAAx]
    crossEquivalent (nameF f) (logF f) (data x M R S) (logData x M R) := by
  have base := GaussianLogGammaEulerNamed.name_regular f x M R h
  have next := GaussianLogGammaEulerNamed.name_regular (shiftF f) (shiftData x) M S (shift_source f x M R S h hS)
  have diff := GaussianNamedDifference.name_regular _ _ _ _ next base
  refine equivalent_of_envelope _ _ _ _ (num 5) diff (GaussianRightHalfPlaneLogarithmNamed.name_regular f x M R h) (.allI ?_)
  let Δ := Γ.map Fm.shift
  let s (v : PTm n) := Syn.shift v
  have hs : Δ ⊢[PRAAx] source f (s x) (s M) (s R) := by simpa [Δ,s,Fm.shift,Syn.shift] using h.shift
  have hsS : Δ ⊢[PRAAx] le (radius (shiftF f) (shiftData (s x))) (s S) := by
    simpa [Δ,s,Fm.shift,Syn.shift,radius] using hS.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift,s,Δ,subst_data,
    GaussianNamedRightHalfPlaneLift.subst_data,PTm.subst_num] using observation f (var 0) (s x) (s M) (s R) (s S) hs hsS

theorem actual_named_canonical_log_Gamma_unit_recurrence_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (source f (var 0) (var 1) (var 2) ⟶ le (radius (shiftF f) (shiftData (var 0))) (var 3) ⟶
        crossEquivalent (nameF f) (logF f) (data (var 0) (var 1) (var 2) (var 3))
          (logData (var 0) (var 1) (var 2))) :=
  closeUniv 4 (.impI (.impI (recurrence f _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_named_log_Gamma_unit_recurrence_computed_disks_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (GaussianNamedRightHalfPlane.source f (var 0) (var 1) ⟶
        crossEquivalent (nameF f) (logF f)
          (data (var 0) (var 1) (radius f (var 0)) (radius (shiftF f) (shiftData (var 0))))
          (logData (var 0) (var 1) (radius f (var 0)))) :=
  closeUniv 2 (.impI (recurrence f _ _ _ _ (.andI Prf.hyp0 (le_refl _)) (le_refl _)))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerNamedRecurrence
