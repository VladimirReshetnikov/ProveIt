import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.FirstDerivative.Cofinal.GaussianBarnesCanonicalPositiveFirstLogarithm
import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.SecondDerivative.GaussianBarnesCanonicalPositiveSecondLogarithm
import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.SecondDerivative.GaussianBarnesCanonicalPositiveSecondDerivativeInterval
import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.ThirdDerivative.Cofinal.GaussianBarnesCanonicalThirdDerivativeCofinalBinding

/-!
# The first to second derivative rate for the positive Barnes log series

At each comparison clock a common literal prefix reads both original
first derivative observations and the original second derivative model.
The positive row margin gives the independent-clock rate for these series.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPositiveSecondDerivativeSeriesBinding

open_ipra
open LeanProofs.IPRA.Common (pos_of_one_le)
open GaussianBarnesCanonicalThirdLogarithmRows (center)
open GaussianBarnesCanonicalThirdDerivativePositiveMargin (step)
open GaussianBarnesCanonicalPositiveFirstDerivativeRow (gain)
open GaussianBarnesCanonicalThirdDerivativeCofinalBinding (source subst_source step_bound)
open GaussianBarnesCanonicalLogSchedule (initial initial_positive)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constant_at constantF constant_regular)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast multiplyModulus)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedLipschitzRate (diagonalNumerator diagonalDenominator diagonalEnvelope)
open GaussianRationalDistanceOrder (distance_congr distance_from_model_comparison distance_triangle_same)
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalSyntheticDivision (qmul_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "S" => GaussianBarnesCanonicalPositiveFirstLogarithm.seriesF
local notation "sd" => GaussianBarnesCanonicalPositiveFirstLogarithm.seriesData
local notation "T" => GaussianBarnesCanonicalPositiveSecondLogarithm.seriesF
local notation "td" => GaussianBarnesCanonicalPositiveSecondLogarithm.seriesData
local notation "Diff" => GaussianNamedDifference.nameF
local notation "dd" => GaussianNamedDifference.data
local notation "disk" => GaussianBarnesCanonicalLogCofinal.source
local notation "margin" => GaussianBarnesCanonicalThirdDerivativePositiveMargin.source
local notation "I" => GaussianBarnesCanonicalPositiveSecondDerivativeInterval.increment
local notation "L" => GaussianBarnesCanonicalPositiveSecondDerivativeInterval.linear

def incrementF : PR 2 := Diff S S
def incrementData (A C B R : PTm n) : PTm n := dd (sd C B R) (sd A B R)

def linearF : PR 2 := multiplyF constantF T
def linearData (A C B R : PTm n) : PTm n := multiplyData constantF T (ofGaussian (step A C) B) (td A B R)

def cutoff (p R : PTm n) : PTm n :=
  GaussianBarnesCanonicalDerivativeCofinal.length p R + GaussianBarnesCanonicalSecondDerivativeCofinal.length p R

def numerator (H K : PTm n) : PTm n := two*gain H K

def observationCost (A C B R H : PTm n) : PTm n :=
  num 14 + (multiplyModulus constantF T (ofGaussian (step A C) B) (td A B R)+one+H*num 4)

@[simp] theorem subst_incrementData {m : ℕ} (σ : Fin n → PTm m) (A C B R : PTm n) :
    Syn.subst σ (incrementData A C B R) =
      incrementData (Syn.subst σ A) (Syn.subst σ C) (Syn.subst σ B) (Syn.subst σ R) := by simp [incrementData]

@[simp] theorem subst_linearData {m : ℕ} (σ : Fin n → PTm m) (A C B R : PTm n) :
    Syn.subst σ (linearData A C B R) = linearData (Syn.subst σ A) (Syn.subst σ C) (Syn.subst σ B) (Syn.subst σ R) := by simp [linearData]

@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (H K : PTm n) :
    Syn.subst σ (numerator H K) = numerator (Syn.subst σ H) (Syn.subst σ K) := by simp [numerator,two,one]

@[simp] theorem subst_observationCost {m : ℕ} (σ : Fin n → PTm m) (A C B R H : PTm n) :
    Syn.subst σ (observationCost A C B R H) =
      observationCost (Syn.subst σ A) (Syn.subst σ C) (Syn.subst σ B) (Syn.subst σ R) (Syn.subst σ H) := by simp [observationCost,one]

private theorem count_readback (R r : PTm n) :
    Γ ⊢[PRAAx] succ (pred (initial R)+r) ≐ initial R+r :=
  (by ipra_ring : Γ ⊢[PRAAx] succ (pred (initial R)+r) ≐ succ (pred (initial R))+r).eqTrans
    (congrAdd (pos_of_one_le (initial_positive R)).eqSymm (.eqRefl _))

theorem finite_error (A C B R H K r : PTm n) (h : Γ ⊢[PRAAx] margin A C B H K) :
    Γ ⊢[PRAAx] distanceBounded (I A C B zero (initial R+r)) (L A C B zero (initial R+r))
      (numerator H K) (B*B) := by
  let k := pred (initial R)+r
  have idx : Γ ⊢[PRAAx] succ k ≐ initial R+r := count_readback R r
  have ei : Γ ⊢[PRAAx] I A C B zero (succ k) ≐ I A C B zero (initial R+r) := by
    ipra_congr (I (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
      with [.eqRefl _, .eqRefl _, .eqRefl _, .eqRefl _, idx]
  have el : Γ ⊢[PRAAx] L A C B zero (succ k) ≐ L A C B zero (initial R+r) := by
    ipra_congr (L (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
      with [.eqRefl _, .eqRefl _, .eqRefl _, .eqRefl _, idx]
  exact distance_congr ei el (.eqRefl _) (.eqRefl _)
    (GaussianBarnesCanonicalPositiveSecondDerivativeInterval.full_error A C B H K k h)

theorem difference_observation (p A C B R r : PTm n)
    (ha : Γ ⊢[PRAAx] disk (center A B) R B) (hc : Γ ⊢[PRAAx] disk (center C B) R B)
    (hr : Γ ⊢[PRAAx] le (GaussianBarnesCanonicalDerivativeCofinal.length p R) r) :
    Γ ⊢[PRAAx] distanceBounded (ap2 incrementF p (incrementData A C B R))
      (I A C B zero (initial R+r)) (num 14) (unit p) := by
  have raw := GaussianNamedDifference.sample_error S S (sd C B R) (sd A B R) p
    (GaussianBarnesCanonicalPositiveFirstLogarithm.series_regular C B R hc)
    (GaussianBarnesCanonicalPositiveFirstLogarithm.series_regular A B R ha)
  have near := GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ (unit_positive p)
    (GaussianBarnesCanonicalPositiveFirstLogarithm.series_prefix_error p C B R r hc hr)
    (GaussianBarnesCanonicalPositiveFirstLogarithm.series_prefix_error p A B R r ha hr)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) raw near)

theorem linear_observation (p A C B R H K r : PTm n) (h : Γ ⊢[PRAAx] margin A C B H K)
    (hd : Γ ⊢[PRAAx] disk (center A B) R B)
    (hr : Γ ⊢[PRAAx] le (GaussianBarnesCanonicalSecondDerivativeCofinal.length p R) r) :
    let a := ofGaussian (step A C) B
    Γ ⊢[PRAAx] distanceBounded (ap2 linearF p (linearData A C B R))
      (L A C B zero (initial R+r)) (multiplyModulus constantF T a (td A B R)+one+H*num 4) (unit p) := by
  let a := ofGaussian (step A C) B
  have close := GaussianBarnesCanonicalPositiveSecondLogarithm.series_prefix_error p A B R r hd hr
  have raw := GaussianNameRingLaws.multiply_sample_error constantF T a (td A B R) p (constant_regular _)
    (GaussianBarnesCanonicalPositiveSecondLogarithm.series_regular A B R hd)
  have first := distance_congr (.eqRefl _) (qmul_congr (constant_at p a) (.eqRefl _)) (.eqRefl _) (.eqRefl _) raw
  have ss := step_bound (step A C) B H h.andE₁ h.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂
  have second := GaussianNamedDifferenceQuotient.scale_distance a _ _ H (num 4) (unit p) (unit_positive p) ss close
  exact distance_triangle_same _ _ _ _ _ _ (unit_positive p) first second

theorem observation (p A C B R H K : PTm n) (h : Γ ⊢[PRAAx] source A C B R H K) :
    Γ ⊢[PRAAx] distanceBounded (ap2 incrementF p (incrementData A C B R)) (ap2 linearF p (linearData A C B R))
      (diagonalNumerator (numerator H K) (B*B) (observationCost A C B R H) p) (diagonalDenominator (B*B) p) := by
  let r := cutoff p R
  have first := difference_observation p A C B R r h.andE₂.andE₁ h.andE₂.andE₂ (le_add_right _ _)
  have middle := finite_error A C B R H K r h.andE₁
  have last := linear_observation p A C B R H K r h.andE₁ h.andE₂.andE₁ (le_add_left _ _)
  exact distance_from_model_comparison (numerator H K) (B*B) (unit p) (num 14) _
    (positive_product _ _ h.andE₁.andE₁ h.andE₁.andE₁) (unit_positive p) first middle last

theorem rate (A C B R H K : PTm n) (h : Γ ⊢[PRAAx] source A C B R H K) :
    Γ ⊢[PRAAx] independentRate incrementF linearF (incrementData A C B R) (linearData A C B R) (numerator H K) (B*B) := by
  have hB := h.andE₁.andE₁
  have ra := GaussianBarnesCanonicalPositiveFirstLogarithm.series_regular A B R h.andE₂.andE₁
  have rc := GaussianBarnesCanonicalPositiveFirstLogarithm.series_regular C B R h.andE₂.andE₂
  have ri : Γ ⊢[PRAAx] pointCN incrementF (incrementData A C B R) := GaussianNamedDifference.name_regular _ _ _ _ rc ra
  have rl : Γ ⊢[PRAAx] pointCN linearF (linearData A C B R) := multiply_fast _ _ _ _ (constant_regular _)
    (GaussianBarnesCanonicalPositiveSecondLogarithm.series_regular A B R h.andE₂.andE₁)
  have env : Γ ⊢[PRAAx] diagonalEnvelope incrementF linearF (incrementData A C B R) (linearData A C B R)
      (numerator H K) (B*B) (observationCost A C B R H) := by
    refine .allI ?_
    let sh (v : PTm n) := Syn.shift v
    have hh : Γ.map Fm.shift ⊢[PRAAx] source (sh A) (sh C) (sh B) (sh R) (sh H) (sh K) := by
      simpa [Fm.shift,Syn.shift,sh] using h.shift
    simpa only [diagonalEnvelope,Syn.shift,sh,subst_incrementData,subst_linearData,
      GaussianNamedLipschitzRate.subst_diagonalNumerator,GaussianNamedLipschitzRate.subst_diagonalDenominator,
      subst_numerator,subst_observationCost,PTm.subst_mul] using
      observation (var 0) (sh A) (sh C) (sh B) (sh R) (sh H) (sh K) hh
  exact GaussianNamedLipschitzRate.independent_rate _ _ _ _ _ _ _ (positive_product _ _ hB hB) ri rl env

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPositiveSecondDerivativeSeriesBinding
