import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.SecondDerivative.GaussianBarnesCanonicalPositiveSecondLogarithm
import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.ThirdDerivative.FiniteDerivatives.GaussianBarnesCanonicalThirdDerivativeInterval
import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.ThirdDerivative.Cofinal.GaussianBarnesCanonicalThirdLogarithmCofinal
import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.DerivativeRates.GaussianNativeDerivativeQuotientRate

/-!
# The positive Barnes second-logarithm expression differentiates to the cubic name

At each requested precision a common literal prefix pays for both second
derivative observations and the cubic series. The identical prefactor
coefficient cancels in the increment at the two endpoints. The actual
native divided difference hence has a quantitative third-derivative limit.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalThirdDerivativeCofinalBinding

open_ipra
open LeanProofs.IPRA.Common (pos_of_one_le)
open ComplexLogarithmRemainder (normSq)
open GaussianBarnesCanonicalThirdLogarithmRows (center)
open GaussianBarnesCanonicalThirdDerivativePositiveMargin (step)
open GaussianBarnesCanonicalThirdDerivativeStep (errorNumerator)
open GaussianBarnesCanonicalLogSchedule (initial initial_positive)
open GaussianCoefficientNameBounds (bounded_radius_mono unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constant_at constantF constant_regular)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast multiplyModulus sum_difference)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedLipschitzRate (diagonalNumerator diagonalDenominator diagonalEnvelope)
open GaussianRationalDistanceOrder (distance_congr distance_from_model_comparison distance_symmetric distance_triangle_same)
open GaussianRationalHorner (ofGaussian ofGaussian_represents positive_product qadd qmul)
open GaussianRationalMetric (bounded bounded_of_cleared distanceBounded qsub qsub_canonical)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qsub_congr qzero_add)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "S" => GaussianBarnesCanonicalPositiveSecondLogarithm.nameF
local notation "sd" => GaussianBarnesCanonicalPositiveSecondLogarithm.data
local notation "T" => GaussianBarnesCanonicalThirdLogarithmCofinal.nameF
local notation "td" => GaussianBarnesCanonicalThirdLogarithmCofinal.data
local notation "tv" => GaussianBarnesCanonicalThirdLogarithmSeries.value
local notation "Diff" => GaussianNamedDifference.nameF
local notation "dd" => GaussianNamedDifference.data
local notation "disk" => GaussianBarnesCanonicalLogCofinal.source
local notation "margin" => GaussianBarnesCanonicalThirdDerivativePositiveMargin.source
local notation "I" => GaussianBarnesCanonicalThirdDerivativeInterval.increment
local notation "L" => GaussianBarnesCanonicalThirdDerivativeInterval.linear

def source (A C B R H K : PTm n) : Fm PTm n :=
  margin A C B H K ⋏ (disk (center A B) R B ⋏ disk (center C B) R B)

def incrementF : PR 2 := Diff S S
def incrementData (A C B R : PTm n) : PTm n := dd (sd C B R) (sd A B R)

def linearF : PR 2 := multiplyF constantF T
def linearData (A C B : PTm n) : PTm n := multiplyData constantF T (ofGaussian (step A C) B) (td A B)

def cutoff (p R : PTm n) : PTm n :=
  GaussianBarnesCanonicalSecondDerivativeCofinal.length p R + GaussianBarnesCanonicalThirdLogarithmCofinal.cutoff p

def numerator (H K : PTm n) : PTm n := two*errorNumerator H K

def observationCost (A C B H : PTm n) : PTm n :=
  num 20 + (multiplyModulus constantF T (ofGaussian (step A C) B) (td A B)+one+H)

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (A C B R H K : PTm n) :
    (source A C B R H K).subst σ =
      source (Syn.subst σ A) (Syn.subst σ C) (Syn.subst σ B) (Syn.subst σ R) (Syn.subst σ H) (Syn.subst σ K) :=
  by simp [source]

@[simp] theorem subst_incrementData {m : ℕ} (σ : Fin n → PTm m) (A C B R : PTm n) :
    Syn.subst σ (incrementData A C B R) =
      incrementData (Syn.subst σ A) (Syn.subst σ C) (Syn.subst σ B) (Syn.subst σ R) := by simp [incrementData]

@[simp] theorem subst_linearData {m : ℕ} (σ : Fin n → PTm m) (A C B : PTm n) :
    Syn.subst σ (linearData A C B) = linearData (Syn.subst σ A) (Syn.subst σ C) (Syn.subst σ B) := by simp [linearData]

@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (H K : PTm n) :
    Syn.subst σ (numerator H K) = numerator (Syn.subst σ H) (Syn.subst σ K) := by simp [numerator,two,one]

@[simp] theorem subst_observationCost {m : ℕ} (σ : Fin n → PTm m) (A C B H : PTm n) :
    Syn.subst σ (observationCost A C B H) =
      observationCost (Syn.subst σ A) (Syn.subst σ C) (Syn.subst σ B) (Syn.subst σ H) := by simp [observationCost,one]

theorem cubic_source (A C B H K : PTm n) (h : Γ ⊢[PRAAx] margin A C B H K) :
    Γ ⊢[PRAAx] GaussianBarnesCanonicalThirdLogarithmCofinal.source A B :=
  .andI h.andE₂.andE₁ h.andE₁

theorem step_bound (h B H : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hh : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded h H) :
    Γ ⊢[PRAAx] bounded (ofGaussian h B) H one := by
  have raw : Γ ⊢[PRAAx] bounded (ofGaussian h B) H B :=
    GaussianRationalMetric.bounded_of_same_denominator hB (ofGaussian_represents h B hB) hh
  have fit : Γ ⊢[PRAAx] le (H*one) (H*B) :=
    le_congr (mul_comm one H) (mul_comm B H) (mul_le_mul_right H hB)
  exact bounded_radius_mono _ _ _ _ _ hB (le_refl one) fit raw

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
    (GaussianBarnesCanonicalThirdDerivativeInterval.full_error A C B H K k h)

theorem difference_observation (p A C B R r : PTm n)
    (ha : Γ ⊢[PRAAx] disk (center A B) R B) (hc : Γ ⊢[PRAAx] disk (center C B) R B)
    (hr : Γ ⊢[PRAAx] le (GaussianBarnesCanonicalSecondDerivativeCofinal.length p R) r) :
    Γ ⊢[PRAAx] distanceBounded (ap2 incrementF p (incrementData A C B R))
      (I A C B zero (initial R+r)) (num 20) (unit p) := by
  let a := GaussianBarnesCanonicalPositiveSecondLogarithm.prefixValue A B R r
  let c := GaussianBarnesCanonicalPositiveSecondLogarithm.prefixValue C B R r
  let u := ap2 GaussianBarnesCanonicalPositiveSecondLogarithm.coefficientF p
    (GaussianBarnesCanonicalPositiveSecondLogarithm.coefficientData : PTm n)
  have raw := GaussianNamedDifference.sample_error S S (sd C B R) (sd A B R) p
    (GaussianBarnesCanonicalPositiveSecondLogarithm.regular C B R hc)
    (GaussianBarnesCanonicalPositiveSecondLogarithm.regular A B R ha)
  have near := GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ (unit_positive p)
    (GaussianBarnesCanonicalPositiveSecondLogarithm.prefix_error p C B R r hc hr)
    (GaussianBarnesCanonicalPositiveSecondLogarithm.prefix_error p A B R r ha hr)
  have cancel : Γ ⊢[PRAAx] qsub (qadd u c) (qadd u a) ≐ I A C B zero (initial R+r) :=
    GaussianNameArithmetic.sum_difference_cancel_left u c a
  exact distance_congr (.eqRefl _) cancel (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) raw near)

theorem linear_observation (p A C B R H K r : PTm n) (h : Γ ⊢[PRAAx] margin A C B H K)
    (hr : Γ ⊢[PRAAx] le (GaussianBarnesCanonicalThirdLogarithmCofinal.cutoff p) r) :
    let a := ofGaussian (step A C) B
    Γ ⊢[PRAAx] distanceBounded (ap2 linearF p (linearData A C B))
      (L A C B zero (initial R+r)) (multiplyModulus constantF T a (td A B)+one+H) (unit p) := by
  let a := ofGaussian (step A C) B
  let n := pred (initial R)+r
  have ht := cubic_source A C B H K h
  have last := GaussianBarnesCanonicalThirdLogarithmCofinal.late_prefix_error p A B n ht (le_trans hr (le_add_left r _))
  have idx : Γ ⊢[PRAAx] tv A B (succ n) ≐ tv A B (initial R+r) := by
    ipra_congr (tv (var 0) (var 1) (var 2) : PTm 3) with [.eqRefl _, .eqRefl _, count_readback R r]
  have close := distance_symmetric _ _ _ _ (unit_positive p)
    (distance_congr idx (.eqRefl _) (.eqRefl _) (.eqRefl _) last)
  have raw := GaussianNameRingLaws.multiply_sample_error constantF T a (td A B) p (constant_regular _)
    (GaussianBarnesCanonicalThirdLogarithmCofinal.regular A B ht)
  have first := distance_congr (.eqRefl _) (qmul_congr (constant_at p a) (.eqRefl _)) (.eqRefl _) (.eqRefl _) raw
  have ss := step_bound (step A C) B H h.andE₁ h.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂
  have second := GaussianNamedDifferenceQuotient.scale_distance a _ _ H one (unit p) (unit_positive p) ss close
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) first second)

theorem observation (p A C B R H K : PTm n) (h : Γ ⊢[PRAAx] source A C B R H K) :
    Γ ⊢[PRAAx] distanceBounded (ap2 incrementF p (incrementData A C B R)) (ap2 linearF p (linearData A C B))
      (diagonalNumerator (numerator H K) (B*B) (observationCost A C B H) p) (diagonalDenominator (B*B) p) := by
  let r := cutoff p R
  have first := difference_observation p A C B R r h.andE₂.andE₁ h.andE₂.andE₂ (le_add_right _ _)
  have middle := finite_error A C B R H K r h.andE₁
  have last := linear_observation p A C B R H K r h.andE₁ (le_add_left _ _)
  exact distance_from_model_comparison (numerator H K) (B*B) (unit p) (num 20) _
    (positive_product _ _ h.andE₁.andE₁ h.andE₁.andE₁) (unit_positive p) first middle last

theorem rate (A C B R H K : PTm n) (h : Γ ⊢[PRAAx] source A C B R H K) :
    Γ ⊢[PRAAx] independentRate incrementF linearF (incrementData A C B R) (linearData A C B) (numerator H K) (B*B) := by
  have hB := h.andE₁.andE₁
  have ra := GaussianBarnesCanonicalPositiveSecondLogarithm.regular A B R h.andE₂.andE₁
  have rc := GaussianBarnesCanonicalPositiveSecondLogarithm.regular C B R h.andE₂.andE₂
  have ri : Γ ⊢[PRAAx] pointCN incrementF (incrementData A C B R) := GaussianNamedDifference.name_regular _ _ _ _ rc ra
  have rl : Γ ⊢[PRAAx] pointCN linearF (linearData A C B) := multiply_fast _ _ _ _ (constant_regular _)
    (GaussianBarnesCanonicalThirdLogarithmCofinal.regular A B (cubic_source A C B H K h.andE₁))
  have env : Γ ⊢[PRAAx] diagonalEnvelope incrementF linearF (incrementData A C B R) (linearData A C B)
      (numerator H K) (B*B) (observationCost A C B H) := by
    refine .allI ?_
    let sh (v : PTm n) := Syn.shift v
    have hh : Γ.map Fm.shift ⊢[PRAAx] source (sh A) (sh C) (sh B) (sh R) (sh H) (sh K) := by
      simpa [Fm.shift,Syn.shift,sh] using h.shift
    simpa only [diagonalEnvelope,Syn.shift,sh,subst_incrementData,subst_linearData,
      GaussianNamedLipschitzRate.subst_diagonalNumerator,GaussianNamedLipschitzRate.subst_diagonalDenominator,
      subst_numerator,subst_observationCost,PTm.subst_mul] using
      observation (var 0) (sh A) (sh C) (sh B) (sh R) (sh H) (sh K) hh
  exact GaussianNamedLipschitzRate.independent_rate _ _ _ _ _ _ _ (positive_product _ _ hB hB) ri rl env

def quotientF : PR 2 := GaussianNamedDifferenceQuotient.nameF S S

def quotientData (A C B R : PTm n) : PTm n :=
  GaussianNamedDifferenceQuotient.data S S (sd C B R) (sd A B R) (step A C) B

def quotientNumerator (H K : PTm n) : PTm n := num 12*H*(K*K*K*K)

theorem quotient_rate (A C B R K : PTm n)
    (h : Γ ⊢[PRAAx] source A C B R (GaussianL1.norm1 (step A C)) K)
    (hn : Γ ⊢[PRAAx] le one (normSq (step A C))) :
    Γ ⊢[PRAAx] independentRate quotientF T (quotientData A C B R) (td A B)
      (quotientNumerator (GaussianL1.norm1 (step A C)) K) B := by
  let H := GaussianL1.norm1 (step A C)
  have hB := h.andE₁.andE₁
  have hD := positive_product _ _ hB hB
  have hp := GaussianNativeDerivativeQuotientRate.norm1_positive (step A C) hn
  have raw : Γ ⊢[PRAAx] independentRate quotientF T (quotientData A C B R) (td A B)
      ((two*B)*numerator H K) (H*(B*B)) :=
    GaussianNativeDerivativeQuotientRate.rate S S T (sd C B R) (sd A B R) (td A B) (step A C) B
      (numerator H K) (B*B)
      (GaussianBarnesCanonicalPositiveSecondLogarithm.regular C B R h.andE₂.andE₂)
      (GaussianBarnesCanonicalPositiveSecondLogarithm.regular A B R h.andE₂.andE₁)
      (GaussianBarnesCanonicalThirdLogarithmCofinal.regular A B (cubic_source A C B H K h.andE₁))
      (.andI hB hn) hD (rate A C B R H K h)
  have fit : Γ ⊢[PRAAx] le (((two*B)*numerator H K)*B) ((quotientNumerator H K)*(H*(B*B))) :=
    le_of_eq_add (d := zero) (by dsimp only [numerator,errorNumerator,quotientNumerator]; ipra_ring)
  exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ (positive_product _ _ hp hD) hB fit raw

theorem actual_Barnes_positive_second_logarithm_third_derivative_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (let A := var 0
       let C := var 1
       let B := var 2
       let R := var 3
       let K := var 4
       let H := GaussianL1.norm1 (step A C)
       (source A C B R H K ⋏ le one (normSq (step A C))) ⟶
         independentRate quotientF T (quotientData A C B R) (td A B) (quotientNumerator H K) B) :=
  closeUniv 5 (.impI (quotient_rate _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalThirdDerivativeCofinalBinding
