import IPRADerivations.Analysis.Barnes.Taylor.RelativeExpansions.GaussianBarnesCanonicalSecondDerivativeCofinal
import IPRADerivations.Analysis.Barnes.Taylor.RelativeExpansions.GaussianBarnesCanonicalSecondDerivativeInterval
import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.GaussianBarnesCanonicalDerivativeCofinal
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedBoundedProductObservation
import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.GaussianNamedDifferenceQuotient
import IPRADerivations.Analysis.Euler.PowerScaling.GaussianEulerNamedPowerScalingPowerFrozen
import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.GaussianNativeDerivativeQuotientRate

/-!
# Differentiate the original cofinal Barnes first-derivative name

At a common late finite prefix, the checked exact sum comparison
has a uniform quadratic remainder. The two original cofinal names
and the actual normalized difference and product contribute only
explicit observation errors, which the independent rate removes.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalSecondDerivativeBinding

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (add normSq)
open GaussianBarnesCanonicalLogCofinal (data source)
open GaussianBarnesCanonicalLogCofinalRate (initial_source)
open GaussianBarnesCanonicalLogSchedule (initial initial_positive)
open GaussianBarnesCanonicalSecondDerivativeStep (errorNumerator)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedLipschitzRate (diagonalEnvelope diagonalNumerator diagonalDenominator)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (ofGaussian ofGaussian_represents qmul positive_product)
open GaussianRationalMetric (bounded bounded_of_cleared distanceBounded qsub)
open GaussianRationalSyntheticDivision (qmul_congr)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "F" => GaussianBarnesCanonicalDerivativeCofinal.nameF
local notation "S" => GaussianBarnesCanonicalSecondDerivativeCofinal.nameF
local notation "fLength" => GaussianBarnesCanonicalDerivativeCofinal.length
local notation "sLength" => GaussianBarnesCanonicalSecondDerivativeCofinal.length
local notation "rawF" => GaussianBarnesCanonicalDerivativeTail.value
local notation "rawS" => GaussianBarnesCanonicalSecondDerivativeTail.value
local notation "secondCap" => GaussianBarnesCanonicalSecondDerivativeRow.boundNumerator

def input (z h R B H : PTm n) : Fm PTm n :=
  source z R B ⋏ (source (add z h) R B ⋏ ComplexLogarithmRemainder.bounded h H)
def incrementF : PR 2 := GaussianNamedDifference.nameF F F
def incrementData (z h R B : PTm n) : PTm n := GaussianNamedDifference.data (data (add z h) R B) (data z R B)
def linearF : PR 2 := multiplyF constantF S
def linearData (z h R B : PTm n) : PTm n := multiplyData constantF S (ofGaussian h B) (data z R B)
def denominator (R B : PTm n) : PTm n := GaussianBarnesCanonicalSecondDerivativeInterval.errorDenominator B (initial R)
def observationCost (R H : PTm n) : PTm n := num 8+(two*(H+secondCap R)+H)

@[simp] theorem subst_input {m : ℕ} (σ : Fin n → PTm m) (z h R B H : PTm n) :
    (input z h R B H).subst σ =
      input (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ H) := by simp [input]

@[simp] theorem subst_incrementData {m : ℕ} (σ : Fin n → PTm m) (z h R B : PTm n) :
    Syn.subst σ (incrementData z h R B) = incrementData (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R) (Syn.subst σ B) :=
  by simp [incrementData]

@[simp] theorem subst_linearData {m : ℕ} (σ : Fin n → PTm m) (z h R B : PTm n) :
    Syn.subst σ (linearData z h R B) = linearData (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R) (Syn.subst σ B) :=
  by simp [linearData]

@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (R B : PTm n) :
    Syn.subst σ (denominator R B) = denominator (Syn.subst σ R) (Syn.subst σ B) := by simp [denominator]

@[simp] theorem subst_observationCost {m : ℕ} (σ : Fin n → PTm m) (R H : PTm n) :
    Syn.subst σ (observationCost R H) = observationCost (Syn.subst σ R) (Syn.subst σ H) := by simp [observationCost,two]

theorem denominator_positive (R B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] le one (denominator R B) :=
  positive_product _ _ (positive_product _ _ hB hB) (initial_positive R)

private theorem step_bound (h B H : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hh : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded h H) : Γ ⊢[PRAAx] bounded (ofGaussian h B) H one := by
  have raw : Γ ⊢[PRAAx] bounded (ofGaussian h B) H B :=
    bounded_of_cleared _ _ _ _ _ hB hB (ofGaussian_represents h B hB)
      (le_congr (mul_comm _ _) (.eqRefl _) (mul_le_mul_right (B*B) hh))
  have fit : Γ ⊢[PRAAx] le (H*one) (H*B) :=
    le_congr (mul_comm one H) (mul_comm B H) (mul_le_mul_right H hB)
  exact bounded_radius_mono _ _ _ _ _ hB (le_refl one) fit raw

private theorem first_late (p z R B r : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hr : Γ ⊢[PRAAx] le (fLength p R) r) : Γ ⊢[PRAAx]
    distanceBounded (ap2 F p (data z R B)) (rawF z B (initial R) r) one (unit p) :=
  distance_symmetric _ _ _ _ (unit_positive p)
    (distance_congr (.eqRefl _) (GaussianBarnesCanonicalDerivativeCofinal.sample_at p z R B).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianBarnesCanonicalDerivativeCofinal.late_prefix_error p z R B r hz hr))

private theorem second_late (p z R B r : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hr : Γ ⊢[PRAAx] le (sLength p R) r) : Γ ⊢[PRAAx]
    distanceBounded (ap2 S p (data z R B)) (rawS z B (initial R) r) one (unit p) :=
  distance_symmetric _ _ _ _ (unit_positive p)
    (distance_congr (.eqRefl _) (GaussianBarnesCanonicalSecondDerivativeCofinal.sample_at p z R B).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianBarnesCanonicalSecondDerivativeCofinal.late_prefix_error p z R B r hz hr))

private theorem difference_observation (p z h R B r : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source (add z h) R B) (hr : Γ ⊢[PRAAx] le (fLength p R) r) :
    Γ ⊢[PRAAx] distanceBounded (ap2 incrementF p (incrementData z h R B))
      (GaussianBarnesCanonicalSecondDerivativeInterval.increment z h B (initial R) r) (num 8) (unit p) := by
  let w := add z h
  let y := data z R B
  let x := data w R B
  have raw := GaussianNamedDifference.sample_error F F x y p
    (GaussianBarnesCanonicalDerivativeCofinal.regular w R B hw) (GaussianBarnesCanonicalDerivativeCofinal.regular z R B hz)
  have finite := GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ (unit_positive p)
    (first_late p w R B r hw hr) (first_late p z R B r hz hr)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) raw finite)

private theorem linear_observation (p z h R B r H : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hh : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded h H) (hr : Γ ⊢[PRAAx] le (sLength p R) r) :
    Γ ⊢[PRAAx] distanceBounded (ap2 linearF p (linearData z h R B))
      (GaussianBarnesCanonicalSecondDerivativeInterval.linear z h B (initial R) r) (two*(H+secondCap R)+H) (unit p) := by
  let a := ofGaussian h B
  let x := data z R B
  have ha := step_bound h B H hz.andE₁ hh
  have raw := GaussianNamedBoundedProductObservation.sample_error constantF S p a x H (secondCap R)
    (constant_regular a) (GaussianBarnesCanonicalSecondDerivativeCofinal.regular z R B hz)
    (GaussianEulerNamedPowerScalingPowerFrozen.constant_bound a H ha)
    (GaussianBarnesCanonicalSecondDerivativeCofinal.samples_bound z R B hz)
  have left := distance_congr (.eqRefl _) (qmul_congr (constant_at p a) (.eqRefl _)) (.eqRefl _) (.eqRefl _) raw
  have right := GaussianNamedDifferenceQuotient.scale_distance a _ _ H one (unit p) (unit_positive p) ha
    (second_late p z R B r hz hr)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) left right)

private theorem bridge (a b c d A D L M U : PTm n) (hD : Γ ⊢[PRAAx] le one D) (hU : Γ ⊢[PRAAx] le one U)
    (h₁ : Γ ⊢[PRAAx] distanceBounded a b L U) (h₂ : Γ ⊢[PRAAx] distanceBounded b c A D)
    (h₃ : Γ ⊢[PRAAx] distanceBounded d c M U) : Γ ⊢[PRAAx]
    distanceBounded a d (A*U+(L+M)*D) (D*U) := by
  let V := D*U
  have hV := positive_product _ _ hD hU
  have left := distance_radius_mono a b L U (L*D) V hU hV (le_of_eq_add (d := zero) (by dsimp only [V]; ipra_ring)) h₁
  have middle := distance_radius_mono b c A D (A*U) V hD hV (le_of_eq_add (d := zero) (by dsimp only [V]; ipra_ring)) h₂
  have right := distance_radius_mono c d M U (M*D) V hU hV (le_of_eq_add (d := zero) (by dsimp only [V]; ipra_ring))
    (distance_symmetric _ _ _ _ hU h₃)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hV (distance_triangle_same _ _ _ _ _ _ hV left middle) right)

theorem observation (p z h R B H : PTm n) (hs : Γ ⊢[PRAAx] input z h R B H) : Γ ⊢[PRAAx]
    distanceBounded (ap2 incrementF p (incrementData z h R B)) (ap2 linearF p (linearData z h R B))
      (diagonalNumerator (errorNumerator H) (denominator R B) (observationCost R H) p)
      (diagonalDenominator (denominator R B) p) := by
  let N := initial R
  let r := fLength p R+sLength p R
  have hz := hs.andE₁
  have hw := hs.andE₂.andE₁
  have hh := hs.andE₂.andE₂
  have source : Γ ⊢[PRAAx] GaussianBarnesCanonicalSecondDerivativeInterval.source z h R B N H :=
    .andI (initial_source z R B hz) (.andI (initial_source (add z h) R B hw) hh)
  have first := difference_observation p z h R B r hz hw (le_add_right _ _)
  have middle := GaussianBarnesCanonicalSecondDerivativeInterval.quadratic_bound z h R B N H r source
  have last := linear_observation p z h R B r H hz hh (le_add_left _ _)
  exact bridge _ _ _ _ (errorNumerator H) (denominator R B) (num 8) (two*(H+secondCap R)+H) (unit p)
    (denominator_positive R B hz.andE₁) (unit_positive p) first middle last

theorem rate (z h R B H : PTm n) (hs : Γ ⊢[PRAAx] input z h R B H) :
    Γ ⊢[PRAAx] independentRate incrementF linearF (incrementData z h R B) (linearData z h R B)
      (errorNumerator H) (denominator R B) := by
  have hz := hs.andE₁
  have hw := hs.andE₂.andE₁
  have x : Γ ⊢[PRAAx] pointCN incrementF (incrementData z h R B) :=
    GaussianNamedDifference.name_regular F F (data (add z h) R B) (data z R B)
      (GaussianBarnesCanonicalDerivativeCofinal.regular _ _ _ hw) (GaussianBarnesCanonicalDerivativeCofinal.regular _ _ _ hz)
  have y : Γ ⊢[PRAAx] pointCN linearF (linearData z h R B) :=
    multiply_fast constantF S (ofGaussian h B) (data z R B) (constant_regular (ofGaussian h B))
      (GaussianBarnesCanonicalSecondDerivativeCofinal.regular _ _ _ hz)
  have env : Γ ⊢[PRAAx] diagonalEnvelope incrementF linearF (incrementData z h R B) (linearData z h R B)
      (errorNumerator H) (denominator R B) (observationCost R H) := by
    refine .allI ?_
    let sh (v : PTm n) := Syn.shift v
    have hh : Γ.map Fm.shift ⊢[PRAAx] input (sh z) (sh h) (sh R) (sh B) (sh H) := by
      simpa [Fm.shift,Syn.shift,sh] using hs.shift
    simpa only [diagonalEnvelope,Syn.shift,sh,subst_incrementData,subst_linearData,
      GaussianNamedLipschitzRate.subst_diagonalNumerator,GaussianNamedLipschitzRate.subst_diagonalDenominator,
      GaussianBarnesCanonicalSecondDerivativeStep.subst_errorNumerator,subst_denominator,subst_observationCost] using
      observation (var 0) (sh z) (sh h) (sh R) (sh B) (sh H) hh
  exact GaussianNamedLipschitzRate.independent_rate incrementF linearF (incrementData z h R B) (linearData z h R B)
    (errorNumerator H) (denominator R B) (observationCost R H) (denominator_positive R B hz.andE₁) x y env

private theorem quotient_budget (B N H : PTm n) : Γ ⊢[PRAAx]
    le (((two*B)*errorNumerator H)*(B*N)) ((num 16*H)*(H*((B*B)*N))) :=
  le_of_eq_add (d := zero) (by unfold errorNumerator; ipra_ring)

theorem quotient_rate (z h R B : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (hw : Γ ⊢[PRAAx] source (add z h) R B)
    (hh : Γ ⊢[PRAAx] le one (normSq h)) :
    Γ ⊢[PRAAx] independentRate (GaussianNamedDifferenceQuotient.nameF F F) S
      (GaussianNamedDifferenceQuotient.data F F (data (add z h) R B) (data z R B) h B) (data z R B)
      (num 16*GaussianL1.norm1 h) (B*initial R) := by
  let H := GaussianL1.norm1 h
  let N := initial R
  let x := data (add z h) R B
  let y := data z R B
  let J := GaussianNamedDifferenceQuotient.nameF F F
  let j := GaussianNamedDifferenceQuotient.data F F x y h B
  have hn : Γ ⊢[PRAAx] le one H := GaussianNativeDerivativeQuotientRate.norm1_positive h hh
  have hD := denominator_positive R B hz.andE₁
  have hr : Γ ⊢[PRAAx] independentRate J S j y ((two*B)*errorNumerator H) (H*denominator R B) :=
    GaussianNativeDerivativeQuotientRate.rate F F S x y y h B (errorNumerator H) (denominator R B)
      (GaussianBarnesCanonicalDerivativeCofinal.regular _ _ _ hw) (GaussianBarnesCanonicalDerivativeCofinal.regular _ _ _ hz)
      (GaussianBarnesCanonicalSecondDerivativeCofinal.regular _ _ _ hz) (.andI hz.andE₁ hh) hD
      (rate z h R B H (.andI hz (.andI hw (GaussianL1.normSq_le_norm1_square h))))
  exact GaussianNamedRateRadius.weaken J S j y _ _ (num 16*H) (B*N)
    (positive_product _ _ hn hD) (positive_product _ _ hz.andE₁ (initial_positive R)) (quotient_budget B N H) hr

theorem actual_Barnes_cofinal_first_derivative_second_order_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (let z := var 0
     let h := var 1
     let R := var 2
     let B := var 3
     let H := var 4
     input z h R B H ⟶ independentRate incrementF linearF (incrementData z h R B) (linearData z h R B)
       (errorNumerator H) (denominator R B)) :=
  closeUniv 5 (.impI (rate _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalSecondDerivativeBinding
