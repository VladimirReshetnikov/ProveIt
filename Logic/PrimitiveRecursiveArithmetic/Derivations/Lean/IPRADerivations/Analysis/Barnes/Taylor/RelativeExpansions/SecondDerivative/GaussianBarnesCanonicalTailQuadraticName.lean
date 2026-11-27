/-
Second-order rate for the original cofinal Barnes logarithm against fixed
original first- and second-derivative coefficient names. The finite
cutoff is used only in proving the rate.
-/
import IPRADerivations.Analysis.Barnes.Taylor.RelativeExpansions.CorrectedMercator.GaussianBarnesCanonicalCorrectedMercatorCofinal
import IPRADerivations.Analysis.Barnes.Taylor.RelativeExpansions.CorrectedMercator.GaussianBarnesCanonicalCorrectedMercatorPrefix
import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.Cofinal.GaussianBarnesCanonicalDerivativeCofinal
import IPRADerivations.Analysis.Barnes.Taylor.RelativeExpansions.SecondDerivative.GaussianBarnesCanonicalSecondDerivativeCofinal
import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.FiniteFactors.GaussianBarnesCanonicalHeadPolynomialDerivative
import IPRADerivations.Analysis.Names.FiniteOperations.Products.Bounds.GaussianBoundedConstantProductName
import IPRADerivations.Analysis.Names.Rates.Moduli.GaussianNamedLipschitzRate

set_option autoImplicit false
set_option maxHeartbeats 550000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTailQuadraticName

open_ipra
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial initial_positive)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianDominantPairAlgebra (radiusPoint radius_bounded)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianNameArithmetic (addF addData add_fast sum_distance)
open GaussianNamedInverseRate (independentRate diagonal_rate)
open GaussianNamedLipschitzRate (diagonalEnvelope diagonalNumerator diagonalDenominator)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (qadd qmul ofGaussian positive_product qadd_canonical qmul_canonical)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (power bound_congr bounded_product)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qzero_add)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "D" => GaussianBarnesCanonicalDerivativeCofinal.nameF
local notation "S" => GaussianBarnesCanonicalSecondDerivativeCofinal.nameF
local notation "G" => GaussianBarnesCanonicalCorrectedMercatorCofinal.nameF
local notation "gd" => GaussianBarnesCanonicalCorrectedMercatorCofinal.data
local notation "coeffData" => GaussianBarnesCanonicalLogCofinal.data
local notation "P" => GaussianBoundedConstantProductName.nameF
local notation "pd" => GaussianBoundedConstantProductName.data
local notation "v1" => GaussianBarnesCanonicalDerivativeTail.value
local notation "v2" => GaussianBarnesCanonicalSecondDerivativeTail.value
local notation "l1" => GaussianBarnesCanonicalDerivativeCofinal.length
local notation "l2" => GaussianBarnesCanonicalSecondDerivativeCofinal.length
local notation "V" => GaussianBarnesCanonicalCorrectedMercatorInterval.value

def secondWeight (h B : PTm n) : PTm n := qmul (radiusPoint one two) (power (ofGaussian h B) two)

def nameF : PR 2 := addF (P D) (P S)
def data (z h R B : PTm n) : PTm n :=
  addData (pd one (ofGaussian h B) (coeffData z R B)) (pd one (secondWeight h B) (coeffData z R B))

def input (z h R B H : PTm n) : Fm PTm n :=
  GaussianBarnesCanonicalCorrectedMercatorCofinal.input two z h R B H ⋏ le H B

def errorNumerator (H : PTm n) : PTm n := GaussianBarnesCanonicalCorrectedMercator.numerator two H
def errorDenominator (R B : PTm n) : PTm n := GaussianBarnesCanonicalCorrectedMercatorCofinal.analyticDenominator two R B

@[simp] theorem subst_input {m : ℕ} (σ : Fin n → PTm m) (z h R B H : PTm n) :
    (input z h R B H).subst σ = input (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ H) := by simp [input,two]

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (z h R B : PTm n) :
    Syn.subst σ (data z h R B) = data (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R) (Syn.subst σ B) := by
  simp [data,secondWeight,one,two]

@[simp] theorem subst_errorNumerator {m : ℕ} (σ : Fin n → PTm m) (H : PTm n) :
    Syn.subst σ (errorNumerator H) = errorNumerator (Syn.subst σ H) := by simp [errorNumerator,two]

@[simp] theorem subst_errorDenominator {m : ℕ} (σ : Fin n → PTm m) (R B : PTm n) :
    Syn.subst σ (errorDenominator R B) = errorDenominator (Syn.subst σ R) (Syn.subst σ B) := by
  simp [errorDenominator,GaussianBarnesCanonicalCorrectedMercatorCofinal.analyticDenominator,
    GaussianBarnesCanonicalCorrectedMercator.scaleDenominator,two]

private theorem weight_bounds (z h R B H : PTm n) (hs : Γ ⊢[PRAAx] input z h R B H) :
    Γ ⊢[PRAAx] bounded (ofGaussian h B) one one ⋏ bounded (secondWeight h B) one one := by
  have hb := hs.andE₁.andE₁.andE₁
  have hw := GaussianBarnesCanonicalHeadPolynomialDerivative.step_bound h B H hb hs.andE₁.andE₂.andE₂.andE₁
  have ha : Γ ⊢[PRAAx] bounded (ofGaussian h B) one one :=
    bounded_radius_mono _ _ _ _ _ hb (le_refl _) (le_congr (by ipra_ring) (by ipra_ring) hs.andE₂) hw
  have r : Γ ⊢[PRAAx] bounded (radiusPoint one two) one one := bounded_radius_mono _ _ _ _ _
    (le_succ_self one) (le_refl one) (Common.mul_le_mul (le_refl one) (le_succ_self one))
    (radius_bounded one two (le_succ_self one))
  have pow : Γ ⊢[PRAAx] bounded (power (ofGaussian h B) two) one one := by
    have v := GaussianRationalReciprocal.bounded_power (ofGaussian h B) one one two (le_refl one) ha
    have e : Γ ⊢[PRAAx] pw one two ≐ one := (Common.pw_two _).eqTrans (one_mul _)
    exact bound_congr (.eqRefl _) e e v
  exact .andI ha (bound_congr (.eqRefl _) (one_mul _) (one_mul _)
    (bounded_product _ _ _ _ _ _ (le_refl one) (le_refl one) r pow))

theorem regular (z h R B H : PTm n) (hs : Γ ⊢[PRAAx] input z h R B H) :
    Γ ⊢[PRAAx] pointCN nameF (data z h R B) := by
  have hz := hs.andE₁.andE₁
  have b := weight_bounds z h R B H hs
  exact add_fast _ _ _ _
    (GaussianBoundedConstantProductName.name_regular _ _ _ _ (.andI (GaussianBarnesCanonicalDerivativeCofinal.regular z R B hz) b.andE₁))
    (GaussianBoundedConstantProductName.name_regular _ _ _ _ (.andI (GaussianBarnesCanonicalSecondDerivativeCofinal.regular z R B hz) b.andE₂))

def finite (z h B N r : PTm n) : PTm n :=
  qadd (qmul (ofGaussian h B) (v1 z B N r)) (qmul (secondWeight h B) (v2 z B N r))

theorem finite_binding (z h R B H r : PTm n) (hs : Γ ⊢[PRAAx] input z h R B H) :
    Γ ⊢[PRAAx] V two z h B (initial R) r ≐ finite z h B (initial R) r := by
  let N := initial R
  let a := ofGaussian h B
  let c : PTm n := radiusPoint one two
  let b := v2 z B N r
  let s := power a two
  let x := qmul a (v1 z B N r)
  let y := qmul (qmul c b) s
  let T := GaussianBarnesCanonicalHigherMercatorTranspose.polynomial z h B N r zero
  have exactPrefix := GaussianBarnesCanonicalCorrectedMercatorPrefix.coefficient_prefix z h R B N H r zero
    (GaussianBarnesCanonicalCorrectedMercatorCofinal.interval_input two z h R B H hs.andE₁)
  have et : Γ ⊢[PRAAx] T ≐ GaussianRationalHorner.qzero := GaussianRationalFiniteSum.sum_zero _ _
  have reorder : Γ ⊢[PRAAx] y ≐ qmul (secondWeight h B) b :=
    (GaussianReciprocalHorner.qmul_associative c b s).eqTrans
      ((qmul_congr (.eqRefl _) (GaussianRationalPowerAlgebra.qmul_commutative b s)).eqTrans
        (GaussianReciprocalHorner.qmul_associative c s b).eqSymm)
  exact exactPrefix.eqTrans ((qadd_congr (.eqRefl _) et).eqTrans
    ((GaussianReciprocalHorner.qadd_commutative (qadd x y) GaussianRationalHorner.qzero).eqTrans
      ((qzero_add _ (qadd_canonical x y)).eqTrans (qadd_congr (.eqRefl _) reorder))))

def clock (p : PTm n) : PTm n :=
  GaussianBoundedConstantProductName.clock (GaussianFastValueCut.exponent two p) one

private theorem sample_at (p z h R B : PTm n) : Γ ⊢[PRAAx]
    ap2 nameF p (data z h R B) ≐
      qadd (qmul (ofGaussian h B) (GaussianBarnesCanonicalDerivativeCofinal.sample (clock p) z R B))
        (qmul (secondWeight h B) (GaussianBarnesCanonicalSecondDerivativeCofinal.sample (clock p) z R B)) := by
  let t := GaussianFastValueCut.exponent two p
  let x := coeffData z R B
  let a := ofGaussian h B
  let b := secondWeight h B
  let s := clock p
  let X := pd one a x
  let Y := pd one b x
  have sum := (GaussianNameArithmetic.add_at (Γ := Γ) (P D) (P S) X Y p).eqTrans
    (GaussianExponentialReference.recode_fixed _ (qadd_canonical (ap2 (P D) t X) (ap2 (P S) t Y)))
  have e := (GaussianBoundedConstantProductName.sample_at (Γ := Γ) D t one a x).eqTrans
    (qmul_congr (.eqRefl _) (GaussianBarnesCanonicalDerivativeCofinal.sample_at s z R B))
  have f := (GaussianBoundedConstantProductName.sample_at (Γ := Γ) S t one b x).eqTrans
    (qmul_congr (.eqRefl _) (GaussianBarnesCanonicalSecondDerivativeCofinal.sample_at s z R B))
  exact sum.eqTrans (qadd_congr e f)

private theorem model_observation (p z h R B H r : PTm n) (hs : Γ ⊢[PRAAx] input z h R B H)
    (h1 : Γ ⊢[PRAAx] le (l1 (clock p) R) r) (h2 : Γ ⊢[PRAAx] le (l2 (clock p) R) r) :
    Γ ⊢[PRAAx] distanceBounded (V two z h B (initial R) r) (ap2 nameF p (data z h R B)) two (unit p) := by
  let s := clock p
  let N := initial R
  let a := ofGaussian h B
  let b := secondWeight h B
  have hsU := unit_positive (Γ := Γ) s
  have hz := hs.andE₁.andE₁
  have ub := weight_bounds z h R B H hs
  have fp := GaussianBarnesCanonicalDerivativeCofinal.late_prefix_error s z R B r hz h1
  have sp := GaussianBarnesCanonicalSecondDerivativeCofinal.late_prefix_error s z R B r hz h2
  have f := GaussianRationalRoundedPower.multiply_distance_bound a _ _ _ _ hsU ub.andE₁ fp
  have g := GaussianRationalRoundedPower.multiply_distance_bound b _ _ _ _ hsU ub.andE₂ sp
  have joined := sum_distance _ _ _ _ _ _ _ hsU f g
  have d : Γ ⊢[PRAAx] distanceBounded (V two z h B N r) (ap2 nameF p (data z h R B)) two (unit s) :=
    distance_congr (finite_binding z h R B H r hs).eqSymm (sample_at p z h R B).eqSymm
    (by ipra_ring) (.eqRefl _) joined
  have hps : Γ ⊢[PRAAx] le p s := le_trans (le_add_right _ _) (le_add_right _ _)
  have grow := GaussianFactorBudget.power_monotone_length two p s (le_succ_self one) hps
  exact distance_radius_mono _ _ _ _ _ _ hsU (unit_positive p) (Common.mul_le_mul (le_refl _) grow) d

theorem observation (p z h R B H : PTm n) (hs : Γ ⊢[PRAAx] input z h R B H) : Γ ⊢[PRAAx]
    distanceBounded (ap2 G p (gd z h R B)) (ap2 nameF p (data z h R B))
      (diagonalNumerator (errorNumerator H) (errorDenominator R B) (num 5) p)
      (diagonalDenominator (errorDenominator R B) p) := by
  let s := clock p
  let N := initial R
  let K := GaussianBarnesCanonicalCorrectedMercatorCofinal.cutoff p R
  let r := K+(l1 s R+l2 s R)
  let x := gd z h R B
  let v := V two z h B N r
  let A := errorNumerator H
  let E := errorDenominator R B
  let U := unit p
  have hp := unit_positive (Γ := Γ) p
  have hB := hs.andE₁.andE₁.andE₁
  have hE := GaussianBarnesCanonicalCorrectedMercatorCofinal.analytic_denominator_positive two R B hB
  have hEU := positive_product E U hE hp
  have cut : Γ ⊢[PRAAx] le K (GaussianBarnesCanonicalCorrectedMercatorCofinal.freezeDenominator R r) := by
    have h : Γ ⊢[PRAAx] le r (GaussianBarnesCanonicalCorrectedMercatorCofinal.freezeDenominator R r) :=
      le_of_eq_add (d := num 3*N+two*r) (by
        unfold GaussianBarnesCanonicalCorrectedMercatorCofinal.freezeDenominator GaussianBarnesCanonicalLogTail.tailDenominator N
        ipra_ring)
    exact le_trans (le_add_right _ _) h
  have near := GaussianBarnesCanonicalCorrectedMercatorCofinal.rate_of_cutoff p two z h R B H r hs.andE₁ cut
  have raw := diagonal_rate G constantF x v _ _ p (positive_product _ _ hp hE) near
  have analytic : Γ ⊢[PRAAx] distanceBounded (ap2 G p x) v (A*U+num 3*E) (E*U) :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ hp hE) hp) hEU
      (le_of_eq_add (d := zero) (by dsimp only [A,E,U,errorNumerator,errorDenominator,
        GaussianBarnesCanonicalCorrectedMercatorCofinal.scheduledNumerator,
        GaussianBarnesCanonicalCorrectedMercatorCofinal.scheduledDenominator,
        GaussianNamedRateComposition.leadingNumerator]; ipra_ring))
      (distance_congr (.eqRefl _) (constant_at p v) (.eqRefl _) (.eqRefl _) raw)
  have last := model_observation p z h R B H r hs
    (le_trans (le_add_right _ _) (le_add_left _ _)) (le_trans (le_add_left _ _) (le_add_left _ _))
  have scaled := distance_radius_mono _ _ two U (two*E) (E*U) hp hEU
    (le_of_eq_add (d := zero) (by ipra_ring)) last
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [diagonalNumerator,A,E,U]; ipra_ring)
    (.eqRefl _) (distance_triangle_same _ _ _ _ _ _ hEU analytic scaled)

theorem rate (z h R B H : PTm n) (hs : Γ ⊢[PRAAx] input z h R B H) : Γ ⊢[PRAAx]
    independentRate G nameF (gd z h R B) (data z h R B) (errorNumerator H) (errorDenominator R B) := by
  have hz := hs.andE₁.andE₁
  have hw := hs.andE₁.andE₂.andE₁
  apply GaussianNamedLipschitzRate.independent_rate G nameF (gd z h R B) (data z h R B)
    (errorNumerator H) (errorDenominator R B) (num 5)
    (GaussianBarnesCanonicalCorrectedMercatorCofinal.analytic_denominator_positive two R B hz.andE₁)
    (GaussianBarnesCanonicalCorrectedMercatorCofinal.regular z h R B hz hw) (regular z h R B H hs)
  refine .allI ?_
  let sh (u : PTm n) := Syn.shift u
  have hy : Γ.map Fm.shift ⊢[PRAAx] input (sh z) (sh h) (sh R) (sh B) (sh H) := by
    simpa [Fm.shift,sh,Syn.shift] using hs.shift
  simpa only [diagonalEnvelope,sh,Syn.shift,GaussianBarnesCanonicalCorrectedMercatorCofinal.subst_data,
    subst_data,subst_errorNumerator,subst_errorDenominator,PTm.subst_num] using
    observation (var 0) (sh z) (sh h) (sh R) (sh B) (sh H) hy

theorem actual_Barnes_fixed_cofinal_second_order_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      independentRate G nameF (gd (var 0) (var 1) (var 2) (var 3)) (data (var 0) (var 1) (var 2) (var 3))
        (errorNumerator (var 4)) (errorDenominator (var 2) (var 3))) :=
  closeUniv 5 (.impI (rate _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTailQuadraticName
