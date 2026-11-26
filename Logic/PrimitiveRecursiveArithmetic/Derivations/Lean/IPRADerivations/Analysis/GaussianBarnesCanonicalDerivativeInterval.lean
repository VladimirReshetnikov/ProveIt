import IPRADerivations.Analysis.GaussianReciprocalSquareSumDistance
import IPRADerivations.Analysis.GaussianBarnesCanonicalDerivativeBinding
import IPRADerivations.Analysis.GaussianBarnesCanonicalDerivativeTail
import IPRADerivations.Analysis.GaussianBarnesCanonicalFiniteLogRows
import IPRADerivations.Analysis.GaussianRationalQuadratureDifference
import IPRADerivations.Analysis.GaussianNamedDifferenceQuotientProperness
import IPRADerivations.Analysis.GaussianNamedLipschitzRate
import IPRADerivations.Analysis.GaussianNamedRateTransport

/-!
# Summing the Barnes first-order increment estimates

At one late row clock, the difference of the two original logarithm
sums is the sum of their row differences. The linear terms sum to the
literal input increment times the rational derivative sum. The reciprocal-
square telescope keeps the leading error bounded independently of the
number of rows.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDerivativeInterval

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open ComplexLogarithmRemainder (add)
open GaussianBarnesCanonicalDerivativeAlgebra (linearTerm)
open GaussianBarnesCanonicalLogTail (source)
open GaussianBarnesCanonicalHead (parameters subst_parameters)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianFastValueCut (exponent query_budget)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNamedInverseRate (independentRate diagonal_rate)
open GaussianNamedLipschitzRate (diagonalEnvelope diagonalNumerator diagonalDenominator)
open GaussianNameEquivalence (crossEquivalent cross_refl)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalFiniteSum (sum multiplyBody multiply_body_at sum_multiply)
open GaussianRationalHorner (ofGaussian qmul positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalQuadratureDifference (differenceBody difference_body_at finite_sum_difference)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr)
open GaussianReciprocalSquareInterval (denominator denominator_positive)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Diff" => GaussianNamedDifference.nameF
local notation "diffData" => GaussianNamedDifference.data
local notation "L" => GaussianBarnesCanonicalLogFactor.nameF
local notation "ld" => GaussianBarnesCanonicalLogFactor.data
local notation "S" => GaussianBarnesCanonicalFiniteLogRows.nameF
local notation "sd" => GaussianBarnesCanonicalFiniteLogRows.data
local notation "F" => GaussianBarnesCanonicalFiniteLog.nameF
local notation "fd" => GaussianBarnesCanonicalFiniteLog.data
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

abbrev errorNumerator (R H : PTm n) : PTm n := GaussianBarnesCanonicalDerivativeBinding.boundNumerator R H
def errorDenominator (B N r : PTm n) : PTm n := (B*B)*denominator N r

def input (z h R B N H : PTm n) : Fm PTm n :=
  source z R B N ⋏ (source (add z h) R B N ⋏ (ComplexLogarithmRemainder.bounded h H ⋏
    (le (num 16*H) (B*N) ⋏ le H B)))

def rowRate (z h R B N H i : PTm n) : Fm PTm n :=
  let k := succ (N+i)
  independentRate (Diff L L) constantF (diffData (ld (add z h) R B k) (ld z R B k))
    (linearTerm z h B k) (errorNumerator R H) ((B*k)*(B*k))

def rowRates (z h R B N H : PTm n) : Fm PTm n :=
  .all (rowRate (Syn.shift z) (Syn.shift h) (Syn.shift R) (Syn.shift B) (Syn.shift N) (Syn.shift H) (var 0))

def incrementF : PR 2 := Diff F F
def incrementData (z h R B N r : PTm n) : PTm n :=
  diffData (fd (add z h) R B N r) (fd z R B N r)
def scaledValue (z h B N r : PTm n) : PTm n :=
  qmul (ofGaussian h B) (GaussianBarnesCanonicalDerivativeTail.value z B N r)

@[simp] theorem subst_errorNumerator {m : ℕ} (σ : Fin n → PTm m) (R H : PTm n) :
    Syn.subst σ (errorNumerator R H) = errorNumerator (Syn.subst σ R) (Syn.subst σ H) := by simp [errorNumerator]

@[simp] theorem subst_errorDenominator {m : ℕ} (σ : Fin n → PTm m) (B N r : PTm n) :
    Syn.subst σ (errorDenominator B N r) = errorDenominator (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ r) := by
  simp [errorDenominator]

@[simp] theorem subst_input {m : ℕ} (σ : Fin n → PTm m) (z h R B N H : PTm n) :
    (input z h R B N H).subst σ = input (Syn.subst σ z) (Syn.subst σ h)
      (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ H) := by
  simp [input]

@[simp] theorem subst_rowRate {m : ℕ} (σ : Fin n → PTm m) (z h R B N H i : PTm n) :
    (rowRate z h R B N H i).subst σ =
      rowRate (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ H) (Syn.subst σ i) := by
  simp [rowRate]

@[simp] theorem subst_rowRates {m : ℕ} (σ : Fin n → PTm m) (z h R B N H : PTm n) :
    (rowRates z h R B N H).subst σ =
      rowRates (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ H) := by
  simp [rowRates,Syn.subst_shift,Syn.shift_subst]

@[simp] theorem subst_incrementData {m : ℕ} (σ : Fin n → PTm m) (z h R B N r : PTm n) :
    Syn.subst σ (incrementData z h R B N r) =
      incrementData (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ r) := by
  simp [incrementData]

@[simp] theorem subst_scaledValue {m : ℕ} (σ : Fin n → PTm m) (z h B N r : PTm n) :
    Syn.subst σ (scaledValue z h B N r) =
      scaledValue (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ r) := by simp [scaledValue]

theorem error_denominator_positive (B N r : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] le one (errorDenominator B N r) :=
  positive_product _ _ (positive_product _ _ hB hB) (denominator_positive N r hN)

private theorem row_rate_at (z h R B N H i : PTm n) (hr : Γ ⊢[PRAAx] rowRates z h R B N H) :
    Γ ⊢[PRAAx] rowRate z h R B N H i := by
  simpa only [rowRates,subst_rowRate,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using hr.allE i

private theorem row_distance (p z h R B N H i : PTm n) (hz : Γ ⊢[PRAAx] source z R B N)
    (hw : Γ ⊢[PRAAx] source (add z h) R B N) (hr : Γ ⊢[PRAAx] rowRate z h R B N H i) :
    let k := succ (N+i)
    let d := (B*B)*(k*k)
    Γ ⊢[PRAAx] distanceBounded (qsub (ap2 L p (ld (add z h) R B k)) (ap2 L p (ld z R B k)))
      (linearTerm z h B k) (errorNumerator R H*unit p+num 8*d) (d*unit p) := by
  let k := succ (N+i)
  let d := (B*k)*(B*k)
  let a := ld (add z h) R B k
  let b := ld z R B k
  have bk := positive_product B k hz.andE₁ (zero_lt_succ _)
  have hd : Γ ⊢[PRAAx] le one d := positive_product _ _ bk bk
  have hu := unit_positive (Γ := Γ) p
  have hdu := positive_product d (unit p) hd hu
  have e := GaussianNamedDifference.sample_error L L a b p
    (GaussianBarnesCanonicalLogFactor.regular _ _ _ _ (GaussianBarnesCanonicalLogTail.row_source _ _ _ _ _ hw))
    (GaussianBarnesCanonicalLogFactor.regular _ _ _ _ (GaussianBarnesCanonicalLogTail.row_source _ _ _ _ _ hz))
  have first := distance_radius_mono _ _ _ _ (num 6*d) (d*unit p) hu hdu
    (le_of_eq_add (d := zero) (by ipra_ring)) (distance_symmetric _ _ _ _ hu e)
  have last := diagonal_rate (Diff L L) constantF (diffData a b) (linearTerm z h B k) (errorNumerator R H) d p hd hr
  exact distance_congr (.eqRefl _) (constant_at p _)
    (by dsimp only [d,k]; ipra_ring) (by dsimp only [d,k]; ipra_ring)
    (distance_triangle_same _ _ _ _ _ _ hdu first last)

private theorem finite_rows (p z h R B N H r : PTm n) (hz : Γ ⊢[PRAAx] source z R B N)
    (hw : Γ ⊢[PRAAx] source (add z h) R B N) (hr : Γ ⊢[PRAAx] rowRates z h R B N H) :
    let body := GaussianNamedFiniteSumFamily.body L GaussianBarnesCanonicalFiniteLogRows.body
    let l := pairT p (parameters (add z h) R B N)
    let rdata := pairT p (parameters z R B N)
    Γ ⊢[PRAAx] distanceBounded (qsub (sum body r l) (sum body r rdata)) (scaledValue z h B N r)
      ((errorNumerator R H*unit p+num 8*errorDenominator B N r)*r) (errorDenominator B N r*unit p) := by
  let body := GaussianNamedFiniteSumFamily.body L GaussianBarnesCanonicalFiniteLogRows.body
  let db := differenceBody body body
  let tb := GaussianBarnesCanonicalDerivativeTail.body
  let mb := multiplyBody tb
  let l := pairT p (parameters (add z h) R B N)
  let d := pairT p (parameters z R B N)
  let x := pairT l d
  let y := pairT (ofGaussian h B) (GaussianBarnesCanonicalDerivativeTail.data z B N)
  have each : Γ ⊢[PRAAx] GaussianReciprocalSquareSumDistance.rows db mb N (errorNumerator R H)
      (B*B) (num 8) (unit p) x y := by
    refine .allI ?_
    let sh (a : PTm n) := Syn.shift a
    let Δ := Γ.map Fm.shift
    let i : PTm (n+1) := var 0
    have hz' : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh N) := by simpa [Fm.shift,Syn.shift,sh,Δ] using hz.shift
    have hw' : Δ ⊢[PRAAx] source (add (sh z) (sh h)) (sh R) (sh B) (sh N) := by simpa [Fm.shift,Syn.shift,sh,Δ] using hw.shift
    have hr' : Δ ⊢[PRAAx] rowRates (sh z) (sh h) (sh R) (sh B) (sh N) (sh H) := by simpa [Fm.shift,Syn.shift,sh,Δ] using hr.shift
    have bound := row_distance (sh p) (sh z) (sh h) (sh R) (sh B) (sh N) (sh H) i hz' hw'
      (row_rate_at _ _ _ _ _ _ _ hr')
    have readA := (GaussianNamedFiniteSumFamily.term_at (Γ := Δ) L GaussianBarnesCanonicalFiniteLogRows.body i (sh p) _).eqTrans
      (congrAp2 L (.eqRefl _) (GaussianBarnesCanonicalFiniteLogRows.body_at i (add (sh z) (sh h)) (sh R) (sh B) (sh N)))
    have readB := (GaussianNamedFiniteSumFamily.term_at (Γ := Δ) L GaussianBarnesCanonicalFiniteLogRows.body i (sh p) _).eqTrans
      (congrAp2 L (.eqRefl _) (GaussianBarnesCanonicalFiniteLogRows.body_at i (sh z) (sh R) (sh B) (sh N)))
    have readL := (difference_body_at body body i (pairT (sh p) (parameters (add (sh z) (sh h)) (sh R) (sh B) (sh N)))
      (pairT (sh p) (parameters (sh z) (sh R) (sh B) (sh N)))).eqTrans (qsub_congr readA readB)
    have readR := (multiply_body_at (Γ := Δ) tb (ofGaussian (sh h) (sh B)) i _).eqTrans
      (qmul_congr (.eqRefl _) (GaussianBarnesCanonicalDerivativeTail.body_at (sh z) (sh B) (sh N) i))
    simpa only [GaussianReciprocalSquareSumDistance.rows,GaussianReciprocalSquareSumDistance.radiusDenominator,
      Syn.shift,sh,Δ,i,x,y,l,d,subst_pairT,subst_parameters,ComplexLogarithmRemainder.subst_add,
      GaussianRationalHorner.subst_ofGaussian,GaussianBarnesCanonicalDerivativeTail.subst_data,
      subst_errorNumerator,GaussianCoefficientNameBounds.subst_unit,PTm.subst_mul,PTm.subst_num] using
      distance_congr readL.eqSymm readR.eqSymm (.eqRefl _) (.eqRefl _) bound
  have result := GaussianReciprocalSquareSumDistance.sum_distance db mb N (errorNumerator R H) (B*B)
    (num 8) (unit p) x y r hz.andE₂.andE₁ (positive_product _ _ hz.andE₁ hz.andE₁) (unit_positive p) each
  exact distance_congr (finite_sum_difference body body r l d) (sum_multiply tb (ofGaussian h B) r _)
    (.eqRefl _) (.eqRefl _) result

private theorem row_sum_observation (p z h R B N H r : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B N) (hw : Γ ⊢[PRAAx] source (add z h) R B N)
    (hr : Γ ⊢[PRAAx] rowRates z h R B N H) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (Diff S S) p (diffData (sd (add z h) R B N r) (sd z R B N r)))
      (ap2 constantF p (scaledValue z h B N r))
      (diagonalNumerator (errorNumerator R H*r) (errorDenominator B N r) (num 14) p)
      (diagonalDenominator (errorDenominator B N r) p) := by
  let k := exponent r p
  let U := unit p
  let V := unit k
  let D := errorDenominator B N r
  let C := errorNumerator R H
  let x := sd (add z h) R B N r
  let y := sd z R B N r
  have dpos := error_denominator_positive B N r hz.andE₁ hz.andE₂.andE₁
  have hU := unit_positive (Γ := Γ) p
  have hV := unit_positive (Γ := Γ) k
  have hz' := GaussianNamedFiniteSumFamily.regular L GaussianBarnesCanonicalFiniteLogRows.body r _
    (GaussianBarnesCanonicalFiniteLogRows.rows_regular z R B N r hz)
  have hw' := GaussianNamedFiniteSumFamily.regular L GaussianBarnesCanonicalFiniteLogRows.body r _
    (GaussianBarnesCanonicalFiniteLogRows.rows_regular (add z h) R B N r hw)
  have e := GaussianNamedDifference.sample_error S S x y p hw' hz'
  have first := distance_radius_mono _ _ _ _ (num 6*D) (D*U) hU (positive_product _ _ dpos hU)
    (le_of_eq_add (d := zero) (by ipra_ring)) e
  have raw := finite_rows k z h R B N H r hz hw hr
  have narrow := distance_radius_mono _ _ _ _ (C*r*U+num 8*D) (D*U)
    (positive_product _ _ dpos hV) (positive_product _ _ dpos hU)
    (by have budget : Γ ⊢[PRAAx] le (r*U) V := query_budget r p
        ipra_le 8*𝔞(D)*𝔞(D)*sl budget) raw
  have last := distance_congr
    (qsub_congr (GaussianNamedFiniteSumFamily.sample_at L GaussianBarnesCanonicalFiniteLogRows.body p r _).eqSymm
      (GaussianNamedFiniteSumFamily.sample_at L GaussianBarnesCanonicalFiniteLogRows.body p r _).eqSymm)
    (constant_at p _).eqSymm (.eqRefl _) (.eqRefl _) narrow
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold diagonalNumerator; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (positive_product _ _ dpos hU) first last)

theorem rate_of_rows (z h R B N H r : PTm n) (hz : Γ ⊢[PRAAx] source z R B N)
    (hw : Γ ⊢[PRAAx] source (add z h) R B N) (hr : Γ ⊢[PRAAx] rowRates z h R B N H) :
    Γ ⊢[PRAAx] independentRate incrementF constantF (incrementData z h R B N r) (scaledValue z h B N r)
      (errorNumerator R H*r) (errorDenominator B N r) := by
  let x := sd (add z h) R B N r
  let y := sd z R B N r
  let a := fd (add z h) R B N r
  let b := fd z R B N r
  let c := scaledValue z h B N r
  have dpos := error_denominator_positive B N r hz.andE₁ hz.andE₂.andE₁
  have hS₁ := GaussianNamedFiniteSumFamily.regular L GaussianBarnesCanonicalFiniteLogRows.body r _
    (GaussianBarnesCanonicalFiniteLogRows.rows_regular (add z h) R B N r hw)
  have hS₂ := GaussianNamedFiniteSumFamily.regular L GaussianBarnesCanonicalFiniteLogRows.body r _
    (GaussianBarnesCanonicalFiniteLogRows.rows_regular z R B N r hz)
  have hF₁ := GaussianBarnesCanonicalFiniteLog.regular (add z h) R B N r hw
  have hF₂ := GaussianBarnesCanonicalFiniteLog.regular z R B N r hz
  have env : Γ ⊢[PRAAx] diagonalEnvelope (Diff S S) constantF (diffData x y) c (errorNumerator R H*r)
      (errorDenominator B N r) (num 14) := by
    refine .allI ?_
    let sh (v : PTm n) := Syn.shift v
    let Δ := Γ.map Fm.shift
    have hz' : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh N) := by simpa [Fm.shift,Syn.shift,sh,Δ] using hz.shift
    have hw' : Δ ⊢[PRAAx] source (add (sh z) (sh h)) (sh R) (sh B) (sh N) := by simpa [Fm.shift,Syn.shift,sh,Δ] using hw.shift
    have hr' : Δ ⊢[PRAAx] rowRates (sh z) (sh h) (sh R) (sh B) (sh N) (sh H) := by simpa [Fm.shift,Syn.shift,sh,Δ] using hr.shift
    simpa only [diagonalEnvelope,Syn.shift,sh,Δ,x,y,c,GaussianNamedDifference.subst_data,
      GaussianBarnesCanonicalFiniteLogRows.subst_data,ComplexLogarithmRemainder.subst_add,subst_scaledValue,
      subst_errorNumerator,subst_errorDenominator,PTm.subst_mul,PTm.subst_num] using
      row_sum_observation (var 0) (sh z) (sh h) (sh R) (sh B) (sh N) (sh H) (sh r) hz' hw' hr'
  have raw := GaussianNamedLipschitzRate.independent_rate (Diff S S) constantF (diffData x y) c
    (errorNumerator R H*r) (errorDenominator B N r) (num 14) dpos
    (GaussianNamedDifference.name_regular S S x y hS₁ hS₂) (constant_regular c) env
  have eq := GaussianNamedDifferenceQuotientProperness.difference_proper F S F S a x b y
    hF₁ hS₁ hF₂ hS₂
    (GaussianNameEquivalence.cross_symm _ _ _ _ (GaussianBarnesCanonicalFiniteLogRows.finite_cross (add z h) R B N r hw))
    (GaussianNameEquivalence.cross_symm _ _ _ _ (GaussianBarnesCanonicalFiniteLogRows.finite_cross z R B N r hz))
  exact GaussianNamedRateTransport.transport (Diff S S) constantF incrementF constantF (diffData x y) c (incrementData z h R B N r) c
    (errorNumerator R H*r) (errorDenominator B N r) dpos raw eq (cross_refl _ _ (constant_regular c))

theorem rows_of_input (z h R B N H : PTm n) (hs : Γ ⊢[PRAAx] input z h R B N H) :
    Γ ⊢[PRAAx] rowRates z h R B N H := by
  refine .allI ?_
  let sh (t : PTm n) := Syn.shift t
  let Δ := Γ.map Fm.shift
  let i : PTm (n+1) := var 0
  let k := succ (sh N+i)
  have src : Δ ⊢[PRAAx] input (sh z) (sh h) (sh R) (sh B) (sh N) (sh H) := by
    simpa [Fm.shift,Syn.shift,sh,Δ] using hs.shift
  have grow : Δ ⊢[PRAAx] le (sh N) k := le_trans (le_add_right _ _) (le_succ_self _)
  have step : Δ ⊢[PRAAx] GaussianBarnesCanonicalRelativeStep.source (sh z) (sh h) (sh R) (sh B) k (sh H) :=
    .andI (GaussianBarnesCanonicalLogTail.row_source _ _ _ _ i src.andE₁)
      (.andI (GaussianBarnesCanonicalLogTail.row_source _ _ _ _ i src.andE₂.andE₁)
        (.andI src.andE₂.andE₂.andE₁
          (le_trans src.andE₂.andE₂.andE₂.andE₁ (le_mul_mono (le_refl _) grow))))
  exact GaussianBarnesCanonicalDerivativeBinding.independent_rate (sh z) (sh h) (sh R) (sh B) k (sh H)
    step src.andE₂.andE₂.andE₂.andE₂

theorem rate (z h R B N H r : PTm n) (hs : Γ ⊢[PRAAx] input z h R B N H) :
    Γ ⊢[PRAAx] independentRate incrementF constantF (incrementData z h R B N r) (scaledValue z h B N r)
      (errorNumerator R H*r) (errorDenominator B N r) :=
  rate_of_rows z h R B N H r hs.andE₁ hs.andE₂.andE₁ (rows_of_input z h R B N H hs)

theorem actual_Barnes_finite_logarithm_first_order_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (let z := var 0
     let h := var 1
     let R := var 2
     let B := var 3
     let N := var 4
     let H := var 5
     let r := var 6
     input z h R B N H ⟶
       independentRate incrementF constantF (incrementData z h R B N r) (scaledValue z h B N r)
         (errorNumerator R H*r) (errorDenominator B N r)) :=
  closeUniv 7 (.impI (rate _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDerivativeInterval
