import IPRADerivations.Analysis.Barnes.Taylor.RelativeExpansions.GaussianBarnesCanonicalCorrectedMercator
import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.GaussianBarnesCanonicalDerivativeInterval

/-!
# Summable arbitrary-degree remainder for the original Barnes logarithm

The interval uses the original rounded logarithm names. Its rational
polynomial is a finite sum of corrected Mercator rows. The squared-index
telescope bounds the remainder uniformly as the interval grows.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCorrectedMercatorInterval

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open ComplexLogarithmRemainder (add)
open GaussianBarnesCanonicalLogTail (source row_source)
open GaussianBarnesCanonicalHead (parameters subst_parameters)
open GaussianBarnesCanonicalCorrectedMercator (polynomial numerator scaleDenominator scale_denominator_positive correctionRate)
open GaussianBarnesCanonicalDerivativeInterval (incrementF incrementData)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianFastValueCut (exponent query_budget)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNamedInverseRate (independentRate diagonal_rate)
open GaussianNameEquivalence (cross_refl cross_symm)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalFiniteSum (sum)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalQuadratureDifference (differenceBody difference_body_at finite_sum_difference)
open GaussianRationalSyntheticDivision (qsub_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Diff" => GaussianNamedDifference.nameF
local notation "dd" => GaussianNamedDifference.data
local notation "L" => GaussianBarnesCanonicalLogFactor.nameF
local notation "ld" => GaussianBarnesCanonicalLogFactor.data
local notation "S" => GaussianBarnesCanonicalFiniteLogRows.nameF
local notation "sd" => GaussianBarnesCanonicalFiniteLogRows.data
local notation "F" => GaussianBarnesCanonicalFiniteLog.nameF
local notation "fd" => GaussianBarnesCanonicalFiniteLog.data
local notation "rowBody" => GaussianBarnesCanonicalFiniteLogRows.body
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def input (m z h R B N H : PTm n) : Fm PTm n :=
  source z R B N ⋏ (source (add z h) R B N ⋏ (ComplexLogarithmRemainder.bounded h H ⋏
    (le (num 16*H) (B*N) ⋏ le two m)))

def polynomialData (m z h B N : PTm n) : PTm n := pairT m (pairT z (pairT h (pairT B N)))

def polynomialBody : PTm 2 :=
  let x := var 1
  let y := sndT x
  let u := sndT y
  let v := sndT u
  polynomial (fstT x) (fstT y) (fstT u) (fstT v) (succ (sndT v+var 0))

def value (m z h B N r : PTm n) : PTm n := sum polynomialBody r (polynomialData m z h B N)

def errorDenominator (m B N r : PTm n) : PTm n :=
  scaleDenominator m B*GaussianReciprocalSquareInterval.denominator N r

@[simp] theorem subst_input {l : ℕ} (σ : Fin n → PTm l) (m z h R B N H : PTm n) :
    (input m z h R B N H).subst σ = input (Syn.subst σ m) (Syn.subst σ z) (Syn.subst σ h)
      (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ H) := by simp [input,two]

@[simp] theorem subst_polynomialData {l : ℕ} (σ : Fin n → PTm l) (m z h B N : PTm n) :
    Syn.subst σ (polynomialData m z h B N) =
      polynomialData (Syn.subst σ m) (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ N) :=
  by simp [polynomialData]

@[simp] theorem subst_value {l : ℕ} (σ : Fin n → PTm l) (m z h B N r : PTm n) :
    Syn.subst σ (value m z h B N r) = value (Syn.subst σ m) (Syn.subst σ z) (Syn.subst σ h)
      (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ r) := by simp [value]

@[simp] theorem subst_errorDenominator {l : ℕ} (σ : Fin n → PTm l) (m B N r : PTm n) :
    Syn.subst σ (errorDenominator m B N r) = errorDenominator (Syn.subst σ m) (Syn.subst σ B)
      (Syn.subst σ N) (Syn.subst σ r) := by simp [errorDenominator]

theorem error_denominator_positive (m B N r : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] le one (errorDenominator m B N r) :=
  positive_product _ _ (scale_denominator_positive m B hB) (GaussianReciprocalSquareInterval.denominator_positive N r hN)

theorem polynomial_body_at (m z h B N i : PTm n) : Γ ⊢[PRAAx]
    inst2 polynomialBody i (polynomialData m z h B N) ≐ polynomial m z h B (succ (N+i)) := by
  let x := polynomialData m z h B N
  let y := sndT x
  let u := sndT y
  let v := sndT u
  have hy := snd_pair (Γ := Γ) m (pairT z (pairT h (pairT B N)))
  have hu := (congrSnd hy).eqTrans (snd_pair z (pairT h (pairT B N)))
  have hv := (congrSnd hu).eqTrans (snd_pair h (pairT B N))
  let t : PTm 6 := polynomial (var 1) (var 2) (var 3) (var 4) (succ (var 5+var 0))
  have read := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) t
    (σ := ![i,fstT x,fstT y,fstT u,fstT v,sndT v]) (σ' := ![i,m,z,h,B,N]) (fun j => by
      fin_cases j
      · exact .eqRefl i
      · exact fst_pair _ _
      · exact (congrFst hy).eqTrans (fst_pair _ _)
      · exact (congrFst hu).eqTrans (fst_pair _ _)
      · exact (congrFst hv).eqTrans (fst_pair _ _)
      · exact (congrSnd hv).eqTrans (snd_pair _ _))
  simpa only [t,inst2,polynomialBody,GaussianBarnesCanonicalCorrectedMercator.subst_polynomial,subst_fstT,subst_sndT,
    PTm.subst_add,PTm.subst_succ,Syn.subst_var,Matrix.cons_val,x,y,u,v] using read

private theorem relative_input (m z h R B N H i : PTm n) (hs : Γ ⊢[PRAAx] input m z h R B N H) :
    Γ ⊢[PRAAx] GaussianBarnesCanonicalRelativeStep.source z h R B (succ (N+i)) H := by
  have grow := le_trans (le_add_right (Γ := Γ) N i) (le_succ_self (N+i))
  exact .andI (row_source z R B N i hs.andE₁)
    (.andI (row_source (add z h) R B N i hs.andE₂.andE₁)
      (.andI hs.andE₂.andE₂.andE₁ (le_trans hs.andE₂.andE₂.andE₂.andE₁ (le_mul_mono (le_refl _) grow))))

private theorem row_distance (p m z h R B N H i : PTm n) (hs : Γ ⊢[PRAAx] input m z h R B N H) :
    let k := succ (N+i)
    let d := GaussianBarnesCanonicalCorrectedMercator.denominator m B k
    Γ ⊢[PRAAx] distanceBounded (qsub (ap2 L p (ld (add z h) R B k)) (ap2 L p (ld z R B k)))
      (polynomial m z h B k) (numerator m H*unit p+num 8*d) (d*unit p) := by
  let k := succ (N+i)
  let d := GaussianBarnesCanonicalCorrectedMercator.denominator m B k
  let a := ld (add z h) R B k
  let b := ld z R B k
  have hrow := relative_input m z h R B N H i hs
  have hd := GaussianBarnesCanonicalCorrectedMercator.denominator_positive m B k hs.andE₁.andE₁ (zero_lt_succ _)
  have hu := unit_positive (Γ := Γ) p
  have hdu := positive_product _ _ hd hu
  have observations := GaussianNamedDifference.sample_error L L a b p
    (GaussianBarnesCanonicalLogFactor.regular _ _ _ _ hrow.andE₂.andE₁)
    (GaussianBarnesCanonicalLogFactor.regular _ _ _ _ hrow.andE₁)
  have first := distance_radius_mono _ _ _ _ (num 6*d) (d*unit p) hu hdu
    (le_of_eq_add (d := zero) (by ipra_ring)) (distance_symmetric _ _ _ _ hu observations)
  have last := diagonal_rate (Diff L L) constantF (dd a b) (polynomial m z h B k) (numerator m H) d p hd
    (correctionRate m z h R B k H hrow hs.andE₂.andE₂.andE₂.andE₂)
  exact distance_congr (.eqRefl _) (GaussianGammaCanonicalExponent.constant_at p _)
    (by ipra_ring) (.eqRefl _) (distance_triangle_same _ _ _ _ _ _ hdu first last)

private theorem finite_rows (p m z h R B N H r : PTm n) (hs : Γ ⊢[PRAAx] input m z h R B N H) :
    let b := GaussianNamedFiniteSumFamily.body L rowBody
    let x := pairT p (parameters (add z h) R B N)
    let y := pairT p (parameters z R B N)
    Γ ⊢[PRAAx] distanceBounded (qsub (sum b r x) (sum b r y)) (value m z h B N r)
      ((numerator m H*unit p+num 8*errorDenominator m B N r)*r) (errorDenominator m B N r*unit p) := by
  let b := GaussianNamedFiniteSumFamily.body L rowBody
  let db := differenceBody b b
  let x := pairT p (parameters (add z h) R B N)
  let y := pairT p (parameters z R B N)
  let w := polynomialData m z h B N
  have each : Γ ⊢[PRAAx] GaussianReciprocalSquareSumDistance.rows db polynomialBody N (numerator m H)
      (scaleDenominator m B) (num 8) (unit p) (pairT x y) w := by
    refine .allI ?_
    let sh (a : PTm n) := Syn.shift a
    let Δ := Γ.map Fm.shift
    let i : PTm (n+1) := var 0
    have hs' : Δ ⊢[PRAAx] input (sh m) (sh z) (sh h) (sh R) (sh B) (sh N) (sh H) := by
      simpa [Fm.shift,Syn.shift,sh,Δ] using hs.shift
    have left := (GaussianNamedFiniteSumFamily.term_at (Γ := Δ) L rowBody i (sh p) _).eqTrans
      (congrAp2 L (.eqRefl _) (GaussianBarnesCanonicalFiniteLogRows.body_at i (add (sh z) (sh h)) (sh R) (sh B) (sh N)))
    have right := (GaussianNamedFiniteSumFamily.term_at (Γ := Δ) L rowBody i (sh p) _).eqTrans
      (congrAp2 L (.eqRefl _) (GaussianBarnesCanonicalFiniteLogRows.body_at i (sh z) (sh R) (sh B) (sh N)))
    have read := (difference_body_at b b i (pairT (sh p) (parameters (add (sh z) (sh h)) (sh R) (sh B) (sh N)))
      (pairT (sh p) (parameters (sh z) (sh R) (sh B) (sh N)))).eqTrans (qsub_congr left right)
    simpa only [GaussianReciprocalSquareSumDistance.rows,GaussianReciprocalSquareSumDistance.radiusDenominator,
      Syn.shift,sh,Δ,i,w,x,y,subst_pairT,subst_parameters,ComplexLogarithmRemainder.subst_add,
      GaussianBarnesCanonicalCorrectedMercator.subst_numerator,GaussianBarnesCanonicalCorrectedMercator.subst_scaleDenominator,
      GaussianCoefficientNameBounds.subst_unit,subst_polynomialData,PTm.subst_num,GaussianBarnesCanonicalCorrectedMercator.denominator] using
      distance_congr read.eqSymm (polynomial_body_at (sh m) (sh z) (sh h) (sh B) (sh N) i).eqSymm (.eqRefl _) (.eqRefl _)
        (row_distance (sh p) (sh m) (sh z) (sh h) (sh R) (sh B) (sh N) (sh H) i hs')
  have raw := GaussianReciprocalSquareSumDistance.sum_distance db polynomialBody N (numerator m H) (scaleDenominator m B)
    (num 8) (unit p) (pairT x y) w r hs.andE₁.andE₂.andE₁ (scale_denominator_positive m B hs.andE₁.andE₁)
    (unit_positive p) each
  exact distance_congr (finite_sum_difference b b r x y) (.eqRefl _) (.eqRefl _) (.eqRefl _) raw

private theorem observation (p m z h R B N H r : PTm n) (hs : Γ ⊢[PRAAx] input m z h R B N H) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (Diff S S) p (dd (sd (add z h) R B N r) (sd z R B N r)))
      (value m z h B N r) ((numerator m H*r)*unit p+num 14*errorDenominator m B N r)
      (errorDenominator m B N r*unit p) := by
  let k := exponent r p
  let U := unit p
  let V := unit k
  let D := errorDenominator m B N r
  let C := numerator m H
  let x := sd (add z h) R B N r
  let y := sd z R B N r
  have hz := hs.andE₁
  have hw := hs.andE₂.andE₁
  have dpos := error_denominator_positive m B N r hz.andE₁ hz.andE₂.andE₁
  have hU := unit_positive (Γ := Γ) p
  have hV := unit_positive (Γ := Γ) k
  have hz' := GaussianNamedFiniteSumFamily.regular L rowBody r _ (GaussianBarnesCanonicalFiniteLogRows.rows_regular z R B N r hz)
  have hw' := GaussianNamedFiniteSumFamily.regular L rowBody r _ (GaussianBarnesCanonicalFiniteLogRows.rows_regular (add z h) R B N r hw)
  have e := GaussianNamedDifference.sample_error S S x y p hw' hz'
  have first := distance_radius_mono _ _ _ _ (num 6*D) (D*U) hU (positive_product _ _ dpos hU)
    (le_of_eq_add (d := zero) (by ipra_ring)) e
  have narrow := distance_radius_mono _ _ _ _ (C*r*U+num 8*D) (D*U)
    (positive_product _ _ dpos hV) (positive_product _ _ dpos hU)
    (by have budget : Γ ⊢[PRAAx] le (r*U) V := query_budget r p
        ipra_le 8*𝔞(D)*𝔞(D)*sl budget) (finite_rows k m z h R B N H r hs)
  have last := distance_congr
    (qsub_congr (GaussianNamedFiniteSumFamily.sample_at L rowBody p r _).eqSymm
      (GaussianNamedFiniteSumFamily.sample_at L rowBody p r _).eqSymm)
    (.eqRefl _) (.eqRefl _) (.eqRefl _) narrow
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (positive_product _ _ dpos hU) first last)

theorem rate (m z h R B N H r : PTm n) (hs : Γ ⊢[PRAAx] input m z h R B N H) :
    Γ ⊢[PRAAx] independentRate incrementF constantF (incrementData z h R B N r) (value m z h B N r)
      (numerator m H*r) (errorDenominator m B N r) := by
  let x := sd (add z h) R B N r
  let y := sd z R B N r
  let a := fd (add z h) R B N r
  let b := fd z R B N r
  let c := value m z h B N r
  have hz := hs.andE₁
  have hw := hs.andE₂.andE₁
  have dpos := error_denominator_positive m B N r hz.andE₁ hz.andE₂.andE₁
  have hS₁ := GaussianNamedFiniteSumFamily.regular L rowBody r _ (GaussianBarnesCanonicalFiniteLogRows.rows_regular (add z h) R B N r hw)
  have hS₂ := GaussianNamedFiniteSumFamily.regular L rowBody r _ (GaussianBarnesCanonicalFiniteLogRows.rows_regular z R B N r hz)
  have hF₁ := GaussianBarnesCanonicalFiniteLog.regular (add z h) R B N r hw
  have hF₂ := GaussianBarnesCanonicalFiniteLog.regular z R B N r hz
  have env : Γ ⊢[PRAAx] GaussianNamedConstantRateFromSlack.sampleSlack (Diff S S) (dd x y) c (numerator m H*r)
      (errorDenominator m B N r) (num 14) := by
    refine .allI ?_
    let sh (v : PTm n) := Syn.shift v
    let Δ := Γ.map Fm.shift
    have hs' : Δ ⊢[PRAAx] input (sh m) (sh z) (sh h) (sh R) (sh B) (sh N) (sh H) := by
      simpa [Fm.shift,Syn.shift,sh,Δ] using hs.shift
    simpa only [GaussianNamedConstantRateFromSlack.sampleSlack,GaussianRationalSlackRemoval.slack,distanceBounded,
      unit,Syn.shift,sh,Δ,x,y,c,GaussianNamedDifference.subst_data,GaussianBarnesCanonicalFiniteLogRows.subst_data,
      ComplexLogarithmRemainder.subst_add,subst_value,GaussianBarnesCanonicalCorrectedMercator.subst_numerator,
      subst_errorDenominator,PTm.subst_mul,PTm.subst_num] using
      observation (var 0) (sh m) (sh z) (sh h) (sh R) (sh B) (sh N) (sh H) (sh r) hs'
  have raw := GaussianNamedConstantRateFromSlack.independent_rate (Diff S S) (dd x y) c
    (numerator m H*r) (errorDenominator m B N r) (num 14) (GaussianNamedDifference.name_regular S S x y hS₁ hS₂) dpos env
  have eq := GaussianNamedDifferenceQuotientProperness.difference_proper F S F S a x b y
    hF₁ hS₁ hF₂ hS₂
    (cross_symm _ _ _ _ (GaussianBarnesCanonicalFiniteLogRows.finite_cross (add z h) R B N r hw))
    (cross_symm _ _ _ _ (GaussianBarnesCanonicalFiniteLogRows.finite_cross z R B N r hz))
  exact GaussianNamedRateTransport.transport (Diff S S) constantF incrementF constantF (dd x y) c (incrementData z h R B N r) c
    (numerator m H*r) (errorDenominator m B N r) dpos raw eq (cross_refl _ _ (constant_regular c))

theorem actual_Barnes_finite_corrected_Mercator_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (let m := var 0
     let z := var 1
     let h := var 2
     let R := var 3
     let B := var 4
     let N := var 5
     let H := var 6
     let r := var 7
     input m z h R B N H ⟶
       independentRate incrementF constantF (incrementData z h R B N r) (value m z h B N r)
         (numerator m H*r) (errorDenominator m B N r)) :=
  closeUniv 8 (.impI (rate _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCorrectedMercatorInterval
