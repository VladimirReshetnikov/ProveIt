import IPRADerivations.Analysis.Gamma.Digamma.ElementaryBounds.GaussianGammaDigammaIntegerBracket
import IPRADerivations.Analysis.Gamma.Digamma.ElementaryBounds.GaussianGammaDigammaInteger

/-!
# The native positive-rational digamma reciprocal series

The finite value at cutoff N is −γ + H_N − Σ_{0≤j<N} 1/(x+j).
The original digamma name has independent rate a/N to these finite
names for x=a/b. Both observation errors are the original 2^{-p}
and 2^{-q} errors.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaSeries

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular harmonicPoint)
open GaussianGammaDerivativeAtOne (negativeGammaF negativeGammaData negativeGamma_regular)
open GaussianGammaDigammaFiniteSum (index reciprocalSum finite_sample_error row_source)
open GaussianGammaDigammaInteger (prefix_error)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameEquivalence (cross_at cross_symm)
open GaussianNameRingLaws (three)
open GaussianNamedDifference (difference_distance)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qadd canonical positive_product)
open GaussianRationalMetric (qsub distanceBounded)
open GaussianRationalSyntheticDivision (qadd_congr qsub_congr)
open GaussianStirlingGammaLogarithm (source)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "DF" => GaussianGammaDigammaNative.nameF
local notation "dd" => GaussianGammaDigammaNative.data
local notation "RF" => GaussianGammaDigammaReal.nameF
local notation "rd" => GaussianGammaDigammaReal.data
local notation "dg" => GaussianGammaDigammaInteger.target

def partialValue (a b N : PTm n) : PTm n := qsub (harmonicPoint N) (reciprocalSum a b N)
def nameF : PR 2 := addF negativeGammaF constantF
def data (a b N : PTm n) : PTm n := addData negativeGammaData (partialValue a b N)
def budget (a N : PTm n) : PTm n := num 10*N+num 5*a+num 17

ipra_subst partialValue
ipra_subst data
ipra_subst budget

theorem name_regular (a b N : PTm n) : Γ ⊢[PRAAx] pointCN nameF (data a b N) :=
  add_fast _ _ _ _ negativeGamma_regular (constant_regular _)

private theorem sample_canonical (p a b : PTm n) : Γ ⊢[PRAAx] canonical (ap2 DF p (dd a b)) :=
  GaussianNameArithmetic.multiply_canonical GaussianGammaC7Name.nameF GaussianEulerLogarithmicImproperName.nameF
    (GaussianGammaDigammaNative.reciprocalData a b) (GaussianGammaDigammaNative.derivativeData a b) p

private theorem subtract_difference (x y : PTm n) (hx : Γ ⊢[PRAAx] canonical x) (hy : Γ ⊢[PRAAx] canonical y) :
    Γ ⊢[PRAAx] qsub x (qsub x y) ≐ y := by
  exact (qsub_congr (GaussianRationalLinearProduct.add_sub_right y x hx).eqSymm (.eqRefl _)).eqTrans
    (GaussianReciprocalHorner.qsub_add_cancel y (qsub x y) hy)

private theorem native_tail (p a b N : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 DF p (dd (index a b N) b)) (ap2 DF p (dd (succ N) one))
      ((num 5*a+num 12)*N+a*unit p) (N*unit p) := by
  let A := index a b N
  let B := succ N
  let X := ap2 DF p (dd A b)
  let Y := ap2 DF p (dd B one)
  let u := ap2 RF p (rd A b)
  let v := ap2 RF p (rd B one)
  let T := unit p
  let D := N*T
  have hp := unit_positive (Γ := Γ) p
  have hd := positive_product _ _ hN hp
  have c := cross_at _ _ _ _ p p (GaussianGammaDigammaReal.original_cross A b (row_source a b N hs))
  have d := cross_at _ _ _ _ p p (cross_symm _ _ _ _ (GaussianGammaDigammaReal.original_cross (Γ := Γ) B one
    (.andI (zero_lt_succ N) (le_refl one))))
  have lift (x y : PTm n) (h : Γ ⊢[PRAAx] distanceBounded x y (T+T) (T*T)) : Γ ⊢[PRAAx]
      distanceBounded x y (two*N) D :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hp hp) hd
      (le_of_eq_add (d := zero) (by unfold D; ipra_ring)) h
  have e := GaussianGammaDigammaIntegerBracket.real_sample_distance p a b N hs hN
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold GaussianGammaDigammaIntegerBracket.numerator; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hd (distance_triangle_same _ _ _ _ _ _ hd (lift X u c) e) (lift v Y d))

set_option maxHeartbeats 850000 in
theorem sample_error (p a b N : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 DF p (dd a b)) (ap2 nameF p (data a b N))
      (GaussianNamedLipschitzRate.diagonalNumerator a N (budget a N) p)
      (GaussianNamedLipschitzRate.diagonalDenominator N p) := by
  let x := ap2 DF p (dd a b)
  let y := ap2 DF p (dd (index a b N) b)
  let z := ap2 DF p (dd (succ N) one)
  let h := ap2 negativeGammaF p (negativeGammaData : PTm n)
  let s := reciprocalSum a b N
  let v := dg p N
  let u := qadd h (partialValue a b N)
  let T := unit p
  let D := N*T
  have hp := unit_positive (Γ := Γ) p
  have hd := positive_product _ _ hN hp
  have lift (u v A : PTm n) (h : Γ ⊢[PRAAx] distanceBounded u v A T) : Γ ⊢[PRAAx]
      distanceBounded u v (A*N) D :=
    distance_radius_mono _ _ _ _ _ _ hp hd (le_of_eq_add (d := zero) (by unfold D; ipra_ring)) h
  have finite := finite_sample_error p a b N hs
  have rearr := difference_distance y y (qsub y x) s zero (N*num 5) T hp
    (GaussianRationalPowerDifference.distance_refl_zero y T hp) finite
  have e := subtract_difference (Γ := Γ) y x (sample_canonical p (index a b N) b) (sample_canonical p a b)
  have first := lift x (qsub y s) (N*num 5) (distance_congr e (.eqRefl _) (by ipra_ring) (.eqRefl _) rearr)
  have tail := native_tail p a b N hs hN
  have second := difference_distance y z s s _ zero D hd tail (GaussianRationalPowerDifference.distance_refl_zero s D hd)
  have thirdRaw := difference_distance z v s s (GaussianGammaDigammaInteger.budget N) zero T hp (prefix_error p N)
    (GaussianRationalPowerDifference.distance_refl_zero s T hp)
  have law : Γ ⊢[PRAAx] qsub v s ≐ u := GaussianRationalSumAlgebra.qadd_associative h (harmonicPoint N) (GaussianRationalMetric.qnegative s)
  have third := lift (qsub z s) u (GaussianGammaDigammaInteger.budget N)
    (distance_congr (.eqRefl _) law (by ipra_ring) (.eqRefl _) thirdRaw)
  have forthRaw := GaussianNameRingLaws.add_sample_error negativeGammaF constantF negativeGammaData (partialValue a b N) p
    (negativeGamma_regular (Γ := Γ)) (constant_regular _)
  have forth := lift u (ap2 nameF p (data a b N)) three
    (distance_symmetric _ _ _ _ hp
      (distance_congr (.eqRefl _) (qadd_congr (.eqRefl _) (constant_at _ _)) (.eqRefl _) (.eqRefl _) forthRaw))
  have d := distance_triangle_same _ _ _ _ _ _ hd (distance_triangle_same _ _ _ _ _ _ hd
    (distance_triangle_same _ _ _ _ _ _ hd first second) third) forth
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by unfold budget three GaussianGammaDigammaInteger.budget GaussianNamedLipschitzRate.diagonalNumerator; ipra_ring)
    (.eqRefl _) d

theorem original_rate (a b N : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] independentRate DF nameF (dd a b) (data a b N) a N := by
  apply GaussianNamedLipschitzRate.independent_rate DF nameF _ _ a N (budget a N) hN
    (GaussianGammaDigammaNative.name_regular a b hs) (name_regular a b N)
  refine .allI ?_
  have hh : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift a) (Syn.shift b) := by simpa [Fm.shift,Syn.shift] using hs.shift
  have hn : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hN.shift
  simpa only [GaussianNamedLipschitzRate.diagonalEnvelope,Syn.shift,GaussianGammaDigammaNative.subst_data,
    subst_data,subst_budget] using sample_error (var 0) (Syn.shift a) (Syn.shift b) (Syn.shift N) hh hn

theorem actual_original_positive_rational_digamma_series_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) ⟶ le one (var 2) ⟶
      independentRate DF nameF (dd (var 0) (var 1)) (data (var 0) (var 1) (var 2)) (var 0) (var 2)) :=
  closeUniv 3 (.impI (.impI (original_rate _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaSeries
