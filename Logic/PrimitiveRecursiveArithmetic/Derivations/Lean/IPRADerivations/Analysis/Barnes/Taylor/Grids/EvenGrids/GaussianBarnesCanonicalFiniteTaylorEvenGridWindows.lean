import IPRADerivations.Analysis.Barnes.Taylor.Grids.MixedGrids.GaussianBarnesCanonicalFiniteTaylorMixedGridPolynomial
import IPRADerivations.Analysis.Barnes.Taylor.Grids.GaussianBarnesCanonicalCofinalTaylorGridReturn
import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalFiniteProperness

/-!
# Adjacent two-sided windows of the fixed Barnes grid

Translation preserves the exact codes of the forward windows. A
backward return can use a distinct signed numerator pair, and properness
of the same literal partial product bounds the resulting row error.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorEvenGridWindows

open_ipra
open ComplexLogarithmRemainder (add bounded normSq scale)
open GaussianBarnesCanonicalCofinalTaylorGridObservations (deadline node_source)
open GaussianBarnesCanonicalCofinalTaylorGridReturn (return_point_fraction_equal)
open GaussianBarnesCanonicalCofinalTaylorGridWindows (native_shift)
open GaussianBarnesCanonicalFiniteTaylorEvenGridComparison (observed)
open GaussianBarnesCanonicalFiniteTaylorGrid (literalData)
open GaussianBarnesCanonicalFiniteTaylorGridObservations (literal_at literalGrid)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianFastValueCut (query_budget)
open GaussianPolynomialForwardDifferenceGridError (rowBound)
open GaussianPolynomialForwardDifferenceGridEvenError (even_error observedDouble)
open GaussianPolynomialForwardDifferenceGridIncrement (slice slice_at)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRootAlgebra (equal equal_of_values re_add im_add re_neg im_neg normSq_equal)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (entry_congr)
open LeanProofs.IPRA.Foundations.SequenceEquality (sequence_equal)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "gneg" => ComplexLogarithmRemainder.neg
local notation "Value" => GaussianBarnesCanonicalValue.prefixF
local notation "literal" => GaussianBarnesCanonicalProduct.literalData

private theorem sequence_equal_from_entries (A C : PTm 2) (N x y : PTm n)
    (h : (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx]
      entry (Syn.shift (sequence A N x)) (var 0) ≐ entry (Syn.shift (sequence C N y)) (var 0)) :
    Γ ⊢[PRAAx] sequence A N x ≐ sequence C N y := by
  have atIndex : (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx]
      entry (sequence A (Syn.shift N) (Syn.shift x)) (var 0) ≐
        entry (sequence C (Syn.shift N) (Syn.shift y)) (var 0) := by simpa [Syn.shift] using h
  exact sequence_equal A C N x y (.allI (.impI
    ((sequence_decode A Prf.hyp0).eqSymm.eqTrans (atIndex.eqTrans (sequence_decode C Prf.hyp0)))))

theorem first_window (t z h R B r e : PTm n) :
    Γ ⊢[PRAAx] slice (literalGrid t z h R B r (succ e)) zero (succ e) ≐ literalGrid t z h R B r e := by
  apply sequence_equal_from_entries
  let s (a : PTm n) := Syn.shift a
  let j : PTm (n+1) := var 0
  let Δ := lt j (succ (s e)) :: Γ.map Fm.shift
  let W := literalGrid (s t) (s z) (s h) (s R) (s B) (s r) (succ (s e))
  have hj : Δ ⊢[PRAAx] lt j (succ (s e)) := Prf.hyp0
  have long := lt_of_lt_of_le hj (le_succ_self (succ (s e)))
  have small := (slice_at W zero (succ (s e)) j hj).eqTrans (entry_congr (.eqRefl W) (zero_add j))
  have right := literal_at (s t) (s z) (s h) (s R) (s B) (s r) (s e) j hj
  have left := literal_at (s t) (s z) (s h) (s R) (s B) (s r) (succ (s e)) j long
  change Δ ⊢[PRAAx] entry (s (slice (literalGrid t z h R B r (succ e)) zero (succ e))) j ≐
    entry (s (literalGrid t z h R B r e)) j
  simpa [s,j,Δ,W,Syn.shift] using small.eqTrans (left.eqTrans right.eqSymm)

theorem next_window (t z h R B r e : PTm n) :
    Γ ⊢[PRAAx] slice (literalGrid t z h R B r (succ e)) one (succ e) ≐ literalGrid t (add z h) h R B r e := by
  apply sequence_equal_from_entries
  let s (a : PTm n) := Syn.shift a
  let j : PTm (n+1) := var 0
  let Δ := lt j (succ (s e)) :: Γ.map Fm.shift
  let W := literalGrid (s t) (s z) (s h) (s R) (s B) (s r) (succ (s e))
  have hj : Δ ⊢[PRAAx] lt j (succ (s e)) := Prf.hyp0
  have long : Δ ⊢[PRAAx] lt (one+j) (succ (succ (s e))) :=
    le_congr (by ipra_ring) (.eqRefl _) ((succ_monus_succ _ _).eqTrans hj)
  have left := (slice_at W one (succ (s e)) j hj).eqTrans
    (literal_at (s t) (s z) (s h) (s R) (s B) (s r) (succ (s e)) (one+j) long)
  have right := literal_at (s t) (add (s z) (s h)) (s h) (s R) (s B) (s r) (s e) j hj
  have middle : Δ ⊢[PRAAx] ap2 Value (s t) (literalData (s z) (s h) (s R) (s B) (s r) (one+j)) ≐
      ap2 Value (s t) (literalData (add (s z) (s h)) (s h) (s R) (s B) (s r) j) := by
    ipra_congr (ap2 Value (var 0) (literal (var 1) (var 2) (var 3) (var 4)) : PTm 5)
      with [.eqRefl _, native_shift (s z) (s h) j, .eqRefl _, .eqRefl _, .eqRefl _] using [literalData]
  change Δ ⊢[PRAAx] entry (s (slice (literalGrid t z h R B r (succ e)) one (succ e))) j ≐
    entry (s (literalGrid t (add z h) h R B r e)) j
  simpa [s,j,Δ,W,Syn.shift,one] using left.eqTrans (middle.eqTrans right.eqSymm)

private def returnCenter (z h : PTm n) : PTm n := add (add z h) (gneg h)

private theorem return_node_equal (z h j : PTm n) :
    Γ ⊢[PRAAx] equal (add (returnCenter z h) (scale j (gneg h))) (add z (scale j (gneg h))) := by
  apply equal_of_values <;> simp only [returnCenter,re_add,im_add,re_neg,im_neg] <;> ring

theorem return_window_at (t u z h R B H r e j : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (hh : Γ ⊢[PRAAx] bounded h H) (hs : Γ ⊢[PRAAx] le (e*H) B)
    (hj : Γ ⊢[PRAAx] lt j (succ e)) :
    Γ ⊢[PRAAx] distanceBounded
      (entry (slice (literalGrid t (add z h) (gneg h) R B r (succ e)) one (succ e)) j)
      (entry (literalGrid u z (gneg h) R B r e) j)
      (unit t+unit u) (unit t*unit u) := by
  let a := add (returnCenter z h) (scale j (gneg h))
  let b := add z (scale j (gneg h))
  have step : Γ ⊢[PRAAx] bounded (gneg h) H :=
    le_congr (ComplexLogarithmRemainder.normSq_neg h).eqSymm (.eqRefl _) hh
  have range : Γ ⊢[PRAAx] le j e := (succ_monus_succ _ _).eqSymm.eqTrans hj
  have sb : Γ ⊢[PRAAx] source b (R+one) B := node_source z (gneg h) R B H e j hz step hs range
  have sa : Γ ⊢[PRAAx] source a (R+one) B :=
    .andI sb.andE₁ (le_congr (normSq_equal (return_node_equal z h j)).eqSymm (.eqRefl _) sb.andE₂)
  let cutoff := initial (R+one)+r
  have cross := GaussianBarnesCanonicalFiniteProperness.prefix_cross a b (R+one) (R+one) B B cutoff
    sa sb (return_point_fraction_equal z h B j hz.andE₁)
  have near := GaussianNameEquivalence.cross_at Value Value (literal a (R+one) B cutoff) (literal b (R+one) B cutoff) t u cross
  have fromWindow := (entry_congr (next_window (Γ := Γ) t (add z h) (gneg h) R B r e) (.eqRefl j)).eqTrans
    (literal_at t (returnCenter z h) (gneg h) R B r e j hj)
  exact distance_congr fromWindow.eqSymm (literal_at u z (gneg h) R B r e j hj).eqSymm (.eqRefl _) (.eqRefl _) near

theorem return_window_rows (t u z h R B H r e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hh : Γ ⊢[PRAAx] bounded h H) (hs : Γ ⊢[PRAAx] le (e*H) B) :
    Γ ⊢[PRAAx] rowBound (slice (literalGrid t (add z h) (gneg h) R B r (succ e)) one (succ e))
      (literalGrid u z (gneg h) R B r e) (succ e) (unit t+unit u) (unit t*unit u) := by
  refine .allI (.impI ?_)
  let s (a : PTm n) := Syn.shift a
  let j : PTm (n+1) := var 0
  let Δ := lt j (succ (s e)) :: Γ.map Fm.shift
  have hz' : Δ ⊢[PRAAx] source (s z) (s R) (s B) := by simpa [Δ,s,Fm.shift,Syn.shift] using hz.shift.wk
  have hh' : Δ ⊢[PRAAx] bounded (s h) (s H) := by simpa [Δ,s,Fm.shift,Syn.shift] using hh.shift.wk
  have hs' : Δ ⊢[PRAAx] le (s e*s H) (s B) := by simpa [Δ,s,Fm.shift,Syn.shift] using hs.shift.wk
  simpa [rowBound,Δ,s,j,Syn.shift,one] using
    return_window_at (s t) (s u) (s z) (s h) (s R) (s B) (s H) (s r) (s e) j hz' hh' hs' (Prf.hyp0 : Δ ⊢[PRAAx] _)

private theorem observed_double_congr {V W P Q e h : PTm n}
    (hV : Γ ⊢[PRAAx] V ≐ P) (hW : Γ ⊢[PRAAx] W ≐ Q) :
    Γ ⊢[PRAAx] observedDouble V W e h ≐ observedDouble P Q e h := by
  ipra_congr (observedDouble (var 0) (var 1) (var 2) (var 3) : PTm 4)
    with [hV,hW,.eqRefl e,.eqRefl h]

private theorem reflexive_rows (V L D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] rowBound V V L zero D := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift L) :: Γ.map Fm.shift
  have pos : Δ ⊢[PRAAx] le one (Syn.shift D) := by simpa [Δ,Fm.shift,Syn.shift] using hD.shift.wk
  simpa [Δ,rowBound,Syn.shift] using
    GaussianRationalPowerDifference.distance_refl_zero (entry (Syn.shift V) (var 0)) (Syn.shift D) pos

theorem shifted_equal (t z h R B r e : PTm n) :
    Γ ⊢[PRAAx] observedDouble
      (slice (literalGrid t z h R B r (succ e)) one (succ e))
      (slice (literalGrid t (add z h) (gneg h) R B r (succ e)) zero (succ e)) e (ofGaussian h B) ≐
      observed t (add z h) h R B r e :=
  observed_double_congr (next_window t z h R B r e) (first_window t (add z h) (gneg h) R B r e)

theorem centered_rate (p t z h R B H r e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hh : Γ ⊢[PRAAx] bounded h H) (hs : Γ ⊢[PRAAx] le (e*H) B) (hn : Γ ⊢[PRAAx] le one (normSq h))
    (ht : Γ ⊢[PRAAx] le (deadline p B e) t) :
    Γ ⊢[PRAAx] distanceBounded (observed t z h R B r e)
      (observedDouble (slice (literalGrid t z h R B r (succ e)) zero (succ e))
        (slice (literalGrid t (add z h) (gneg h) R B r (succ e)) one (succ e)) e (ofGaussian h B)) one (unit p) := by
  let V := slice (literalGrid t z h R B r (succ e)) zero (succ e)
  let W := slice (literalGrid t (add z h) (gneg h) R B r (succ e)) one (succ e)
  let U := literalGrid t z (gneg h) R B r e
  let T := unit t*unit t
  have hT : Γ ⊢[PRAAx] le one T := positive_product _ _ (unit_positive t) (unit_positive t)
  have raw := even_error V W V U e (ofGaussian h B) one B zero (unit t+unit t) T
    (le_refl one) hz.andE₁ (GaussianNamedDifferenceQuotient.parameter_lower h B (.andI hz.andE₁ hn)) hT
    (reflexive_rows V (succ e) T hT) (return_window_rows t t z h R B H r e hz hh hs)
  have actual : Γ ⊢[PRAAx] observedDouble V U e (ofGaussian h B) ≐ observed t z h R B r e :=
    observed_double_congr (first_window t z h R B r e) (.eqRefl U)
  have near : Γ ⊢[PRAAx] distanceBounded (observedDouble V W e (ofGaussian h B)) (observed t z h R B r e)
      (pw B e*(pw two e*(unit t+unit t))) T :=
    distance_congr (.eqRefl _) actual (by ipra_ring)
      ((congrMul (GaussianPolynomialPerturbation.one_power e) (.eqRefl T)).eqTrans (one_mul T)) raw
  have enough : Γ ⊢[PRAAx] le (num 3*(pw B e*pw two e)*unit p) (unit t) :=
    le_trans (query_budget _ _) (GaussianExponentialReference.unit_monotone ht)
  have twice : Γ ⊢[PRAAx] le (two*(pw B e*pw two e)*unit p) (unit t) :=
    le_trans (le_of_eq_add (d := (pw B e*pw two e)*unit p) (by ipra_ring)) enough
  have comparison : Γ ⊢[PRAAx] le ((pw B e*(pw two e*(unit t+unit t)))*unit p) (one*T) :=
    le_congr (by ipra_ring) (one_mul _).eqSymm (mul_le_mul_right (unit t) twice)
  exact distance_symmetric _ _ _ _ (unit_positive p)
    (distance_radius_mono _ _ _ _ _ _ hT (unit_positive p) comparison near)

theorem actual_Barnes_finite_even_windows_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
      (let p := var 0
       let t := var 1
       let z := var 2
       let h := var 3
       let R := var 4
       let B := var 5
       let H := var 6
       let r := var 7
       let e := var 8
       let V := literalGrid t z h R B r (succ e)
       let W := literalGrid t (add z h) (gneg h) R B r (succ e)
       let q := ofGaussian h B
       (observedDouble (slice V one (succ e)) (slice W zero (succ e)) e q ≐ observed t (add z h) h R B r e) ⋏
         ((source z R B ⋏ (bounded h H ⋏ (le (e*H) B ⋏ (le one (normSq h) ⋏ le (deadline p B e) t)))) ⟶
           distanceBounded (observed t z h R B r e)
             (observedDouble (slice V zero (succ e)) (slice W one (succ e)) e q) one (unit p))) :=
  closeUniv 9 (.andI (shifted_equal _ _ _ _ _ _ _) (.impI (centered_rate _ _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorEvenGridWindows
