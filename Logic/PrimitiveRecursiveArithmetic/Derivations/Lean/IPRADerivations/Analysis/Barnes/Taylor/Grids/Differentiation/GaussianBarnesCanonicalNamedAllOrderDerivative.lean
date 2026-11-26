import IPRADerivations.Analysis.Barnes.Names.GaussianBarnesCanonicalNamedFactorialTaylorIncrementEndpoints
import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.GaussianBarnesCanonicalNamedIncrementDerivative
import IPRADerivations.Analysis.Barnes.Taylor.Grids.Differentiation.GaussianBarnesCanonicalFiniteTaylorAllOrderDerivative

/-!
# Adjacent Barnes factorial derivatives along regular Gaussian steps

At every encoded order, compare the actual named difference quotient
with its synchronous rational chart. A certificate of apartness controls
the readback clock, while the small-step modulus depends only on the
disk, order, and demanded output precision.
-/

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedAllOrderDerivative

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (add bounded_mono)
open GaussianBarnesCanonicalNamedDemand (source)
open GaussianBarnesCanonicalNamedFrozen (source_widen)
open GaussianBarnesCanonicalNamedFactorialTaylor (clock retains regular)
open GaussianBarnesCanonicalNamedFactorialTaylorIncrementEndpoints (base_rate rates)
open GaussianBarnesCanonicalNamedIncrementDerivative (stepSamples step_at step_source)
open GaussianBarnesCanonicalNamedIncrementEndpoints (nativeClock native_clock_later observation shifted_source chart_sources)
open GaussianBarnesCanonicalFiniteTaylorAllOrderDerivative (canonical_retention)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianFastValueCut (exponent)
open GaussianL1 (norm1)
open GaussianNameArithmetic (addF addData)
open GaussianNameEquivalence (cross_refl cross_symm)
open GaussianNamedIncrementChart (baseNumerator stepNumerator denominator step_separated step_small)
open GaussianNamedIncrementQuotientFrozenRate (commonNumerator common_precision_rate differenceCap late_separated)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedRateComposition (same_denominator symmetric)
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (pred)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "C" => GaussianBarnesCanonicalNamedFactorialTaylor.nameF
local notation "cd" => GaussianBarnesCanonicalNamedFactorialTaylor.data
local notation "F" => GaussianBarnesCanonicalTaylorProductDerivativeName.nameF
local notation "fd" => GaussianBarnesCanonicalTaylorProductDerivativeName.data
local notation "Q" => GaussianBarnesCanonicalTaylorNamedQuotient.nameF
local notation "qd" => GaussianBarnesCanonicalTaylorNamedQuotient.data
local notation "Qn" => GaussianNamedIncrementDifferenceQuotient.nameF
local notation "qnd" => GaussianNamedIncrementDifferenceQuotient.data
local notation "rationalClock" => GaussianBarnesCanonicalTaylorAllOrderDerivative.stepClock
local notation "disk" => GaussianBarnesCanonicalLogCofinal.source

def stepClock (p R e : PTm n) : PTm n := succ (rationalClock (p+two) (R+one) e)

def input (L K : PR 2) (p x y R a e : PTm n) : Fm PTm n :=
  source L x R ⋏ (GaussianNameReciprocal.input K a y ⋏ stepSamples K y (unit (stepClock p R e)))

def nameF (L K : PR 2) : PR 2 := Qn (C (addF L K)) (C L) K

def data (L K : PR 2) (x y R a e : PTm n) : PTm n :=
  qnd (C (addF L K)) (C L) K (cd (addData x y) (R+one) e) (cd x (R+one) e) y a

private theorem widen (z R B : PTm n) (hz : Γ ⊢[PRAAx] disk z R B) :
    Γ ⊢[PRAAx] disk z (R+one) B :=
  .andI hz.andE₁ (bounded_mono hz.andE₂ (le_of_eq_add (d := B) (by ipra_ring)))

private theorem chart_step (L K : PR 2) (p k x y R e : PTm n)
    (hs : Γ ⊢[PRAAx] stepSamples K y (unit (stepClock p R e))) :
    Γ ⊢[PRAAx] le
      (norm1 (stepNumerator (observation L k x) (observation K k y))*unit (rationalClock (p+two) (R+one) e))
      (denominator (observation L k x) (observation K k y)) := by
  let q := observation L k x
  let r := observation K k y
  let s := rationalClock (p+two) (R+one) e
  have pay : Γ ⊢[PRAAx] le (two*unit s*one) (unit (stepClock p R e)) :=
    le_congr (by ipra_ring : Γ ⊢[PRAAx] unit s*two ≐ two*unit s*one)
      (pw_succ two s).eqSymm (le_refl (unit s*two))
  exact le_congr (mul_comm _ _) (.eqRefl _)
    (step_small q r one _ (unit s) (unit_positive _) (step_at K y _ (nativeClock k) hs) pay)

private theorem finish_budget (p : PTm n) : Γ ⊢[PRAAx]
    le ((one+one+one)*unit p) (one*unit (p+two)) := by
  have scale : Γ ⊢[PRAAx] unit (p+two) ≐ unit p*(two*two) :=
    (pw_add two p two).eqTrans (congrMul (.eqRefl _) ((pw_succ two one).eqTrans (congrMul (pw_one two) (.eqRefl _))))
  exact le_congr (.eqRefl _) (congrMul (.eqRefl one) scale).eqSymm
    (le_of_eq_add (d := unit p) (by ipra_ring))

theorem rate (L K : PR 2) (p x y R a e : PTm n) (hi : Γ ⊢[PRAAx] input L K p x y R a e) :
    Γ ⊢[PRAAx] independentRate (nameF L K) (C L) (data L K x y R a e) (cd x (R+one) (succ e)) one (unit p) := by
  let S := R+one
  let L₀ := C L
  let L₁ := C (addF L K)
  let x₀ := cd x S e
  let x₁ := cd (addData x y) S e
  let E := commonNumerator a one one (differenceCap L₁ L₀ x₁ x₀)
  let s := p+two
  let U := unit s
  let t := exponent E s
  let d := clock t S e
  let c := clock s S (succ e)
  let b := GaussianNameReciprocal.anchor a
  let k := d+c+(b+t)
  let j := nativeClock k
  let q := observation L k x
  let r := observation K k y
  let z := baseNumerator q r
  let h := stepNumerator q r
  let B := denominator q r
  let u := fd (add z h) (S+one) B e e
  let v := fd z (S+one) B e e
  let w := fd z (S+one) B (pred e) (succ e)
  let named := cd x S (succ e)
  have hl := hi.andE₁
  have ha := hi.andE₂.andE₁
  have hs := hi.andE₂.andE₂
  have hU := unit_positive (Γ := Γ) s
  have step := step_source K y _ (unit_positive (stepClock p R e)) ha.andE₁ hs
  have hbase := source_widen L x R S hl (le_add_right R one)
  have hshift := shifted_source L K x y R hl step
  have hd : Γ ⊢[PRAAx] le d k := le_trans (le_add_right _ _) (le_add_right _ _)
  have hc : Γ ⊢[PRAAx] le c k := le_trans (le_add_left _ _) (le_add_right _ _)
  have ht : Γ ⊢[PRAAx] le t j := le_trans (le_add_left _ _) (le_trans (le_add_left _ _) (native_clock_later k))
  have hb : Γ ⊢[PRAAx] le b j := le_trans (le_add_right _ _) (le_trans (le_add_left _ _) (native_clock_later k))
  have ends := rates L K t k x y R e hl step hd
  have chart := chart_sources L K k x y R hl step
  have h₀ := widen z S B chart.andE₁
  have h₁ := widen (add z h) S B chart.andE₂
  have ru := GaussianBarnesCanonicalTaylorProductDerivativeName.regular _ _ _ _ _ h₁ (retains e)
  have rv := GaussianBarnesCanonicalTaylorProductDerivativeName.regular _ _ _ _ _ h₀ (retains e)
  have sep := step_separated q r (late_separated K a y j ha hb).andE₂
  have raw := GaussianBarnesCanonicalTaylorAllOrderDerivative.rate s z h S B e e
    chart.andE₁ chart.andE₂ sep.andE₂ (retains e) (chart_step L K p k x y R e hs)
  have rl := regular (addF L K) (addData x y) S e hshift
  have rr := regular L x S e hbase
  have compared := common_precision_rate L₁ L₀ F F K x₁ x₀ u v y a j t one one
    (.andI rl (.andI rr ha)) ru rv hb ht ends.andE₁ ends.andE₂
  have shrunk := GaussianEulerNamedPowerScalingPowerFrozen.unit_rate_after _ _ _ _ E t s (le_refl _) compared
  have nativeEq := GaussianBarnesCanonicalNamedIncrementEndpoints.native_quotient_data_equal (Γ := Γ) L K F F k x y u v
  have qr := GaussianBarnesCanonicalTaylorNamedQuotient.regular z h S B e e chart.andE₁ chart.andE₂ sep.andE₂ (retains e)
  have qreg := GaussianNamedIncrementDifferenceQuotient.name_regular L₁ L₀ K x₁ x₀ y a (.andI rl (.andI rr ha))
  have first := GaussianNamedRateTransport.transport _ _ _ _ _ _ _ _ _ _ hU shrunk
    (cross_refl _ _ qreg)
    (GaussianGammaCompactCutoffAlignment.cross_data_congr Q Q (qd z h S B e e) (qd z h S B e e) (qd z h S B e e) _
      (.eqRefl _) nativeEq.eqSymm (cross_refl _ _ qr))
  have retarget := GaussianBarnesCanonicalTaylorDerivativeOrderInvariance.cofinal_cross z (S+one) B (pred e) (succ e)
    (succ e) h₀ (canonical_retention e) (retains (succ e))
  have target := base_rate L K s k x y R (succ e) hl hc
  have last := GaussianNamedRateTransport.transport (C L) F (C L) F named _ named w one U hU target
    (cross_refl _ _ (regular L x S (succ e) hbase)) retarget
  have joined := same_denominator (nameF L K) Q F (data L K x y R a e) (qd z h S B e e) w one U one hU first raw
  have complete := same_denominator (nameF L K) F (C L) (data L K x y R a e) w named (one+one) U one hU joined
    (symmetric (C L) F named w one U hU last)
  exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ hU (unit_positive p) (finish_budget p) complete

theorem actual_Barnes_all_order_named_increment_derivative_closed (L K : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (let p := var 0
       let x := var 1
       let y := var 2
       let R := var 3
       let a := var 4
       let e := var 5
       input L K p x y R a e ⟶
         independentRate (nameF L K) (C L) (data L K x y R a e) (cd x (R+one) (succ e)) one (unit p)) :=
  closeUniv 6 (.impI (rate L K _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedAllOrderDerivative
