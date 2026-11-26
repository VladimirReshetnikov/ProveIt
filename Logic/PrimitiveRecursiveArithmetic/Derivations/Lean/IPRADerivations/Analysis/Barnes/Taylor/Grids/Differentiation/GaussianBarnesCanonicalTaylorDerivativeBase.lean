import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.GaussianBarnesCanonicalTaylorDerivativeZero
import IPRADerivations.Analysis.Barnes.Taylor.Grids.Differentiation.GaussianBarnesCanonicalTaylorFirstDerivativeAnchor
import IPRADerivations.Analysis.Barnes.Taylor.Grids.Differentiation.GaussianBarnesCanonicalTaylorNamedQuotient
import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.GaussianNamedDifferenceQuotientProperness

/-!
# The order-zero to order-one Barnes factorial derivative

The zero coefficient is the canonical value, and the first coefficient
is its previously verified named derivative. Transport the original
value difference-quotient theorem along those two identifications.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorDerivativeBase

open_ipra
open ComplexLogarithmRemainder (add bounded_mono normSq oneCode)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial initial_positive)
open GaussianBarnesCanonicalValueDerivative (input_of_margin stepGain numerator denominator)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianFastValueCut (exponent query_budget)
open GaussianL1 (norm1 norm1_one)
open GaussianNameEquivalence (cross_symm)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (positive_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "V" => GaussianBarnesCanonicalValue.nameF
local notation "vd" => GaussianBarnesCanonicalValue.data
local notation "D" => GaussianBarnesCanonicalValueDerivative.nameF
local notation "dd" => GaussianBarnesCanonicalValueDerivative.data
local notation "W" => GaussianBarnesCanonicalValueDerivative.quotientF
local notation "wd" => GaussianBarnesCanonicalValueDerivative.quotientData
local notation "F" => GaussianBarnesCanonicalTaylorProductDerivativeName.nameF
local notation "fd" => GaussianBarnesCanonicalTaylorProductDerivativeName.data
local notation "Q" => GaussianBarnesCanonicalTaylorNamedQuotient.nameF
local notation "qd" => GaussianBarnesCanonicalTaylorNamedQuotient.data

def gain (R : PTm n) : PTm n := numerator (R+one) oneCode

def stepCost (R : PTm n) : PTm n := stepGain (R+one)+gain R

def stepClock (p R : PTm n) : PTm n := exponent (stepCost R) p

private theorem widen (z R B : PTm n) (hz : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx] source z (R+one) B :=
  .andI hz.andE₁ (bounded_mono hz.andE₂ (le_of_eq_add (d := B) (by ipra_ring)))

private theorem numerator_linear (R h : PTm n) : Γ ⊢[PRAAx] numerator (R+one) h ≐ gain R*norm1 h := by
  unfold gain numerator GaussianBarnesCanonicalValueDerivativeJoin.numerator
  refine congrMul ?_ (.eqRefl (norm1 h))
  exact ((congrMul (.eqRefl _) norm1_one).eqTrans (Common.mul_one_right _)).eqSymm

theorem linear_rate (z h R B J K : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source (add z h) R B) (hn : Γ ⊢[PRAAx] le one (normSq h))
    (hs : Γ ⊢[PRAAx] le (stepGain (R+one)*norm1 h) B) : Γ ⊢[PRAAx]
    independentRate Q F (qd z h R B J zero) (fd z (R+one) B K one) (numerator (R+one) h) (denominator (R+one) B) := by
  let S := R+one
  let w := add z h
  have hzS := widen z R B hz
  have hwS := widen w R B hw
  have old := GaussianBarnesCanonicalValueDerivative.rate z h S B (input_of_margin z h S B hzS hwS hn hs)
  have qcross := GaussianNamedDifferenceQuotientProperness.proper F V F V (fd w S B J zero) (vd w S B)
    (fd z S B J zero) (vd z S B) h B
    (GaussianBarnesCanonicalTaylorProductDerivativeName.regular _ _ _ _ _ hwS (zero_le _))
    (GaussianBarnesCanonicalValue.regular w S B hwS)
    (GaussianBarnesCanonicalTaylorProductDerivativeName.regular _ _ _ _ _ hzS (zero_le _))
    (GaussianBarnesCanonicalValue.regular z S B hzS)
    (GaussianBarnesCanonicalTaylorDerivativeZero.value_cross w S B J hwS)
    (GaussianBarnesCanonicalTaylorDerivativeZero.value_cross z S B J hzS)
  have target := GaussianBarnesCanonicalTaylorFirstDerivativeAnchor.cross z R B K hz
  exact GaussianNamedRateTransport.transport W D Q F (wd z h S B) (dd z S B) (qd z h R B J zero)
    (fd z S B K one) _ _ (positive_product _ _ hz.andE₁ (initial_positive S)) old qcross target

theorem dyadic_rate (p z h R B J K : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source (add z h) R B) (hn : Γ ⊢[PRAAx] le one (normSq h))
    (hs : Γ ⊢[PRAAx] le (norm1 h*unit (stepClock p R)) B) : Γ ⊢[PRAAx]
    independentRate Q F (qd z h R B J zero) (fd z (R+one) B K one) one (unit p) := by
  let S := R+one
  let H := norm1 h
  let C := stepGain S
  let G := gain R
  let U := unit p
  let X := unit (stepClock p R)
  have hp : Γ ⊢[PRAAx] le ((C+G)*U) X := query_budget (C+G) p
  have fits : Γ ⊢[PRAAx] le (C*U) X := le_trans (mul_le_mul_right U (le_add_right C G)) hp
  have grow : Γ ⊢[PRAAx] le C (C*U) :=
    le_congr (one_mul C) (mul_comm U C) (mul_le_mul_right C (unit_positive p))
  have margin : Γ ⊢[PRAAx] le (C*H) B :=
    le_trans (le_congr (.eqRefl _) (mul_comm X H) (mul_le_mul_right H (le_trans grow fits))) hs
  have budget : Γ ⊢[PRAAx] le (G*U) X := le_trans (mul_le_mul_right U (le_add_left G C)) hp
  have small : Γ ⊢[PRAAx] le (numerator S h*U) B :=
    le_trans (le_congr ((congrMul (numerator_linear R h) (.eqRefl U)).eqTrans (by ipra_ring)).eqSymm
      (mul_comm X H) (mul_le_mul_right H budget)) hs
  have den : Γ ⊢[PRAAx] le B (denominator S B) :=
    le_congr (one_mul B) (mul_comm _ _) (mul_le_mul_right B (initial_positive S))
  exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ (positive_product _ _ hz.andE₁ (initial_positive S)) (unit_positive p)
    (le_congr (.eqRefl _) (one_mul _).eqSymm (le_trans small den)) (linear_rate z h R B J K hz hw hn margin)

theorem actual_Barnes_base_factorial_Taylor_derivative_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (let p := var 0
     let z := var 1
     let h := var 2
     let R := var 3
     let B := var 4
     let J := var 5
     let K := var 6
     (source z R B ⋏ source (add z h) R B ⋏ le one (normSq h)) ⟶ le (norm1 h*unit (stepClock p R)) B ⟶
       independentRate Q F (qd z h R B J zero) (fd z (R+one) B K one) one (unit p)) :=
  closeUniv 7 (.impI (.impI (dyadic_rate _ _ _ _ _ _ _
    Prf.hyp1.andE₁ Prf.hyp1.andE₂.andE₁ Prf.hyp1.andE₂.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorDerivativeBase
