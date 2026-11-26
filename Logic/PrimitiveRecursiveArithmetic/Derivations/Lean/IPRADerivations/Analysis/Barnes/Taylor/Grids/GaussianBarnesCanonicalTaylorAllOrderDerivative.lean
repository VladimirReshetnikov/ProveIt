import IPRADerivations.Analysis.Barnes.Taylor.Grids.GaussianBarnesCanonicalTaylorDerivativeBase
import IPRADerivations.Analysis.Barnes.Taylor.Grids.GaussianBarnesCanonicalTaylorDerivativeSuccessor

/-!
# The derivative operation at every retained order

A single step modulus pays for either order zero or a positive encoded
order. The exact next factorial Taylor name then approximates the original
named difference quotient at every pair of observation clocks.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorAllOrderDerivative

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (add normSq)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianCoefficientNameBounds (unit)
open GaussianExponentialReference (unit_monotone)
open GaussianL1 (norm1)
open GaussianNamedInverseRate (independentRate)
open ConciseIPRA.PTm (succ zero)
open LeanProofs.IPRA.PTm (pred)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "Q" => GaussianBarnesCanonicalTaylorNamedQuotient.nameF
local notation "qd" => GaussianBarnesCanonicalTaylorNamedQuotient.data
local notation "F" => GaussianBarnesCanonicalTaylorProductDerivativeName.nameF
local notation "fd" => GaussianBarnesCanonicalTaylorProductDerivativeName.data
local notation "baseClock" => GaussianBarnesCanonicalTaylorDerivativeBase.stepClock
local notation "higherClock" => GaussianBarnesCanonicalTaylorDerivativeSuccessor.stepClock

def stepClock (p R e : PTm n) : PTm n := baseClock p R+higherClock p R (pred e) e

private theorem data_congr {x x' y y' A N : PTm n}
    (hx : Γ ⊢[PRAAx] x ≐ x') (hy : Γ ⊢[PRAAx] y ≐ y')
    (h : Γ ⊢[PRAAx] independentRate Q F x y A N) :
    Γ ⊢[PRAAx] independentRate Q F x' y' A N := by
  let φ : Fm PTm 4 := independentRate Q F (var 0) (var 1) (var 2) (var 3)
  let a : Fin 4 → PTm n := ![x,y,A,N]
  let b : Fin 4 → PTm n := ![x',y',A,N]
  have he : ∀ i, Γ ⊢[PRAAx] a i ≐ b i := by
    intro i
    fin_cases i
    · exact hx
    · exact hy
    · exact .eqRefl A
    · exact .eqRefl N
  have start : Γ ⊢[PRAAx] φ.subst a := by simpa [φ,a] using h
  simpa [φ,b] using Prf.eqSubst φ a b he start

theorem rate (p z h R B J e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source (add z h) R B) (hn : Γ ⊢[PRAAx] le one (normSq h))
    (he : Γ ⊢[PRAAx] le e (previous J))
    (hs : Γ ⊢[PRAAx] le (norm1 h*unit (stepClock p R e)) B) : Γ ⊢[PRAAx]
    independentRate Q F (qd z h R B J e) (fd z (R+one) B (pred e) (succ e)) one (unit p) := by
  let a := baseClock p R
  let b := higherClock p R (pred e) e
  have h₀ : Γ ⊢[PRAAx] le (norm1 h*unit a) B :=
    le_trans (le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right (norm1 h) (unit_monotone (le_add_right a b)))) hs
  have h₁ : Γ ⊢[PRAAx] le (norm1 h*unit b) B :=
    le_trans (le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right (norm1 h) (unit_monotone (le_add_left b a)))) hs
  refine .orE (lt_or_le zero e) ?_ ?_
  · exact GaussianBarnesCanonicalTaylorDerivativeSuccessor.positive_order_rate p z h R B J e
      hz.wk hw.wk hn.wk Prf.hyp0 he.wk h₁.wk
  · let Δ := le e zero :: Γ
    have ez : Δ ⊢[PRAAx] (zero : PTm n) ≐ e := le_antisymm (zero_le e) Prf.hyp0
    have base := GaussianBarnesCanonicalTaylorDerivativeBase.dyadic_rate (Γ := Δ) p z h R B J (pred zero)
      hz.wk hw.wk hn.wk h₀.wk
    have same_q : Δ ⊢[PRAAx] qd z h R B J zero ≐ qd z h R B J e := by
      ipra_congr (qd (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6)
        with [.eqRefl z, .eqRefl h, .eqRefl R, .eqRefl B, .eqRefl J, ez]
        using [one,LeanProofs.IPRA.Analysis.Products.fact,GaussianBarnesCanonicalTaylorNamedQuotient.data,
          GaussianBarnesCanonicalTaylorProductDerivativeName.data,GaussianBarnesCanonicalTaylorProductDerivativeName.coefficientData]
    have same_f : Δ ⊢[PRAAx] fd z (R+one) B (pred zero) one ≐ fd z (R+one) B (pred e) (succ e) := by
      ipra_congr (fd (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
        with [.eqRefl z, .eqRefl (R+one), .eqRefl B, congrPred ez, congrSucc ez]
        using [one,LeanProofs.IPRA.Analysis.Products.fact,
          GaussianBarnesCanonicalTaylorProductDerivativeName.data,GaussianBarnesCanonicalTaylorProductDerivativeName.coefficientData]
    exact data_congr same_q same_f base

theorem actual_Barnes_all_retained_factorial_Taylor_derivatives_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (let p := var 0
     let z := var 1
     let h := var 2
     let R := var 3
     let B := var 4
     let J := var 5
     let e := var 6
     (source z R B ⋏ source (add z h) R B ⋏ le one (normSq h)) ⟶
       le e (previous J) ⟶ le (norm1 h*unit (stepClock p R e)) B ⟶
       independentRate Q F (qd z h R B J e) (fd z (R+one) B (pred e) (succ e)) one (unit p)) :=
  closeUniv 7 (.impI (.impI (.impI (rate _ _ _ _ _ _ _
    Prf.hyp1.wk.andE₁ Prf.hyp1.wk.andE₂.andE₁ Prf.hyp1.wk.andE₂.andE₂ Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorAllOrderDerivative
