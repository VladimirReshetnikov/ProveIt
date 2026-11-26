import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalValueDerivative

/-!
# A common input precision for the original Barnes derivative quotient

The step may be represented with any positive native denominator. A
single dyadic upper bound on its size pays both the local Taylor guard
and the requested output precision, independently of the separate
certificate that the step is nonzero.
-/

set_option autoImplicit false
set_option maxHeartbeats 750000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDerivativeIncrementPrecision

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (add normSq oneCode)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial_positive)
open GaussianBarnesCanonicalValueDerivative
  (nameF data quotientF quotientData stepGain numerator denominator input_of_margin precision_rate)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianFastValueCut (exponent query_budget)
open GaussianL1 (norm1 norm1_one)
open GaussianNamedInverseRate (independentRate)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def gain (R : PTm n) : PTm n := two*(stepGain R+numerator R oneCode)
def inputClock (R p : PTm n) : PTm n := exponent (gain R) p

theorem numerator_factor (R h : PTm n) : Γ ⊢[PRAAx] numerator R h ≐ numerator R oneCode*norm1 h := by
  let C := GaussianBarnesCanonicalDiskBound.prefixBound R*(two*GaussianBarnesCanonicalTailExponentialDerivative.errorGain R)+
    GaussianBarnesCanonicalValueDerivativeJoin.tailDerivativeBound R*GaussianBarnesCanonicalValueDerivativeJoin.prefixGain R+
    GaussianBarnesCanonicalTailExponentialMargin.exponentialBound R*GaussianBarnesCanonicalPrefixDerivative.gain R
  change Γ ⊢[PRAAx] C*norm1 h ≐ (C*norm1 oneCode)*norm1 h
  have eq : Γ ⊢[PRAAx] C*norm1 oneCode ≐ C :=
    (congrMul (.eqRefl C) norm1_one).eqTrans (by ipra_ring)
  exact congrMul eq.eqSymm (.eqRefl _)

private theorem budget_product (h B K U : PTm n) (hU : Γ ⊢[PRAAx] le one U)
    (hs : Γ ⊢[PRAAx] le (norm1 h*U) (two*B)) (hb : Γ ⊢[PRAAx] le (two*K) U) :
    Γ ⊢[PRAAx] le (K*norm1 h) B := by
  apply RationalValueBounds.positive_cancel hU
  ipra_le 𝔞(K)*sl hs+𝔞(B)*sl hb

theorem rate (p z h R B : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source (add z h) R B) (hn : Γ ⊢[PRAAx] le one (normSq h))
    (hs : Γ ⊢[PRAAx] le (norm1 h*unit (inputClock R p)) (two*B)) :
    Γ ⊢[PRAAx] independentRate quotientF nameF (quotientData z h R B) (data z R B) one (unit p) := by
  let U := unit (inputClock R p)
  let A := numerator R oneCode
  let G := gain R
  have hU : Γ ⊢[PRAAx] le one U := unit_positive _
  have q : Γ ⊢[PRAAx] le (G*unit p) U := query_budget G p
  have step : Γ ⊢[PRAAx] le (two*stepGain R) G := by
    change Γ ⊢[PRAAx] le (two*stepGain R) (two*(stepGain R+A))
    ipra_le 2*𝔞(A)
  have err : Γ ⊢[PRAAx] le (two*A) G := by
    change Γ ⊢[PRAAx] le (two*A) (two*(stepGain R+A))
    ipra_le 2*𝔞(stepGain R)
  have gU : Γ ⊢[PRAAx] le G U :=
    le_trans (le_congr (one_mul G) (mul_comm _ _) (mul_le_mul_right G (unit_positive p))) q
  have b := budget_product h B (stepGain R) U hU hs (le_trans step gU)
  have c := budget_product h B (A*unit p) U hU hs
    (le_trans (le_congr (by ipra_ring) (.eqRefl _) (mul_le_mul_right (unit p) err)) q)
  have t : Γ ⊢[PRAAx] le (numerator R h*unit p) B :=
    le_congr ((by ipra_ring : Γ ⊢[PRAAx] A*unit p*norm1 h ≐ (A*norm1 h)*unit p).eqTrans
      (congrMul (numerator_factor R h).eqSymm (.eqRefl _))) (.eqRefl _) c
  have den : Γ ⊢[PRAAx] le B (denominator R B) :=
    le_congr (one_mul B) (mul_comm _ _) (mul_le_mul_right B (initial_positive R))
  exact precision_rate p z h R B (input_of_margin z h R B hz hw hn b) (le_trans t den)

theorem actual_Barnes_derivative_precision_from_small_step_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (let p := var 0
     let z := var 1
     let h := var 2
     let R := var 3
     let B := var 4
     (source z R B ⋏ (source (add z h) R B ⋏ (le one (normSq h) ⋏
       le (norm1 h*unit (inputClock R p)) (two*B)))) ⟶
       independentRate quotientF nameF (quotientData z h R B) (data z R B) one (unit p)) :=
  closeUniv 5 (.impI (rate _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDerivativeIncrementPrecision
