import Std
import «FiniteCore»

/-!
# Analytic contracts for the Meijer G roadmap

The structures in this file package hypotheses.  They are not axioms: every
field must eventually be inhabited by a bounded checker together with a
`Prf PRAAx` proof of its soundness.  Keeping contracts as data prevents a host
proof from silently importing classical completeness or choice.
-/

namespace MeijerGIPRA

structure GammaContract where
  eval : QComplex → Nat → CBall
  recurrence : ∀ z p, BallEq (eval z (p + 4)) (eval z (p + 5)) p
  -- Replace the placeholder recurrence above by the actual z*Gamma(z)=Gamma(z+1)
  -- ball theorem after rational-complex addition/multiplication are implemented.

structure LogContract where
  eval : QComplex → BranchCert → Nat → CBall
  regular : ∀ z b p, BallEq (eval z b (p + 4)) (eval z b (p + 5)) p

structure ContourContract where
  cert : EvalCert
  poleClearance : PoleClearance
  verticalTail : Nat → Nat
  closingTail : Nat → Nat

structure MellinContract where
  leftCutoff : Nat → Nat
  rightCutoff : Nat → Nat
  frequencyCutoff : Nat → Nat
  mesh : Nat → Nat
  totalBudget : Nat → Nat

structure FubiniContract where
  xLow : Nat → Nat
  xHigh : Nat → Nat
  tHigh : Nat → Nat
  meshX : Nat → Nat
  meshT : Nat → Nat
  budgetOK : ∀ p,
    xLow p + xHigh p + tHigh p + meshX p + meshT p ≤ 2 ^ p

structure RationalPowerProductContract where
  exponentNum1 : Nat
  exponentDen1 : Nat
  exponentNum2 : Nat
  exponentDen2 : Nat
  exponentDen1Pos : 0 < exponentDen1
  exponentDen2Pos : 0 < exponentDen2
  mellin : MellinContract
  fubini : FubiniContract
  -- The object checker also stores the Gauss-expanded parameter blocks and
  -- verifies their affine list transformation exactly.

structure TransformPairContract where
  forward : QComplex → QComplex → Nat → CBall
  inverse : QComplex → QComplex → Nat → CBall
  mellin : MellinContract
  fubini : FubiniContract
  -- A completed object version additionally carries the finite multiplier
  -- identity and the test-function inversion modulus.

end MeijerGIPRA
