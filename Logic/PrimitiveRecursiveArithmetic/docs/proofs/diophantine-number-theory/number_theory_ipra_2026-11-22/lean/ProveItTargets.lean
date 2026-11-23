/-
Object-level target construction for the pinned ProveIt snapshot.
STATUS: not compiled here; requires ProveIt at the revision in provenance.json.
This file defines exact sentences and proof obligations; it does not supply
the missing number-theoretic proof terms. In particular, a field in
RequiredDerivations is an obligation, not a new object-theory axiom.
-/
import IPRADerivations.Core.Definitions
import IPRADerivations.Foundations.BoundedSyntax

namespace NumberTheoryIPRA.ObjectTargets

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.BoundedSyntax
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ app)

/-- A fixed primitive recursive tuple of four witnesses. -/
def fourSquaresBody (w : Fin 4 → PR 1) : Fm PTm 1 :=
  let x : PTm 1 := var 0
  let a := app (w 0) ![x]
  let b := app (w 1) ![x]
  let c := app (w 2) ![x]
  let d := app (w 3) ![x]
  a * a + b * b + c * c + d * d ≐ x

def fourSquaresSentence (w : Fin 4 → PR 1) : Fm PTm 0 :=
  Fm.all (fourSquaresBody w)

/-- Valid is a fixed Boolean code for D >= 2 and nonsquare.
    X,Y are fixed numerical witness functions constructed from the Pell bound. -/
def pellBody (valid X Y : PR 1) : Fm PTm 1 :=
  let D : PTm 1 := var 0
  let x := app X ![D]
  let y := app Y ![D]
  (app valid ![D] ≐ succ zero) ⟶
    ((x * x ≐ succ (D * (y * y))) ⋏ lt zero y)

def pellSentence (valid X Y : PR 1) : Fm PTm 0 :=
  Fm.all (pellBody valid X Y)

/-- The pinned repository already supplies the bounded Boolean compiler.
    Re-export its actual proof, without postulating a reflection axiom. -/
theorem boundedReflection {n : Nat} (A : BFm n) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx]
      univ n (Fm.iff (app (bitF A) var ≐ one) (formula A)) :=
  boolean_reflection_closed A

structure RequiredDerivations (w : Fin 4 → PR 1) (valid X Y : PR 1) : Prop where
  fourSquares : ([] : List (Fm PTm 0)) ⊢[PRAAx] fourSquaresSentence w
  pell : ([] : List (Fm PTm 0)) ⊢[PRAAx] pellSentence valid X Y

/- Completion requirements:
1. Instantiate w, valid, X, Y by PR codes for the displayed bounded algorithms.
2. Prove their defining equations and validity-bit reflection, using bitF.
3. Compile the norm/descent/collision invariants, then use PRA.qfInd.
4. Build RequiredDerivations with actual proof terms and no extra object axioms.
5. Audit public endpoint types and #print axioms in the selected checkout.

The ambient semantic specifications in the other files are not sufficient
to construct RequiredDerivations by a soundness theorem in reverse.
-/

end NumberTheoryIPRA.ObjectTargets
