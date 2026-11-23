import IPRADerivations.Core.Tactic

/-!
# Proposed ProveIt object-language targets for the four-square theorem

STATUS: UNCOMPILED SOURCE OUTLINE.

This file is intended for the ProveIt root Lake workspace at commit
3a521d0265941f9e9d4ad450818365a78a6c9a73 (Lean 4.32.0).
It was NOT compiled in the present packet. The Euler-identity proof script is a
proposed adaptation of a source-inspected ProveIt proof pattern, not a fresh
kernel-check receipt. No proof of the full four-square object sentence is
asserted or postulated here.

The final goals below are defined as propositions. They are not axioms,
opaque constants, declarations with missing proofs, or completed theorems.

Inspected interfaces:
* ConciseIPRA/Syntax.lean, blob a3c8ec9700382e34df9ffdeaa2f2066bbfaf1348:
  Fm.all and Fm.ex bind index 0; other free indices are shifted upward.
* ConciseIPRA/PR.lean, blob 3251631592070d9ed3687cc0bf7dbd5eb452e46f:
  PR, PTm, PRAAx.
* ConciseIPRA/Deduction.lean, blob 0969040f77fdd3ed9526e360e7a998584b4d9d8c:
  Prf, Prf.allI, Prf.exI.
* IPRADerivations/Core/Tactic.lean,
  blob f303f4b70537110ccafae184c3fa552d522377a0:
  univ, closeUniv, ZT.var2, ipra_ring.
* IPRADerivations/DiophantineNumberTheory/Pell.lean,
  blob 50dec3e87ae23ad004e681412fb290cb8543d899:
  source-inspected example of closeUniv followed by ipra_ring.

All source paths above are relative to the corresponding ProveIt Lean roots.
Upstream code is licensed MIT-0 (see the packet's source provenance).
-/

namespace LeanProofs.IPRA.FourSquaresTarget

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm

/-! ## The exact existential object sentence -/

/-- A natural square is multiplication of a term by itself. -/
def natSquare {k : ℕ} (t : PTm k) : PTm k := t * t

/-- Four natural squares, with an explicitly fixed association. -/
def natSquareSum {k : ℕ} (a b c d : PTm k) : PTm k :=
  ((natSquare a + natSquare b) + natSquare c) + natSquare d

/--
The innermost matrix for "forall n, exists a b c d, n = a^2+b^2+c^2+d^2".

Inside all five binders the de Bruijn indices are:
  0 = d, 1 = c, 2 = b, 3 = a, 4 = n.
The newest (innermost) binder always has index 0.
-/
def fourSquareMatrix : Fm PTm 5 :=
  (var 4 : PTm 5) ≐
    natSquareSum (var 3) (var 2) (var 1) (var 0)

/--
Exact closed first-order iPRA sentence.
The outer binder is universal (n); the four inner binders are existential
(a, b, c, d, in that order).
-/
def fourSquareSentence : Fm PTm 0 :=
  Fm.all (Fm.ex (Fm.ex (Fm.ex (Fm.ex fourSquareMatrix))))

/--
The required object proof type. This merely defines a proposition;
it neither assumes nor supplies an inhabitant.
-/
def FourSquareObjectGoal : Prop :=
  ([] : List (Fm PTm 0)) ⊢[PRAAx] fourSquareSentence

/-! ## Stronger target with primitive recursive witnesses -/

/--
Apply one unary PR symbol to the sole free variable n.
The family W is a parameter of this interface, not a postulated witness.
-/
def witnessTerm (W : Fin 4 → PR 1) (i : Fin 4) : PTm 1 :=
  PTm.app (W i) (fun _ => (var 0 : PTm 1))

/-- Quantifier-free matrix asserting the correctness of four fixed PR symbols. -/
def witnessMatrix (W : Fin 4 → PR 1) : Fm PTm 1 :=
  (var 0 : PTm 1) ≐
    natSquareSum (witnessTerm W 0) (witnessTerm W 1)
      (witnessTerm W 2) (witnessTerm W 3)

/-- Universal closure of the witnessed identity. -/
def witnessSentence (W : Fin 4 → PR 1) : Fm PTm 0 :=
  Fm.all (witnessMatrix W)

/--
A stronger proposed object goal, for a concretely compiled family W.
Defining this proposition does not assert that any W satisfies it.
-/
def WitnessObjectGoal (W : Fin 4 → PR 1) : Prop :=
  ([] : List (Fm PTm 0)) ⊢[PRAAx] witnessSentence W

/-!
Completion plan for these goals:

1. Construct the four unary symbols W using PR.zero, PR.succ, PR.proj,
   PR.comp and PR.prec, or the inspected Core.Definitions/Pairing/Search
   compilers. The report supplies bounded algorithms and their QF invariants.
2. Build an actual Prf PRAAx derivation of witnessMatrix W from no assumptions.
   Each loop invariant must be represented by a QF formula or a PR Boolean
   checker equation; do not invoke unrestricted induction on an existential.
3. Close the sole free variable with Prf.allI.
4. For fourSquareSentence, open the universal binder, introduce the four
   explicit terms by Prf.exI, and close n with Prf.allI. The de Bruijn order in
   fourSquareMatrix is fixed above and must be preserved during substitution.

No theorem implementing steps 1-4 is included in this uncompiled target file.
-/

/-! ## Euler's polynomial identity as an object formula -/

/--
Eight signed integer coordinates are represented by sixteen natural variables.
ZT stores differences; it does not demand a canonical sign encoding.
-/
abbrev x0 : ZT 16 := .var2 0 1
abbrev x1 : ZT 16 := .var2 2 3
abbrev x2 : ZT 16 := .var2 4 5
abbrev x3 : ZT 16 := .var2 6 7
abbrev y0 : ZT 16 := .var2 8 9
abbrev y1 : ZT 16 := .var2 10 11
abbrev y2 : ZT 16 := .var2 12 13
abbrev y3 : ZT 16 := .var2 14 15

/--
Euler's four-square identity, in the dot-product / alternating-product form
used for descent. ZT.eq expands to a natural-number equation, so the matrix
is quantifier free.
-/
def eulerMatrix : Fm PTm 16 :=
  ZT.eq
    (((ZT.sq (x0 * y0 + x1 * y1 + x2 * y2 + x3 * y3) +
       ZT.sq (x1 * y0 - x0 * y1 - x2 * y3 + x3 * y2)) +
       ZT.sq (x2 * y0 - x0 * y2 + x1 * y3 - x3 * y1)) +
       ZT.sq (x3 * y0 - x0 * y3 - x1 * y2 + x2 * y1))
    (((ZT.sq x0 + ZT.sq x1) + ZT.sq x2 + ZT.sq x3) *
     ((ZT.sq y0 + ZT.sq y1) + ZT.sq y2 + ZT.sq y3))

/--
PROPOSED, UNCOMPILED proof fragment for the polynomial identity only.

ipra_ring first uses ZT.derive to reduce the object equation to an equality
in the commutative ring of differences of the quotient of terms by provable
equality; its ring proof is then reflected into an actual PRAAx derivation.
This source-level construction does not assume arbitrary semantic reflection.
It follows the inspected pattern of Pell.brahmagupta.
-/
theorem eulerIdentity_proposed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 16 eulerMatrix :=
  closeUniv 16 (by
    unfold eulerMatrix x0 x1 x2 x3 y0 y1 y2 y3
    ipra_ring)

/-!
Next object-level modules still to implement and compile:
* injectivity of small squares modulo an odd prime and the bounded seed;
* parity pairing and exact halving;
* centered remainder bounds and the odd-multiplier descent step;
* the invariant and explicit clock of the absorbing descent;
* bounded least-prime-factor extraction and assembly for arbitrary n;
* the final witnessed identity and existential packaging.

The above proposed identity fragment is only one algebraic component.
It is not a formalization of those remaining steps.
-/

end LeanProofs.IPRA.FourSquaresTarget

