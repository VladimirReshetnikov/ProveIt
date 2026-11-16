import KIFCR.KernelCore
import IPRADerivations.Core.Pairing

/-!
# Packed trace blueprint

A fixed finite control graph is lowered to one primitive recursion on a packed
state.  State components use checked pairing/projection equations.  The
program counter and every local invariant are Booleanized before induction.
-/

namespace LeanProofs.KIFCR

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm

structure TraceCertificate (n : ℕ) where
  pre : List (Fm PTm n)
  fuel : PTm n
  terminalState : PTm n
  terminalFormula : Fm PTm n
  loop : LoopCertificate n
  terminal : pre ⊢[PRAAx] terminalFormula

/-!
Generation steps:

1. Allocate a fixed program counter and right-nested-pair register state.
2. Generate a total transition term; the done state maps to itself.
3. Conjoin all local QF assertions guarded by program-counter equalities.
4. Prove base/step branches using the node-local derivations.
5. Compile the loop with `IPRA.ind`, instantiate at `fuel`, and project the
   terminal formula with checked `fst_pair`/`snd_pair` equations.

Nested source loops need not remain nested object inductions: their counters,
accumulators, and continuations are registers in the single transition.
-/

end LeanProofs.KIFCR
