import IPRADerivations.Core.Definitions
import PCFM.Core

/-!
# The low-level fixed-trace invariant wrapper

`InvariantSpec` deliberately matches `IPRA.ind`.  A higher-level constructor
will later generate this payload from a specialized run term and local state
invariant.
-/

namespace LeanProofs.IPRA.Framework

open LeanProofs.ConciseIPRA
open LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {k : ℕ}

/-- Exactly the four ingredients required by quantifier-free open induction. -/
structure InvariantSpec (k : ℕ) where
  inv : Fm PTm (k + 1)
  qf : inv.QF
  zeroProof :
    ([] : List (Fm PTm k)) ⊢[PRAAx] inv.subst (Syn.inst zero)
  succProof :
    [inv] ⊢[PRAAx] inv.subst (Syn.repl (succ (Syn.var 0)))

namespace InvariantSpec

/-- Compile the supplied base and step proofs with the checked induction rule. -/
def prove (S : InvariantSpec k) :
    ([] : List (Fm PTm (k + 1))) ⊢[PRAAx] S.inv :=
  IPRA.ind S.inv S.qf S.zeroProof S.succProof

/-- Package the compiled invariant as a proof-carrying module. -/
def toModule (S : InvariantSpec k) : Module (k + 1) :=
  Module.closed S.prove

end InvariantSpec

/-
Higher-level target:

structure TraceSpec (k : Nat) where
  base : PTm k
  step : PTm (k + 2)
  stateInv : Fm PTm (k + 1)
  stateInvQF : stateInv.QF
  baseProof : ...
  stepProof : ...

def TraceSpec.runSymbol : PR (k + 1) := recDef base step

def TraceSpec.toInvariantSpec : InvariantSpec k := ...

theorem TraceSpec.run_invariant (S : TraceSpec k) :
  [] |- [PRAAx] S.stateInv[ S.runSymbol(...) / state ]
-/

end LeanProofs.IPRA.Framework
