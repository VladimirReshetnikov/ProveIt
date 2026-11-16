import IPRADerivations.Core.Search
import IPRADerivations.Core.Pairing
import IPRADerivations.Core.MultiSums
import IPRADerivations.Core.Integers
import IPRADerivations.Core.Powers
import FIBER.Kernel

/-!
# FIBER implementation blueprint

This file fixes names and theorem shapes.  It is not a completed Lean module and
is not claimed to compile.  Unfinished results are kept as comments rather than
as `sorry` or new axioms.  The dependency-ordered implementation path is in
`lean/FORMALIZATION_PLAN.md`.
-/

namespace LeanProofs.IPRA.FIBER

open LeanProofs.ConciseIPRA
open LeanProofs.IPRA
open Syn
open scoped Fm

/-- Metalevel syntax for a fixed bounded formula.  A full implementation should
compile this syntax to a primitive-recursive bit and a `Prf PRAAx` reflection
proof. -/
inductive BFm (n : ℕ)
  | eq   : PTm n → PTm n → BFm n
  | lt   : PTm n → PTm n → BFm n
  | and  : BFm n → BFm n → BFm n
  | or   : BFm n → BFm n → BFm n
  | imp  : BFm n → BFm n → BFm n
  | bEx  : PTm n → BFm (n + 1) → BFm n
  | bAll : PTm n → BFm (n + 1) → BFm n

/-- Host metadata for a fixed query interface.  The proof fields in a completed
version must be literal object derivations, not semantic theorems about Nat. -/
structure Interface where
  arity      : ℕ
  queryOK    : PR (arity + 1)
  certBound  : PR (arity + 1)
  verifier   : PR (arity + 2)
  observe    : PR (arity + 2)
  validFm    : Fm PTm (arity + 2)
  soundFm    : Fm PTm (arity + 2)
  sound      : ([] : List (Fm PTm (arity + 2))) ⊢[PRAAx] soundFm

/-- Escape policy of a finite witness. -/
inductive EscapeClass
  | local
  | observational
  | canonical
  | residual
  deriving DecidableEq, Repr

/-- A finite source graph.  Arithmetic proof-bearing constructors should be
added only after the small kernel modules are checked. -/
inductive Program
  | primitive (name : String)
  | pair (left right : Program)
  | call (callee : String) (query : Program)
  | localExists (body : Program)
  | reflectedCase (test yes no : Program)
  | boundedLoop (fuel : Program) (body : Program)
  | leastSearch (bound verifier : Program)
  | observe (body : Program) (escape : EscapeClass)
  | requireResidual (name : String) (body : Program)
  deriving Repr

/-!
## Required theorem targets

The exact formulas depend on the canonical Boolean and sequence libraries.
They should be implemented in this order:

* `BFm.toFm`, `BFm.bit`, and
  `BFm.reflect (A) : [] ⊢[PRAAx] (A.bit ≐ 1) 🡘 A.toFm`;
* a one-success wrapper over `Search.search_found` and `search_minimal`;
* bounded sequence append/lookup and a master-certificate theorem;
* fixed-arity finite monotone demand closure;
* bounded strategy realization;
* `compile : WellFormed P → Compiled P`, where `Compiled.sound` is a
  `Prf PRAAx` value;
* dyadic adjacent-motion and finite-net examples.

No universal primitive-recursive evaluator is to be introduced.  Source
programs are specialized at the metalevel to fixed `PR` terms and proof terms.
-/

end LeanProofs.IPRA.FIBER
