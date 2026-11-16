/-!
# Bounded-formula Booleanization: exact target interface

This is a blueprint, not a completed formalization.  It gives the intended
objects and theorem endpoints without declaring unfinished results as axioms.
After the term-to-symbol compiler from
`ipra_resources_and_elimination_2026-11-15` is integrated, the structures below
can be instantiated by structural recursion.
-/

import ConciseIPRA.PR

namespace LeanProofs.ConciseIPRA.PCOG

open Syn
open scoped Fm

/-- The formula saying that a fixed PR Boolean checker returns one. -/
def checked {n r : Nat} (b : PR r) (args : Fin r → PTm n) : Fm PTm n :=
  PTm.app b args ≐ PTm.succ PTm.zero

/-- A completed Booleanization theorem for one fixed formula.  The two fields
are embedded derivations, not host equivalences. -/
structure BoolReflection {n : Nat} (φ : Fm PTm n) where
  arity : Nat
  code : PR arity
  args : Fin arity → PTm n
  forward : [φ] ⊢[PRAAx] checked code args
  backward : [checked code args] ⊢[PRAAx] φ

/-- Syntax for fixed strictly bounded formulas.  Bounds and atomic predicates
are represented by already compiled PR symbols. -/
inductive BForm : Nat → Type
  | atom {n r : Nat} (test : PR r) (args : Fin r → PTm n) : BForm n
  | bot {n : Nat} : BForm n
  | and {n : Nat} : BForm n → BForm n → BForm n
  | or  {n : Nat} : BForm n → BForm n → BForm n
  | imp {n : Nat} : BForm n → BForm n → BForm n
  | allLt {n : Nat} (bound : PTm n) : BForm (n + 1) → BForm n
  | exLt  {n : Nat} (bound : PTm n) : BForm (n + 1) → BForm n

/-!
Completion targets, in dependency order:

1. `boolEq`, `boolAnd`, `boolOr`, `boolNot` as concrete `PR` symbols and their
   defining-equation proofs.
2. `allBelow` and `anyBelow` by primitive recursion on the bound.
3. Internal reflection lemmas proved by `PRA.qfInd`.
4. A host structural recursion

      compile : (φ : BForm n) →
        Σ ψ : Fm PTm n, BoolReflection ψ

   where bounded binders are translated to their Boolean fold equations.
5. `leastBelow` with an object proof of minimality and the no-witness branch.

The compiler is a host recursion on one *fixed* syntax tree.  It does not ask
for, and must not introduce, an object-level universal evaluator for encoded
primitive-recursive programs.
-/

end LeanProofs.ConciseIPRA.PCOG
