/-!
# Finite relational clouds and backward viability: formalization blueprint

No unfinished proposition is asserted.  The comments record concrete target
signatures and the intended object-iPRA induction invariant.
-/

import ConciseIPRA.PR

namespace LeanProofs.ConciseIPRA.PCOG

open Syn
open scoped Fm

/-- Fixed primitive-recursive interface for a finite cloud tower.

`bound(level, parameters)` bounds candidate codes;
`valid(level, candidate, parameters)` and
`edge(level, candidate, next, parameters)` are Boolean PR predicates.
All arities are kept explicit in the eventual integrated module. -/
structure CloudSymbols where
  parameterArity : Nat
  bound : PR (parameterArity + 1)
  valid : PR (parameterArity + 2)
  edge  : PR (parameterArity + 3)

/-!
Target construction.

For a supplied finite horizon `h`, define by primitive recursion a table

  W(h,i,a) = valid(i,a) ∧
             (i=h ∨ ∃ b < bound(i+1), edge(i,a,b) ∧ W(h,i+1,b)).

The implementation should use reverse time `r = h-i`, so its defining
recursion is forward primitive recursion.  Bounded existential is the Boolean
fold from `BoundedFormulaBlueprint`.

Object theorem `viable_iff_path`:

  [] ⊢[PRAAx] W(h,i,a)=1 ↔
       there is a coded compatible valid path from (i,a) through h.

The right side is itself represented by a bounded Boolean checker.  The proof
is quantifier-free induction on `h-i`.

Object theorem `least_path_correct`:

  from `∃ a < bound(0), W(h,0,a)=1`, bounded least search constructs the
  lexicographically least full path and proves every validity and edge row.

No infinite branch is chosen.  For a requested precision p, a PR horizon H(p)
is fixed and only that finite path is constructed.  The shrinking-viability
Cauchy theorem then uses (a) a diameter modulus for viable candidates and (b)
a summable edge-motion budget.  Exact labels are recovered only under a
separate positive-gap proof.
-/

end LeanProofs.ConciseIPRA.PCOG
