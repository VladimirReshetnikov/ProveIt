import KIFC.BooleanBlueprint

/-!
# Least bounded search blueprint

A completed module will define the packed `(found, witness)` state by one
primitive recursion and prove its quantifier-free prefix invariant through
`LoopCertificate`.
-/

namespace LeanProofs.KIFC

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm

/-- Public object-level interface of a generated least-search routine.

The formulas `hasWitness`, `witnessValid`, and `witnessMinimal` are generated
from one fixed reflected predicate.  Keeping them as fields allows application
modules to depend on the proof contract before the generic generator is done. -/
structure SearchCertificate (n : ℕ) where
  pre : Fm PTm n
  found : PTm n
  witness : PTm n
  hasWitness : Fm PTm n
  witnessValid : Fm PTm n
  witnessMinimal : Fm PTm n
  foundIff : [pre] ⊢[PRAAx]
    Fm.iff (found ≐ one) hasWitness
  valid : [pre, found ≐ one] ⊢[PRAAx] witnessValid
  minimal : [pre, found ≐ one] ⊢[PRAAx] witnessMinimal

/-!
Target implementation invariant for search time `i`:

* `found i = anyB i pred`;
* if found, `witness i < i`;
* if found, the reflected predicate holds at the witness;
* if found, `allB (witness i) (not pred) = 1`;
* if not found, witness is the chosen default.

Every clause is quantifier-free because bounded content is represented by a
fold term.  At the terminal bound, fold reflection yields the quantified API.
-/

end LeanProofs.KIFC
