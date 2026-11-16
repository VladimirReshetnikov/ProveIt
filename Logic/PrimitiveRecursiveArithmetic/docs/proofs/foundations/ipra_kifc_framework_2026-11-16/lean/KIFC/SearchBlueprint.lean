import KIFC.BooleanBlueprint
import IPRADerivations.Core.Search

/-!
# Checked-search adapter and least bounded search contract

The audited repository already contains `LeanProofs.IPRA.Search.mu`,
`search_spec`, `search_found`, and `search_minimal`, all as derivations in
`Prf PRAAx`.  KIFC should reuse that engine.  The missing generic layer is a
formula-specific Boolean compiler and an adapter from truth-as-one to the
zero predicate expected by `Search.mu`.
-/

namespace LeanProofs.KIFC

open LeanProofs.ConciseIPRA
open LeanProofs.IPRA
open Syn
open scoped Fm
open LeanProofs.ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (monus)

/-- Convert a Boolean truth code `chi` into a zero-on-truth search body.
The proof that this has the intended zeros uses the Boolean range theorem. -/
def zeroOnTrue {n : ℕ} (chi : PTm n) : PTm n :=
  monus one chi

/-- Public object-level interface of a generated least-search routine.

The formulas are generated from one fixed reflected predicate.  Application
modules may depend on this contract while the syntax-directed adapter is being
implemented. -/
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
Completion path:

1. obtain a `Reflected` predicate `P(i,x) <-> chi(i,x)=1`;
2. prove, from `predicate.range` and the monus equations,
   `zeroOnTrue chi = 0 <-> chi = 1`;
3. instantiate `IPRA.Search.mu` with the specialized two-argument zero test
   (or pack several parameters with the checked pairing library);
4. transport `search_spec`, `search_found`, and `search_minimal` through the
   reflection theorem;
5. package the transported derivations as `SearchCertificate`.

No competing least-search induction should be added to the trusted generic
layer unless an application needs a different arity and direct generation is
smaller than parameter packing.
-/

end LeanProofs.KIFC
