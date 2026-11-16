import KIFCR.BooleanBlueprint
import IPRADerivations.Core.Search

/-!
# Adapter to the current checked least-search library

`IPRADerivations.Core.Search` already defines `Search.mu` and proves its QF
specification, foundness, soundness, and minimality.  KIFC-R must wrap that
implementation rather than introduce a second search recurrence.
-/

namespace LeanProofs.KIFCR

open LeanProofs.ConciseIPRA
open LeanProofs.IPRA
open Syn
open scoped Fm

/-- Public contract generated from one fixed reflected success predicate.
The proof fields are intended to be constructed by instantiating
`LeanProofs.IPRA.Search.search_spec` and `search_found`. -/
structure FirstValidCertificate (n : ℕ) where
  pre : Fm PTm n
  bound : PTm n
  witness : PTm n
  witnessFound : Fm PTm n
  witnessValid : Fm PTm n
  witnessMinimal : Fm PTm n
  found : [pre] ⊢[PRAAx] witnessFound
  valid : [pre, witnessFound] ⊢[PRAAx] witnessValid
  minimal : [pre, witnessFound] ⊢[PRAAx] witnessMinimal

/-!
Implementation target:

* For Boolean predicate `p`, define the zero-success body `1 ∸ p`.
* Prove, from the Boolean range theorem, `(1 ∸ p = 0) ↔ (p = 1)`.
* Define `firstValid p N x := Search.mu (1 ∸ p) N x`.
* Derive `firstValid_sound`, `firstValid_found`, and `firstValid_minimal` only
  by term instantiation, equality transport, and the checked Search theorems.
* Build bounded argmin and finite cover selection as clients of this adapter.

No new induction belongs in this module.
-/

end LeanProofs.KIFCR
