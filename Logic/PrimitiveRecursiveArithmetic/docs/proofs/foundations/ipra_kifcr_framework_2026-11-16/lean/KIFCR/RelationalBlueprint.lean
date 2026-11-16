import KIFCR.SearchAdapterBlueprint
import KIFCR.TraceBlueprint

/-!
# Finite relational viability blueprint

The intended object representation is a rectangular Boolean table.  Backward
row computation is one QF-certified trace; path extraction uses the checked
least-search adapter.  The public theorem exports a path checker or a stable
observer, not an unproved global choice function.
-/

namespace LeanProofs.KIFCR

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm

structure RelationTowerCertificate (n : ℕ) where
  pre : Fm PTm n
  horizon : PTm n
  width : PTm n
  viabilityTable : PTm n
  anyStartViable : Fm PTm n
  selectedPath : PTm n
  pathValid : Fm PTm n
  viabilityLoop : LoopCertificate n
  pathProof : [pre, anyStartViable] ⊢[PRAAx] pathValid

structure ExactObserverCertificate (n : ℕ) where
  pre : Fm PTm n
  selectedValid : Fm PTm n
  output : PTm n
  arbitraryValid : Fm PTm n
  observerIndependent : Fm PTm n
  selected : [pre] ⊢[PRAAx] selectedValid
  stable : [pre, selectedValid, arbitraryValid] ⊢[PRAAx]
    observerIndependent

structure DiameterObserverCertificate (n : ℕ) where
  pre : Fm PTm n
  selectedValid : Fm PTm n
  arbitraryValid : Fm PTm n
  diameterBound : Fm PTm n
  selected : [pre] ⊢[PRAAx] selectedValid
  stable : [pre, selectedValid, arbitraryValid] ⊢[PRAAx]
    diameterBound

/-!
Completion path:

1. Implement finite table lookup/write over checked pairing.
2. Generate the reverse viability recurrence with `anyB` rows.
3. Prove the written-row invariant using `LoopCertificate`.
4. Define a coded bounded path checker.
5. Prove viability iff an accepted suffix code exists.
6. Use `Search.mu` adapters for least viable starts/successors.
7. Compose selected-path validity.
8. Add exact/diameter observer elimination and, separately, the finite tail
   theorem needed for coherent names.
-/

end LeanProofs.KIFCR
