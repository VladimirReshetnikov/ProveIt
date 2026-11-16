import KIFCS.OpenContract

/-!
# Backend integration

Native open-sequent transfer is already checked upstream.  Foundation open
transport remains a separate integration task; its expected interfaces and
round-trip obligations are documented here without adding an axiom.
-/

set_option autoImplicit false

namespace LeanProofs.ConciseIPRA.KIFCS

open scoped Fm

variable {n : Nat} {A : List (Fm PTm n)} {phi : Fm PTm n}

/-- Direct contract/native equivalence inherited from `pra_iff_native`. -/
theorem contract_iff_native :
    Contract A phi ↔ NPrf (A.map NFm.ofPRA) (NFm.ofPRA phi) :=
  Contract.iff_native

/-!
Expected Foundation completion path:

1. prove object-level extensional equality of every Foundation PR code and its
   Concise round trip at arbitrary parameters;
2. lift to terms and formula biconditionals, including both binders;
3. prove translation commutes with substitution, shift, and context mapping;
4. preserve open derivations under arbitrary term assignments;
5. reflect finite free-variable contexts using distinct fresh indices;
6. replace translated assumptions by originals through round-trip
   biconditionals and `Prf.trans`;
7. expose an open contract transport theorem and recover the existing closed
   endpoints as corollaries.

No declaration is introduced here until those proofs are implemented.
-/

end LeanProofs.ConciseIPRA.KIFCS
