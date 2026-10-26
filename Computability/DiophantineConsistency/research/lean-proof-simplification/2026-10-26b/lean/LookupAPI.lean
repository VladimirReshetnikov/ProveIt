import Std

/-!
The two standard-library lemmas below replace seven local induction proofs
in the pinned DiophantineConsistency snapshot. This checks their general
types, so the Form and Judgment instances are direct specializations.
See lookup-api.patch for the exact proof-only proposed changes.
-/

namespace DiophantineConsistency.Proposals.LookupAPI

theorem lookup_mem {α : Type} {xs : List α} {i : Nat} {a : α}
    (h : xs[i]? = some a) : a ∈ xs :=
  List.mem_of_getElem? h

theorem exists_lookup {α : Type} (xs : List α) (a : α) (h : a ∈ xs) :
    ∃ i : Nat, xs[i]? = some a :=
  List.getElem?_of_mem h

#print axioms lookup_mem
#print axioms exists_lookup

end DiophantineConsistency.Proposals.LookupAPI
