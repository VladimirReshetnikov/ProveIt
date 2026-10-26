import Init

namespace DiophantineConsistency.ProofSimplification

/-- Replaces the duplicated `lookup_mem` / `mem_of_lookup` inductions. -/
theorem lookup_mem_short {α : Type u} {xs : List α} {i : Nat} {a : α}
    (h : xs[i]? = some a) : a ∈ xs :=
  List.mem_of_getElem? h

/-- Replaces both duplicated `exists_lookup` inductions. -/
theorem exists_lookup_short {α : Type u} (xs : List α) (a : α) (h : a ∈ xs) :
    ∃ i : Nat, xs[i]? = some a :=
  List.getElem?_of_mem h

#print axioms lookup_mem_short
#print axioms exists_lookup_short

end DiophantineConsistency.ProofSimplification
