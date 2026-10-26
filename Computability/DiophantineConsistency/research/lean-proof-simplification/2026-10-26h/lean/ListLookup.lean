import Init.Data.List.Lemmas

/-! Exact generic replacements for seven duplicated list inductions. -/
namespace ProofSimplification.ListLookup

theorem lookup_mem {α : Type} {xs : List α} {i : Nat} {a : α}
    (h : xs[i]? = some a) : a ∈ xs :=
  List.mem_of_getElem? h

theorem exists_lookup {α : Type} (xs : List α) (a : α) (h : a ∈ xs) :
    ∃ i : Nat, xs[i]? = some a :=
  List.getElem?_of_mem h

#print axioms lookup_mem
#print axioms exists_lookup

end ProofSimplification.ListLookup
