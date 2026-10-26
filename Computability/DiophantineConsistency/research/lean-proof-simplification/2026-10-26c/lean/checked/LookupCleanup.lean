/-! The two core-library facts used by lookup-cleanup.patch.

The source files have exactly these statements, specialized to Form, Row,
or Judgment. No project assumptions are used by either proof.
-/

namespace ProofRefactor.LookupCleanup

theorem lookup_mem {A : Type} {xs : List A} {i : Nat} {a : A}
    (h : xs[i]? = some a) : a ∈ xs :=
  List.mem_of_getElem? h

theorem exists_lookup {A : Type} (xs : List A) (a : A) (h : a ∈ xs) :
    ∃ i : Nat, xs[i]? = some a :=
  List.getElem?_of_mem h

#print axioms lookup_mem
#print axioms exists_lookup

end ProofRefactor.LookupCleanup
