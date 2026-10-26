import Init.Data.List.Lemmas

/-! A checked generic replacement for the private lookup lemma in
AnnotatedProofChecker.lean. The enclosing checker module was not replayed
as part of this small API check. -/
namespace DiophantineConsistency.ProofRefactor

universe u

theorem mem_of_lookup {α : Type u} {seen : List α} {i : Nat} {j : α}
    (h : seen[i]? = some j) : j ∈ seen :=
  List.mem_of_getElem? h

#print axioms mem_of_lookup

end DiophantineConsistency.ProofRefactor
