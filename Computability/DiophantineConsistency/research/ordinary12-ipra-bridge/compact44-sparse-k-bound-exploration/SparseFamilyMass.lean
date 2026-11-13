import AbstractSparseFamily
set_option autoImplicit false
namespace SparseFamilyMass
open scoped BigOperators

theorem twoBands_total {n : ℕ} (left right weight : Fin n → ℕ) :
    ((AbstractSparseFamily.twoBands left right weight).map Prod.snd).sum =
      2 * (∑ i : Fin n, weight i) := by
  simp [AbstractSparseFamily.twoBands, AbstractSparseFamily.terms,
    List.map_ofFn, List.sum_ofFn, two_mul]

#print axioms SparseFamilyMass.twoBands_total
end SparseFamilyMass
