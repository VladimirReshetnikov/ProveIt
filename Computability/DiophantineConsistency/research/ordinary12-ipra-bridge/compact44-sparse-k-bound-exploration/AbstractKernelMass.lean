import SparseFamilyMass
set_option autoImplicit false
namespace AbstractKernelMass
open scoped BigOperators

def kernelShape {n m : ℕ} (left right weight : Fin n → ℕ)
    (left' right' weight' : Fin m → ℕ) : List (ℕ × ℕ) :=
  [(30,1),(62,1),(1100,1),(2201,1)] ++
  AbstractSparseFamily.twoBands left right weight ++
  AbstractSparseFamily.twoBands left' right' weight' ++ [(8849,1)]

theorem kernelShape_mass {n m : ℕ} (left right weight : Fin n → ℕ)
    (left' right' weight' : Fin m → ℕ) :
    ((kernelShape left right weight left' right' weight').map Prod.snd).sum + 1 =
      2 * ((∑ i : Fin n, weight i) + (∑ i : Fin m, weight' i)) + 6 := by
  simp only [kernelShape, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, SparseFamilyMass.twoBands_total]
  omega

#print axioms AbstractKernelMass.kernelShape_mass
end AbstractKernelMass
