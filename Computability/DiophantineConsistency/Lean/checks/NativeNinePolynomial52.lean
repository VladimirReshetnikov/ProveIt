import DiophantineConsistency.NativeNinePolynomial52

open DiophantineConsistency.NativeNinePolynomial52
open scoped BigOperators

example : (∑ k : Fin 22, (DiophantineConsistency.NativeQuadraticParent.rowSupport k).card) = 136 := by
  decide

example : sourceBase (3 : ℤ) 2 = 49152 := by decide

private def boundary : DiophantineConsistency.NativeNineRatio52.NewVars := ⟨1, 1, 1, 0, 1, 0⟩

example : witnessVector 2 3 boundary 4 = ![2, 3, 1, 1, 1, 0, 1, 0, 4] := rfl

example : ratioValue (8 : ℤ) 8 1 0 100 1 1 1 0 1 0 0 =
    boundary.finalValue 8 8 1 0 100 0 := rfl

#print axioms ratioValue
#print axioms kernelValue
#print axioms value
#print axioms value_eq_finalValue
#print axioms map_value
#print axioms eval_polynomial
