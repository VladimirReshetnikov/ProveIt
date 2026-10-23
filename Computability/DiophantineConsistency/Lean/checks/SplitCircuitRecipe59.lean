import DiophantineConsistency.SplitCircuitRecipe59
open DiophantineConsistency.SplitCircuitRecipe59
open DiophantineConsistency.SplitCircuitRegisters59
#print axioms naturalValue_eq_recipe
#print axioms jointNaturalValue_eq_recipe
#print axioms map_fixedLeaves
#print axioms naturalPolynomial_eq_recipe
#print axioms jointNaturalPolynomial_eq_recipe

example (ports : Fin 4 → ℤ) (a : ℕ) :
    (DiophantineConsistency.SplitJointCircuit59.naturalPolynomial
      (fixedLeaves ports ((2:ℤ)^a) ((2:ℤ)^(8*a+85)))).totalDegree =
        (DiophantineConsistency.SplitNinePolynomial59.polynomial ports a).totalDegree :=
  congrArg MvPolynomial.totalDegree (jointNaturalPolynomial_eq_recipe ports a)
