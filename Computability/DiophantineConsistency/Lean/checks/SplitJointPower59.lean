import DiophantineConsistency.SplitJointPower59
open DiophantineConsistency.SplitJointPower59
#print axioms positiveValue_eq_parent
#print axioms naturalValue_eq_parent
#print axioms positivePolynomial_eq_parent
#print axioms naturalPolynomial_eq_parent

-- The polynomial identity transfers degree for every supplied fixed tuple.
example (p : Fin 12 → ℤ) :
    (DiophantineConsistency.SplitJointCircuit59.positivePolynomial p).totalDegree =
      (DiophantineConsistency.SplitCircuit59.positivePolynomial p).totalDegree :=
  congrArg MvPolynomial.totalDegree (positivePolynomial_eq_parent p)

example {R : Type*} [CommRing R] (p : Fin 12 → R) (x : Fin 9 → R) :
    DiophantineConsistency.SplitJointCircuit59.naturalValue p x = 0 ↔
      DiophantineConsistency.SplitCircuit59.naturalValue p x = 0 := by
  rw [naturalValue_eq_parent]
