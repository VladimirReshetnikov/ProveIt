import DiophantineConsistency.GapNinePolynomial66
open DiophantineConsistency.GapNinePolynomial66
#print axioms map_coefficients0
#print axioms map_coefficients1
#print axioms map_coefficients2
#print axioms map_kernel0
#print axioms map_kernel1
#print axioms map_kernel2
#print axioms map_sourceRank
#print axioms map_ratioValue
#print axioms map_mixedValue
#print axioms map_value
#print axioms kernel0_eq_eval
#print axioms kernel1_eq_eval
#print axioms kernel2_eq_eval
#print axioms ratioValue_nat
#print axioms eval_polynomial
#print axioms sourceBase_nat
#print axioms sourceRank_nat
#print axioms threshold_nat
#print axioms marginScale_nat
#print axioms mixedValue_nat
#print axioms successorShift_nat
#print axioms value_eq_naturalValue
#print axioms eval_polynomial_nat
#print axioms exists_natural_zero_iff_source
#print axioms exists_natural_zero_iff_source_portBounds
#print axioms exists_natural_zero_iff_source_compact54
#print axioms no_natural_zero_iff_source
#print axioms compact54_zero_iff_split59

-- This is actual ordinary integer-polynomial data with exactly the nine input indices.
noncomputable example (ports : Fin 4 → ℤ) (a : ℕ) : MvPolynomial (Fin 9) ℤ := polynomial ports a
