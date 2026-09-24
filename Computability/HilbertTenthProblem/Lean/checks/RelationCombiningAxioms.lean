import Diophantine

/-!
Transitive axiom audit for relation combining and the twelve-variable prime
polynomial. Run `lake env lean Computability/HilbertTenthProblem/Lean/checks/RelationCombiningAxioms.lean` after
the consolidated build. Only Lean's standard logical axioms are expected.
-/

#print axioms Diophantine.RadicalWeights.norm_weightedSum_le
#print axioms Diophantine.RadicalWeights.eq_zero_of_weightedSum_eq_zero
#print axioms Diophantine.RadicalWeights.one_le_weight_add_re
#print axioms Diophantine.RadicalBounds.norm_sq_of_sq_eq_int
#print axioms Diophantine.RadicalBounds.one_le_norm_of_sq_eq_int
#print axioms Diophantine.RadicalBounds.norm_le_sq_of_sq_eq_int
#print axioms Diophantine.RadicalField.isGalois
#print axioms Diophantine.RadicalField.exists_rat_of_fixed
#print axioms Diophantine.RadicalField.isSquare_int_of_fixed
#print axioms Diophantine.RadicalIndependence.isSquare_of_rational_weightedSum
#print axioms Diophantine.RadicalIndependence.isSquare_of_rational_powerSum
#print axioms Diophantine.signFlip_invariant_iff_exists_expand_two
#print axioms Diophantine.RelationCombiningPolynomial.signFlip_rawProduct
#print axioms Diophantine.RelationCombiningPolynomial.expand_two_core
#print axioms Diophantine.RelationCombiningPolynomial.value_eq_product
#print axioms Diophantine.RelationCombiningPolynomial.eval_compose
#print axioms Diophantine.RelationCombiningPolynomial.eval_polynomial_assignment
#print axioms Diophantine.RelationCombiningBounds.one_le_offset
#print axioms Diophantine.RelationCombiningArithmetic.sum_rational_of_factor
#print axioms Diophantine.RelationCombiningArithmetic.factor_iff
#print axioms Diophantine.RelationCombining.squares_of_value_zero
#print axioms Diophantine.RelationCombining.conditions_of_value_zero
#print axioms Diophantine.RelationCombining.exists_value_zero_of_conditions
#print axioms Diophantine.RelationCombining.relationCombining_iff
#print axioms JSWW1976.beta_defined_iff_margin
#print axioms JSWW1976.elim39Values_divisibility_positive
#print axioms JSWW1976.Sys39.reduced
#print axioms JSWW1976.ReducedSys39.exists_sys39
#print axioms JSWW1976.reducedSys39_iff_exists_sys39
#print axioms JSWW1976.theorem_3_9_reduced
#print axioms JSWW1976.TwelveVariable.eval_combined
#print axioms JSWW1976.TwelveVariable.reduced_of_combined_zero
#print axioms JSWW1976.TwelveVariable.exists_combined_zero_of_reduced
#print axioms JSWW1976.TwelveVariable.positive_value_prime
#print axioms JSWW1976.TwelveVariable.exists_value_of_prime
#print axioms JSWW1976.TwelveVariable.prime_iff_positive_value
#print axioms JSWW1976.TwelveVariable.exists_twelve_variable_prime_polynomial
