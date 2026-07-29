import PolynomialFormulas

/-! Kernel-assumption audit for the degree-one-through-four solver theorems. -/

open LeanProofs.PolynomialFormulas

#check solveLinear_correct
#check solveQuadratic_correct
#check cardano_formula
#check solveCubic_correct
#check ferrari_parameters_of_resolvent
#check solveQuartic_correct
#check cubic_eq_zero_iff
#check quartic_eq_zero_iff

#print axioms solveLinear_correct
#print axioms solveQuadratic_correct
#print axioms cardano_formula
#print axioms solveCubic_correct
#print axioms ferrari_parameters_of_resolvent
#print axioms solveQuartic_correct
#print axioms cubic_eq_zero_iff
#print axioms quartic_eq_zero_iff
