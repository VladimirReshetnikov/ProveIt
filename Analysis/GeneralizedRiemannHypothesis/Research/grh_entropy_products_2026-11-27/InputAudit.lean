-- Run inside the vendor grh/ Lake package with its pinned toolchain.
-- This is an interface and axiom audit, NOT a formalization of the new results.
import Main

#check DirichletLNonvanishingRightOfHalf
#check LFunction_ne_zero_of_half_lt_re
#check DirichletLZerosOnLine
#check LFunction_eq_zero_re
#check riemannHypothesis
#print axioms LFunction_ne_zero_of_half_lt_re
#print axioms LFunction_eq_zero_re
#print axioms riemannHypothesis

-- Check that the half-plane theorem actually has the public proposition type.
example : DirichletLNonvanishingRightOfHalf := LFunction_ne_zero_of_half_lt_re
example : DirichletLZerosOnLine := LFunction_eq_zero_re
