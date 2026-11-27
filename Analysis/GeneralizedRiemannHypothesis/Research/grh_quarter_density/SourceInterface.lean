/-!
  Optional upstream interface audit; not executed for this research note.
  Run in the vendored grh package after its documented build:
    lake env lean /absolute/path/to/SourceInterface.lean
  This file is not a formalization of the new allocation theorem.
-/
import Main

#check riemannHypothesis
#check riemannZeta_eq_zero_re
#check LFunction_ne_zero_of_half_lt_re
#check LFunction_eq_zero_re
#check LFunction_eq_zero_re_of_isPrimitive

example : DirichletLNonvanishingRightOfHalf := LFunction_ne_zero_of_half_lt_re
example : DirichletLZerosOnLine := LFunction_eq_zero_re

#print axioms riemannHypothesis
#print axioms LFunction_ne_zero_of_half_lt_re
#print axioms LFunction_eq_zero_re
