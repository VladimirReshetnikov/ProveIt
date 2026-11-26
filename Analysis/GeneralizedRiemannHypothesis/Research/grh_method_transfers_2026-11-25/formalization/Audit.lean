/-
Upstream audit driver. NOT RUN in this session.
First complete `lake build` in the pinned upstream grh project. Then run
`lake env lean /absolute/path/to/Audit.lean` from that project directory.
It imports the upstream final theorem and prints its types and axiom dependencies.
-/
import Main

#check riemannHypothesis
#check LFunction_ne_zero_of_half_lt_re
#check LFunction_eq_zero_re
#print axioms riemannHypothesis
#print axioms LFunction_ne_zero_of_half_lt_re
#print axioms LFunction_eq_zero_re
