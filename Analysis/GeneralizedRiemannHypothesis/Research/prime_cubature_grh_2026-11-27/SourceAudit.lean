/-
Audit entry point only. Run in the vendored grh Lake package with its pinned
Lean/Mathlib: lake env lean /absolute/path/to/SourceAudit.lean
Not run in the research environment. Does not formalize paper.tex.
-/
import Main

#check riemannHypothesis
#check riemannZeta_eq_zero_re
#check LFunction_ne_zero_of_half_lt_re
#check LFunction_eq_zero_re
#check LFunction_eq_zero_re_of_isPrimitive
#print axioms LFunction_eq_zero_re_of_isPrimitive
#print axioms LFunction_ne_zero_of_half_lt_re

theorem primeCubatureInput : PrimitiveDirichletLZerosOnLine :=
  LFunction_eq_zero_re_of_isPrimitive

#print axioms primeCubatureInput
