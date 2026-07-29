From PolynomialFormulas Require Import Basic Cubic CubicComplex Quartic.

(** Kernel-assumption audit for the degree-one-through-four solver theorems. *)

Import LeanProofs.PolynomialFormulas.
Import LeanProofs.PolynomialFormulasCubic.
Import LeanProofs.PolynomialFormulasQuartic.

Check solve_linear_correct.
Check solve_quadratic_correct.
Check cardano_formula.
Check solve_cubic_correct.
Check ferrari_parameters_of_resolvent.
Check solve_quartic_correct.
Check LeanProofs.PolynomialFormulasCubicComplex.cubic_eq_zero_iff.
Check solve_quartic_exhaustive.
Check quartic_eq_zero_iff.

Print Assumptions solve_linear_correct.
Print Assumptions solve_quadratic_correct.
Print Assumptions cardano_formula.
Print Assumptions solve_cubic_correct.
Print Assumptions ferrari_parameters_of_resolvent.
Print Assumptions solve_quartic_correct.
Print Assumptions LeanProofs.PolynomialFormulasCubicComplex.cubic_eq_zero_iff.
Print Assumptions solve_quartic_exhaustive.
Print Assumptions quartic_eq_zero_iff.
