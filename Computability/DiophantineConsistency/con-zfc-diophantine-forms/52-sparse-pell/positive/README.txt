POSITIVE-VARIABLE IMPROVEMENTS

Recommended single equations:
  positive11_Y_lean_product.json      11 positive variables, degree 954, 113 gates
  positive12_none_lean_product.json   12 positive variables, degree 897, 108 gates

Recommended shifted systems:
  positive11_Y_lean_shifted_system.json  2 equations, max degree 952, 108 gates
  positive12_none_lean_shifted_system.json  3 equations, max degree 888, 102 gates

The unshifted systems are included to match the direct product equation.
All variables are strictly positive integers. All other names are computed
registers, not additional variables. Gates are binary +,-,*; multiplication
by an integer literal is charged. System comparisons are uncharged.

The fixed integer coefficients must be loaded together via
COEFFICIENT_BINDING.json. Its paths point to the sibling coefficients folder.
No finite test values can replace the fixed coefficients.

Read Y_ABSORPTION_PROOF.md for the full soundness, completeness, positivity,
exact-degree and inherited compiler boundary. section.tex is the concise
LaTeX contribution to the consolidated report. The independent mathematical
review and leading-form checks are in ../review/POSITIVE_THEOREM_REVIEW.md,
../review/POSITIVE_LEADING_FORM_CHECKS.json and
../review/check_positive_leading_form.py.

Reproduce with Python 3 and NumPy:
  python build_absorbed.py
  python check_absorbed.py

The newly authored checker validates actual fixed-payload hashes, 240 formal
radical products, 240 modulo-four guards, 18 full univariate polynomial
replays over three finite fields, 120 transport-shift identities and 432
no-index-equation bound instances. CHECK_RESULTS.json is the receipt.
The builder executes no upstream code. Preserved upstream proof texts are
inert references, with source pins and licenses retained.

The theorem is the equivalence of insolubility with Con(ZFC), not a proof of
consistency or inconsistency. The unbounded machine/compiler bridge remains
an inherited ordinary mathematical dependency, not a newly kernel-checked
Lean/Rocq certificate. No ten-positive-variable improvement is claimed.

Research boundary: attempting to absorb the independent transport quotient
as well would remove Nt=1, which currently supplies the outer positivity and
R bounds. No sound replacement for those prerequisites was established.
Simply clearing a second denominator or deleting that equation is not valid.
