# Ten integer norm saturated equation

This component gives a completed ordinary polynomial with ten unrestricted integer variables, exact degree 1,245,324, and480 live binary operations. It lowers the previous degree1,576,864 while saving one operation and retaining the same fixed coefficient values.

The structural idea replaces C^4 D^2 xi^2 by C^4 D xi^2 in the two inner Pell expressions, while retaining the old congruence modulus. D is proved square by the certificate, so its square root can occur only in the mathematical proof. The source inequality guard excludes C=+/-1, and a generalized full-residue interpolation theorem proves completeness.

- `PROOF.md`: full mathematical argument and source interface.
- `section.tex`: article-ready section.
- `integer10.json`: exact division-free circuit.
- `fixed/` and `FIXED_COEFFICIENTS.json`: twelve actual signed fixed integer leaves.
- `data/`: fixed source packing and authentic four coefficient ports.
- `build.py`: reproducible constructor; `circuit.py`: elementary DAG helper.
- `check.py`: actual coefficients, degree, topology, full independent formula, residue and identity checks.
- `check_interpolation.py`: independent finite modular realizations of the new interpolation theorem.
- `independent_formula.py`: separate direct source-plus-tail evaluator.

Run `python3 build.py`, `python3 check.py`, and `python3 check_interpolation.py` from this directory. Checkers also work under `python3 -O`. Finite checks do not replace the unbounded proof. The compiler/calibration and classical Lucas interfaces remain inherited dependencies; no new Lean/Rocq certificate or global minimality is claimed.
