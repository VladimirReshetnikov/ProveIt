# Signed affine horizons

This portable component contains two complete fixed-coefficient quartics over unrestricted integers.

| Profile | Variables | Quadratic residuals | Degree | Monomials | Coefficient height |
|---|---:|---:|---:|---:|---:|
| p214_scaled_square |214|153|4|5875|655360|
| p212_minimum8 |212|151|4|5706|316912650058804747029598371840|

Read AFFINE_HORIZON_PROOF.md for the ordinary mathematical proof and exact dependency boundary. Each equation is the sum of the squares of the complete quadratic rows in its equation.json. The adjacent expanded_polynomial.json supplies every collected coefficient. All variables are unrestricted integers; no variable exponentiation occurs in the final equations.

Run `python3 verify_affine_horizons.py` or `python3 -O verify_affine_horizons.py` from this directory. Python's standard library suffices. Run `python3 build_affine_horizons.py` to rebuild both emitted equations from the exact pinned source files. The separate evaluator accepts an equation path and a JSON integer tuple: `python3 evaluate.py affine_horizons/p214_scaled_square/equation.json point.json`.

The inherited certificates establish that the source horizon and growth changes commute with the original coordinate reductions. Finite checks authenticate all new coefficients and exact maps; the unbounded proof is separate. This component proves an equivalence to syntactic consistency, not consistency or the existence of a zero.

New exposition and code are provided under the included MIT No Attribution license. The numerical calculus, signed Pell interfaces, CRT source, original equations and inherited projections are credited in PROVENANCE.json and NOTICE.source173.md. No worldwide priority or global minimum claim is made.
