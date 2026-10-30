# Exact degree certificate for the factored 87-operation parent

[`verify_degree87_parent.py`](verify_degree87_parent.py) evaluates the actual pinned factored 87-row JSON (SHA-256 `da6b88365da3ec9db6040373c25de20b30baf63edc9fdf742de2aa4b2c06e6e8`) as exact sparse integer polynomials in its thirteen unknowns and four symbolic ports. It checks the final product wiring and the exact degree in unknowns of each of the four factors, and exhibits one top-degree witness monomial whose coefficient has exactly one port monomial:

| Factor | Degree | Witness monomial | Coefficient |
|---|---:|---|---:|
| first | 15 | `J^9 X^2 Y^2 eta^2` | `-2 beta^9` |
| main | 13 | `J^4 X^2 Y^5 eta gamma` | `8 beta^4` |
| auxiliary | 13 | `J^4 f^4 X^2 Y^2 u` | `2 beta^4` |
| strong | 10 | `i^2 Y^4 eta^4` | `1` |

The other three ports do not occur in these coefficients, and the fixed `beta=(2^47)^2011-1` is positive. Hence the top coefficients remain nonzero after all ports are fixed. Since the integer polynomial ring is an integral domain, the degree of the product minus one is exactly `15+13+13+10=51`. Positive shifting preserves the leading homogeneous part. This audits the specific factored 87 graph directly; it does not assume that the earlier unfactored graph's degree survived a transformation.

Run `python3 Computability/DiophantineConsistency/research/adaptive-direct-ordinate86/verify_degree87_parent.py`; the saved transcript is [`verify_degree87_parent.out`](verify_degree87_parent.out). The root independently reran the script and reviewed the coefficient and integral-domain argument. This is an exact computational/mathematical certificate, not a Lean degree theorem or a minimality claim. The independently checked 86-operation variant has degree 56, so these two candidates trade operation count against polynomial degree.
