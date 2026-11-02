# Direct substitutions in the 26-variable degree-eight graph

[`survey.py`](survey.py) checks 14 direct witness bindings in square
residuals of the pinned [AQ26 graph](../adaptive-square-sums26-degree8/candidate.json).
The 14 include both direct bindings of `qValueVariable`; the `g72` binding
has the opposite subtraction orientation.
For each coordinate it substitutes the bound DAG expression into every
residual, checks that the removed binding residual is identically zero, and
calculates the exact degrees by sparse integer-polynomial arithmetic. It finds
a surviving highest-degree monomial whose coefficient is a nonzero integer
times a power of `beta`. Since the fixed `beta = (2^47)^2011 - 1` is positive,
that monomial survives specialization of the ports. Translation by the
positive shift preserves polynomial degree. A real sum of squares cannot
cancel the top degree of all its nonzero residuals.

| Eliminated coordinate | Resulting sum-of-squares degree |
| --- | ---: |
| `scaleVariable` | 16 |
| `mainScaleVariable` | 12 |
| `rankVariable` | 10 |
| `cVariable` | 10 |
| `ellVariable` | 16 |
| `cSquareVariable` | 12 |
| `zValueVariable` | 16 |
| `dValueVariable` | 12 |
| `vValueVariable` | 18 |
| `deltaVariable` | 10 |
| `qSquareVariable` | 10 |
| `productVariable2` | 10 |
| `qValueVariable` | 10 |
| `qValueVariable` from `g72` | 12 |

Thus none of these **single direct substitution and deletion** rewrites
preserves degree eight. The calculation does not assert that each substituted
expression is positive, prove a witness transport, rule out different
rewrites or equations, or establish any global minimum. In particular it is a
Python finite polynomial calculation, not a Lean degree theorem. Run with
normal Python: `python3 survey.py`; optimized mode is rejected.
