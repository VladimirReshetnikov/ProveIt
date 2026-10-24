# Lower-degree quotient-fusion companions

These four unrestricted-integer equations share the complete actual six-coefficient
binding in `../../coefficients/BINDING.json`. The `port` leaves of each DAG name
those exact numerals; they are not extra variables or unfilled parameters.

| File stem | Integer variables | Degree | Binary operations |
|---|---:|---:|---:|
| quotient20 | 20 | 24 | 120 |
| quotient20_transport | 19 | 28 | 116 |
| quotient19_transport | 18 | 32 | 112 |
| quotient18_transport | 17 | 88 | 110 |

Run `python build.py` to reproduce the four literal DAGs and `python verify.py`
to check them. The verifier checks exact homogeneous leading coefficients,
all live variables and binary operation counts, independent residual formulas
modulo a prime with symbolic test ports, and additional diagnostics with the
actual fixed coefficients. These finite diagnostics do not replace the
number-theoretic proof in `PROOF.md` and the main report.

The proof retains two earlier intermediate endpoints for comparison; only the
four nondominated endpoints above are exported in this directory.
