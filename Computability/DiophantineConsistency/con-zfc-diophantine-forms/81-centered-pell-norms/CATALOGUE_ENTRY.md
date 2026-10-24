# Proposed catalogue entry: centered Pell norms and shared positivity

Source number: **to be assigned by the repository maintainer**.

Comparison pin: `2605669a532342f153b13eb6b4a0af4b54f5fa37` (sources 31–75,
wave-10 catalogue).

| Domain | Variables | Exact degree | Live binary operations | Change against inspected comparison |
|---|---:|---:|---:|---|
| unrestricted integers | 31 | 6 | 144 | one fewer variable than the 32-integer sextics |
| unrestricted integers | 26 | 8 | 131 | one fewer variable than the 27-integer octics |
| unrestricted integers | 24 | 10 | 135 | dominates the 26-integer degree-16 point |
| unrestricted integers | 23 | 12 | 122 | dominates the 26-integer degree-16 and 24-integer degree-1936 points |
| unrestricted integers | 22 | 14 | 123 | dominates the same two prior points |
| strictly positive integers | 11 | 277 | 111 | degree 325→277 and operations 113→111 |
| strictly positive integers | 12 | 78 | 103 | degree 82→78, operations 102→103 |

The integer equations combine the signed-power bootstrap, canonical
determinant and shared positivity. Centering the auxiliary root and applying
an elementary strong-norm row operation remove the strong ordinate at
degree fourteen; a main-norm replacement on a proved nonzero scale produces
the degree-ten companion. The positive equations combine the adjacent-Pell
integrality descent and adaptive weighted carriers with the previous
norm-based constructions.

All fixed coefficient bytes, exact polynomial packets, compact evaluators,
literal source pins, ordinary mathematical proofs and standard-library
checkers are included. Formal status: ordinary inherited native/compiler
calibration plus new proved reductions; no new complete Lean/Rocq or
object-language ZFC derivation. The nine-positive and ten-integer
high-degree variable records are unchanged. The alternative CRT
homogenization appendix is a compiler-stage result, not a completed eighth
equation.

Reproduction command: `python3 verify.py`. The separate `_circuit.json`
files give the operation counts for the integer equations. The
25-integer/degree-12 intermediate is not a frontier claim.
