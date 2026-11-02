# A 22-coordinate degree-10 candidate

This is a research candidate obtained from the pinned 26-coordinate,
degree-8 sum-of-squares graph in `../adaptive-square-sums26-degree8/`.
Its graph has 22 positive-coordinate inputs, four fixed-numeral ports,
114 live arithmetic rows and 13 squared residuals.  It trades two degrees
for four fewer coordinates; this is not a minimality result. The graph is
given by `candidate.json`, not by the equation in the project's current PDF.

The scripts check exact polynomial identities and degree. They are not Lean
proofs, and neither a Lean witness-transport theorem nor a native iPRA proof
for this candidate has been completed. In particular, these finite checks do
not prove the requested equivalence with `Con(ZFC)` in iPRA.

An [independent audit](../../reviews/aq22-degree10-independent-audit/README.md)
reconstructed the graph and residual identities, confirmed the degree and
positivity argument, and exercised mutation controls. Its scope is finite
computation and ordinary integer reasoning, not Lean derivability.

## Substitution and positivity

In the parent's graph, eliminate these four positive coordinates using the
indicated existing expressions, and delete the corresponding squared binding
residuals:

| Parent coordinate | Expression | Deleted residual |
| --- | --- | --- |
| `cVariable` | `eta + Y * (eta + zeta)` | `cDifference` |
| `productVariable2` | `X * Y` | `product2Difference` |
| `qSquareVariable` | `(1 + beta * J)^2` | `qSquareDifference` |
| `qValueVariable` | `deltaVariable * (f^2 - 1)` | `qSignedDifference` |

These substitutions are simultaneous. Every retained parent residual becomes
the identically named child residual, and every deleted residual becomes zero;
`verify_substitution.py` checks all 17 identities as sparse integer
polynomials, including dependence on all four ports.

This yields the following ordinary integer witness argument, under the
intended condition `beta >= 0` (in the intended specialization it is positive).
A positive zero of the parent projects to a positive zero of the child because
each deleted parent residual is zero. Conversely, at a positive zero of the
child, reconstruct the four coordinates by the displayed expressions. The
first two are positive since their inputs are positive; the third is positive
since `1 + beta * J >= 1`. For the fourth, the retained residual `g72` is
zero, so the expression equals `(cSquareVariable * i)^2`, which is positive.
The reconstructed tuple is therefore positive and makes every parent residual
zero. Both directions use the fact that an integer sum of squares is zero only
when each summand is zero. This argument specifies the intended transport but
has not been formalized in Lean or lifted to an internal iPRA derivation.

## Exact checks

Run the scripts using ordinary, non-optimized Python:

```sh
python3 generate.py
python3 verify_substitution.py
```

The generator pins the parent's graph SHA-256, checks the deleted rows, and
checks size, topological order and liveness. `verify_substitution.py` runs
both parent and child degree checks and verifies the residual identities.
The child checker pins the graph SHA-256
`1266b143c5512351739ea2c71fc8e0b8b0e5cecc599392f128c0803ff78ce106`,
checks the square and sum wiring, and expands residuals exactly. Their maximum
degree in the 22 witnesses is five. The degree-five monomial
`f^2 * y^2 * deltaVariable` has coefficient `-1` in `auxResidual`,
independently of all four ports. The leading sum of squares is therefore
nonzero over the reals, establishing degree exactly 10 even after fixing the
ports; shifting positive coordinates to nonnegative coordinates preserves the
degree. The Python checks deliberately reject `python3 -O`.
