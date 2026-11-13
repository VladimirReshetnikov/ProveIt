# Bounded one-gate screen for the current 13-variable frontier

This deterministic source-only screen found no identity in the precise rewrite
class below for the three pinned current-port circuit graphs:

| Graph | Eligible target/predecessor pairs | Ordered replacement expressions | Survivors of all eight vectors |
| --- | ---: | ---: | ---: |
| 86/56 positive-ordinate product | 63 | 1,115,313 | 0 |
| 87/36 positive-ordinate four-square | 64 | 1,154,562 | 0 |
| 88/30 four-square | 64 | 1,163,244 | 0 |

The notation describes the cited graphs' externally recorded operation counts
and degrees; this packet does not re-prove those degree or endpoint claims.

For every target operation, choose one **direct predecessor operation whose
only consumer is that target**. Consider replacing the target with one `+`,
`−`, or `*` operation applied to an **ordered pair** of earlier available
witnesses, formal ports, operation wires or literal constants 0–4, excluding
the predecessor to be deleted. Each such expression must equal the original
target as a polynomial in **all** witness and port variables. A discrepancy
at even one explicit assignment modulo the prime 1,000,003 proves that an
integer polynomial identity cannot hold. Thus the zero survivor count rules
out every candidate in exactly this enumerated class, not merely with high
probability. All eight assignments for every graph are stored explicitly in
`vectors.json`; the checker validates their dimensions and range.

The checker counts the full ordered search but avoids evaluating every triple
at all eight vectors. It indexes each permitted second operand by its first
coordinate and solves the field equation for each first operand and operator;
it explicitly handles a zero multiplier. An independent brute-force
first-coordinate enumeration checks five eligible pairs per graph, plus two
synthetic controls covering a zero multiplier. For the 86 and 88 graphs the
first vector refutes every candidate. Four expressions across two 87-graph
pairs survive the first vector, but the second refutes each; their exact
replacement triples and counterexample index are recorded in the receipt.
Per-pair enumeration counts are also recorded.

This search does **not** cover arbitrary literal constants, more than one
remaining replacement operation, removal of an operation without this
exclusive direct-predecessor pattern, changes to witness coordinates, claims
only at the fixed current tuple, or transformations preserving only zeros.
In particular it does not prove an operation lower bound, graph optimality,
nonexistence of a different Pareto improvement, a Lean theorem, or an iPRA
endpoint. The finite-field calculations and graph pins are external evidence.

Run from `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/current2011-frontier-one-gate-screen/check.py | cmp - research/current2011-frontier-one-gate-screen/receipt.json
```

No Lean, build, staging or historical-source edits were performed.
