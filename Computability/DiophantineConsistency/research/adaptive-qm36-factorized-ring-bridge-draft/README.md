# Proposed all-port QM36/153↔155 ring bridge

This source-only Lean draft proposes a pointwise identity between the
[153-operation graph](../adaptive-square-sums36-factored-roots/README.md)
and the 155-operation QM36 graph. The intended theorem quantifies over every
commutative ring, every integer-port tuple and every 36-vector. It contains 27
individual residual comparisons, followed by the equality of their ordered
square sums. Residuals 14 and 15 are the two distributively factored root
bindings. No positivity or beta-representation premise is needed for this
ring identity.

The source then proposes a split-natural zero equivalence and shifted
`SameNoZero` bridge. Its native iPRA client retains the explicit QM38, QM37
and represented-beta QM36 model obligations. The pointwise ring identity and
all later clients remain **unelaborated**; no axioms, provider compatibility or
proof resources have been checked in Lean.

The read-only checker verifies all 27 proposed residual indices against both
pinned generated residual vectors and the authors' exact external polynomial
receipt. Both source and external receipts reproduce; the latter gives
all-port algebraic evidence, not a Lean theorem or formal page binding.

From the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/adaptive-qm36-factorized-ring-bridge-draft/check_source.py | cmp - Computability/DiophantineConsistency/research/adaptive-qm36-factorized-ring-bridge-draft/source-result.json
```
