# Lean ring identities for the 92-operation graph

`QCube92.lean` defines the complete candidate graph as expression syntax and
checks three identities over **every commutative ring**, for arbitrary integer
ports and arbitrary valuations. With `lift` replacing the old `Y` valuation
by `q³s`:

- `first_eval` identifies the old first residual with `q⁶` times the new one;
- `main_eval` and `ordinary_eval` identify the two remaining residuals.

The first identity applies a separately proved seven-operand `scaled_first`
identity, keeping shared subexpressions opaque to the ring tactic. The
recorded axiom reports are `[propext, Quot.sound]` for `first_eval` and
`[propext]` for each later identity. These are Lean metatheory axioms, not
axioms of the candidate arithmetic theory. No `sorryAx` or warning occurs in
the accepted run. These are ring identities, not yet a zero-existence theorem
or an iPRA derivation.

The bounded author-side `attempt05` took 6.2 seconds and exited 0. Its source
and runner SHA-256 hashes are respectively
`d79cdacdeb36d6d080d71284b501d651be80312ae85edb43c270f5360244e8aa` and
`76c2e30af23b71b626bd7e0e36032324f347bd6c8f317bd607d59b18cfc45910`.
The runner records source, graph, checker and binary hashes before and after,
as well as 74 selected provider-file hashes. Those files were unchanged. The
selected inventory follows the runner's filesystem traversal and is **not** a
complete transitive provider or package inventory, especially across symlinked
directories. The existing imported `FreeJSumSquares` object and historical
package and dynamic ancestry remain inherited. Three samples saw at most one
Lean process and at least 18,501,092 KiB MemAvailable; sampling cannot rule
out shorter overlaps or memory dips. This is one author build, not a peer
replay or an iPRA theorem.

The first attempt reached its 180-second cap; attempts 02–04 failed because
of unresolved expression, finite-index and cast simplifications. Exact source
snapshots, logs and receipts are retained under `observations/attempt01/`
through `attempt05/`. The successful proof retains a local setting that
suppresses unused `simp` argument lints; the accepted log has no warnings.

`check_lean_graph.py` independently parses the Lean graph's 12 variable
indices, four port indices, all 92 operations and its four projections against
`candidate.json`; three mutations are rejected. Its output is retained in
`observations/graph01/stdout`. This is a narrow external source check, not a
Lean theorem interpreting JSON, TeX or PDF.

To repeat, choose an unused attempt number and preserve the recorded provider
paths:

```sh
ATTEMPT=attempt06 python3 run.py
python3 -I -S -B check_lean_graph.py
```
