# Positive main expression on the 88 negative-transport branch

`graph_main_positive` applies to a positive actual 88-graph zero in the
indicated models of IΣ₁, when `beta>0` and the negative transport hypothesis
`ιBp < ιBn` holds. Using the checked graph-specific rank lower bound and
two-norm gap, it proves strict positivity in the model difference ring of
the explicit expression

```
W*(X+a*(eta+Y*k)) + H*(W*direct-k+rank+1),
```

with the graph registers and signed rank defined in the source. This is the
main-root expression as read from the graph; this module states the explicit
expression and does not contain a separate equality theorem identifying it
with the evaluator of `mainParts`. In particular, it does not yet derive an
oriented main Pell balance, a nonnegative rank, a transport normalization,
the reverse 88/89 implication, or an iPRA endpoint.

## Observed check

On 2026-11-04, Lean 4.32.0 exited 0 and reported theorem axioms `[propext,
Classical.choice, Quot.sound]`, with no `sorryAx`. It reported one warning:
the statement's local let-binding `P` is not explicitly referenced. From
the repository root, with the three preceding local objects in `/tmp`:

```sh
TASK_LEAN_PATH=$(python3 -c 'import json; print(json.load(open("Computability/DiophantineConsistency/research/ordinary12-absorb88-signed-divisibility-draft/observations/attempt02/terminal.json"))["lean_path"])')
LEAN_PATH=/tmp:/tmp/absorb89-chain-gpc9zymd/lib:$TASK_LEAN_PATH \
  /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -M3000 -j1 -DElab.async=false \
  --root=Computability/DiophantineConsistency/research/ordinary12-absorb88-negative-main-graph-draft \
  Computability/DiophantineConsistency/research/ordinary12-absorb88-negative-main-graph-draft/Absorb88NegativeMainGraph.lean \
  -o /tmp/Absorb88NegativeMainGraph.olean
```

Source SHA-256:
`ac1cab154cad9756e331018b1bdb59ced747c2dadb258c7217b75c8e3801dcf7`;
output SHA-256:
`fcaf153e91fee9d00bf8584044c4cd0747de6c973368e90552bc18c3504c0a77`.
The three direct locally built objects were:

```text
Absorb88NegativeMainOrientation.olean ff5b89e1efc90814dc95297166bedf1f19b15cba32022a042acb71cec6debb59
Absorb88NegativeRankBound.olean       7e51595186792e27e68bc9bea5b5b34fe87f01328d723f085d7c40e613c414be
Absorb88GraphGap.olean                4221086c49220f43faaab42cb0159aade3b847c3f9369edc9844e976f820b7f3
```

The full transitive source/object, package, dynamic-library, and search-path
ancestry of the temporary providers was not independently audited.
