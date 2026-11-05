# Evaluated 88 main-root positivity

`main_expression` identifies the expanded difference-ring expression used
by the [negative-branch orientation theorem](../ordinary12-absorb88-negative-main-graph-draft/README.md)
with the evaluation of the actual main-root syntax
`(Absorb89Main.mainParts ...).1`; the 88 and 89 graphs share this main
residual, as shown in the [main-root packet](../ordinary12-absorb88-main-root-draft/README.md).
The `graph_main_root_positive` corollary proves that evaluated register
strictly positive for an actual positive 88 zero with `beta>0` and the
explicit negative-transport hypothesis `ιBp < ιBn`.

The theorem identifies and orients the main root, but does not yet extract
an oriented Pell balance, prove nonnegative rank, normalize transport, derive
an 89 zero, or establish an iPRA endpoint. The source's `Draft` comment
predates the successful check below.

## Observed check

On 2026-11-04 Lean 4.32.0 exited 0 for this module. Both declarations
reported axioms `[propext, Classical.choice, Quot.sound]`, with no
`sorryAx` or warnings. From the repository root, after preparing the checked
local objects:

```sh
TASK_LEAN_PATH=$(python3 -c 'import json; print(json.load(open("Computability/DiophantineConsistency/research/ordinary12-absorb88-signed-divisibility-draft/observations/attempt02/terminal.json"))["lean_path"])')
LEAN_PATH=/tmp:/tmp/absorb89-chain-gpc9zymd/lib:$TASK_LEAN_PATH \
  /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -M3000 -j1 -DElab.async=false \
  --root=Computability/DiophantineConsistency/research/ordinary12-absorb88-main-evaluation-draft \
  Computability/DiophantineConsistency/research/ordinary12-absorb88-main-evaluation-draft/Absorb88MainEvaluation.lean \
  -o /tmp/Absorb88MainEvaluation.olean
```

Source SHA-256:
`f717eb3391260c50d3a6abd2495d4b86ffa9cacb71767ed281c1f0cffffca6e4`;
output SHA-256:
`55a73dfa0857e26f914c103b63d447cc7bbbbf42dd5afd46276a850429897cb6`.
The direct `Absorb88NegativeMainGraph.olean` input hash was
`fcaf153e91fee9d00bf8584044c4cd0747de6c973368e90552bc18c3504c0a77`.
The full transitive source/object, package, dynamic-library, and search-path
ancestry of the temporary providers was not independently audited.
