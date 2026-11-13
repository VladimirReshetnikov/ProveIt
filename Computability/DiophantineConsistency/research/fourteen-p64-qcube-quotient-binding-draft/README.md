# Residual binding for the generated q³ quotient graph

`P64QCubeBinding` checks, over any commutative ring, the generated
`P64QCube81.graph` against the actual package-64 graph at the valuation
where its `Y` coordinate is replaced by `q³*s`. The old `A0` evaluation is
`q⁶` times the candidate `A0` evaluation; the `M`, `W`, `Na`, and `Lt`
evaluations are equal. It also checks the candidate output's five-square
shape. The ring statements use the actual Lean graph definitions; they do
not prove zero-existence equivalence, a machine-halt bridge, or an iPRA
endpoint. The source's `Draft` comment predates this check.

## Observed checks

On 2026-11-04 Lean 4.32.0 compiled the generated graph, exit 0 with empty
output, as recorded in [CANDIDATE_CHECK.md](CANDIDATE_CHECK.md). It then
compiled this binding, exit 0 with no warnings or `sorryAx`:

```sh
LEAN_PATH=/tmp/p64-independent-captured-replay/lib:/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  timeout 120 /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -M4000 -j1 -DElab.async=false \
  --root=Computability/DiophantineConsistency/research/fourteen-p64-qcube-quotient-binding-draft \
  Computability/DiophantineConsistency/research/fourteen-p64-qcube-quotient-binding-draft/P64QCubeBinding.lean \
  -o /tmp/P64QCubeBinding.olean
```

`first` reported axioms `[propext, Quot.sound]`; the other five declarations
reported `[propext]`. Source SHA-256:
`011131e97aa31b0a6837d95344f81c0bd22b0d8ca8389ee161caddc2db5853cd`;
output SHA-256:
`b0a32668e5e6869e4067d7813b9142ad3465b941cc174452c08579938deda07d`.
Direct locally compiled inputs were `P64QCubeMap.olean`
`e5a9328375384611b092c1cf29bcf3b8e317c4c0a85c0665b439ff97af148fa3`
and `P64QCube81.olean`
`f2b88d807ac99ebfa8a73b25ed354a302b93a35f53eda9816b3c842502b7a64f`.
The captured-provider overlay's full transitive source/object, package,
dynamic-library and search-path ancestry was not independently audited.
