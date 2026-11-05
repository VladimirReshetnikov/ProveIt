# Signed 88 rank congruence modulo q⁴

`graph_signed_rank_congruence` combines the checked actual-graph q⁵ divisor
with signed factor-three cancellation. In the indicated IΣ₁ models, for an
actual positive 88-graph zero with `beta>0` and the explicit negative
transport hypothesis `ιBp < ιBn`, it proves in the model difference ring

```
q⁴ ∣ (k − rank − 1).
```

The signed rank and all graph registers are defined in the Lean statement.
The proof uses `Y=q³*s` and `H=3+4Y(X+1)`. It does not assert nonnegative
rank, a rank window, early-index equality, an 89 witness, or an iPRA endpoint.
The source's `Draft` comment predates the observed check.

## Observed check

On 2026-11-04 Lean 4.32.0 exited 0; the theorem reported axioms
`[propext, Classical.choice, Quot.sound]`, with no `sorryAx` or warnings.
From the repository root, after building the prior local objects in `/tmp`:

```sh
TASK_LEAN_PATH=$(python3 -c 'import json; print(json.load(open("Computability/DiophantineConsistency/research/ordinary12-absorb88-signed-divisibility-draft/observations/attempt02/terminal.json"))["lean_path"])')
LEAN_PATH=/tmp:/tmp/absorb89-chain-gpc9zymd/lib:$TASK_LEAN_PATH \
  /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -M3000 -j1 -DElab.async=false \
  --root=Computability/DiophantineConsistency/research/ordinary12-absorb88-signed-rank-congruence-draft \
  Computability/DiophantineConsistency/research/ordinary12-absorb88-signed-rank-congruence-draft/Absorb88SignedRankCongruence.lean \
  -o /tmp/Absorb88SignedRankCongruence.olean
```

Source SHA-256:
`3988c507f929a41c9b7b0bca01b9f030a209399661c3778f0f48add56e11cf78`;
output SHA-256:
`d8265fec7e027b457ba69b9d29199092a5ebac6947249705e5be58f96761e88a`.
Direct local input hashes: `Absorb88SignedRankDivisor.olean`
`bafc5ffdfed87779a5eecaf7bbddda3fe1bb0c4f2809ca44fff0ab7d2be0031f`
and `Absorb88SignedCancel.olean`
`943a6d105f7885fe99e53679924800494561c80957cff2c9ad34026ba1a7bf47`.
The full transitive source/object, package, dynamic-library, and search-path
ancestry of the temporary providers was not independently audited.
