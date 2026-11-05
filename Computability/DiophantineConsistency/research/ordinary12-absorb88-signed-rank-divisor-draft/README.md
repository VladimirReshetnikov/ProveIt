# Signed rank divisibility from the 88 negative-branch main balance

`graph_signed_rank_divisor` applies to the indicated models of IΣ₁, an
actual positive 88-graph zero, `beta>0`, and the explicit negative-transport
hypothesis `ιBp < ιBn`. With the signed rank and graph registers defined in
the Lean statement, it proves in the model difference ring

```
q⁵ ∣ H * (k − rank − 1).
```

It uses the checked oriented main balance and the identity `W=q⁵*s`; the
quotient is explicitly constructed in the difference ring. It does **not**
yet cancel `H`, show `q⁴ ∣ k−rank−1`, establish a rank window, construct an
89 zero, or provide an iPRA endpoint. The source's `Draft` comment predates
the successful check recorded below.

## Observed check

On 2026-11-04 Lean 4.32.0 exited 0 and reported axioms `[propext,
Classical.choice, Quot.sound]`, with no `sorryAx` or warnings. From the
repository root, with prior checked objects available in `/tmp`:

```sh
TASK_LEAN_PATH=$(python3 -c 'import json; print(json.load(open("Computability/DiophantineConsistency/research/ordinary12-absorb88-signed-divisibility-draft/observations/attempt02/terminal.json"))["lean_path"])')
LEAN_PATH=/tmp:/tmp/absorb89-chain-gpc9zymd/lib:$TASK_LEAN_PATH \
  /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -M3000 -j1 -DElab.async=false \
  --root=Computability/DiophantineConsistency/research/ordinary12-absorb88-signed-rank-divisor-draft \
  Computability/DiophantineConsistency/research/ordinary12-absorb88-signed-rank-divisor-draft/Absorb88SignedRankDivisor.lean \
  -o /tmp/Absorb88SignedRankDivisor.olean
```

Source SHA-256:
`e195cdf903fd5ba00594dab3424b1a5221fa06c19ba83bf5b0127cd9c777519f`;
output SHA-256:
`bafc5ffdfed87779a5eecaf7bbddda3fe1bb0c4f2809ca44fff0ab7d2be0031f`.
The direct `Absorb88MainBalance.olean` input SHA-256 was
`ec231619db9f3830626678b9d553bbaa5b6727f73443fd2afa8e2ff514026267`.
The full transitive source/object, package, dynamic-library and search-path
ancestry of the temporary providers was not independently audited.
