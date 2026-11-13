# Package 64 q³ quotient-coordinate map

`P64QCubeMap` checks the model and ring steps for replacing the positive
`Y` input of package 64 by a positive quotient `s`, with `Y=q³*s`:

- `lift_pos` preserves positivity under the substitution.
- `quotient_of_first_zero` extracts a positive `s` from an actual positive
  package-64 valuation whose `A0` residual vanishes, and proves the lifted
  tuple equals that valuation. This uses the existing `P64Root.first_root`.
- `first_factor` proves over every commutative ring that the actual old
  `A0` at the lifted valuation equals `q⁶` times the reduced first residual
  `(ell+rho+s)²−(ell(ell+k)+1)`.
- `lift_cast` identifies the natural-model lift after embedding with the
  corresponding commutative-ring valuation.

These statements do not themselves bind the generated 81-operation graph,
prove its zero-existence equivalence, or give an iPRA endpoint. The source's
`Draft` comment predates the successful check below.

## Observed check

On 2026-11-04 Lean 4.32.0 exited 0 under a 120-second timeout, with no
warnings or `sorryAx`. `first_factor` reported axioms `[propext, Quot.sound]`;
the other three declarations reported `[propext, Classical.choice,
Quot.sound]`. From the repository root:

```sh
LEAN_PATH=/tmp/p64-independent-captured-replay/lib:/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  timeout 120 /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -M4000 -j1 -DElab.async=false \
  --root=Computability/DiophantineConsistency/research/fourteen-p64-qcube-quotient-map-draft \
  Computability/DiophantineConsistency/research/fourteen-p64-qcube-quotient-map-draft/P64QCubeMap.lean \
  -o /tmp/P64QCubeMap.olean
```

Source SHA-256:
`20bd2cc8803cea1b7b088b9150341045679076141f007c205aff2c1e92c49916`;
output SHA-256:
`e5a9328375384611b092c1cf29bcf3b8e317c4c0a85c0665b439ff97af148fa3`.
The direct `P64Root.olean` input hash was
`0a7b84ca9683c1903b9189c3792ce90d9fc8b7562ce873888d1eb664136b89b3`.
The captured-provider overlay's full transitive source/object, package,
dynamic-library and search-path ancestry was not independently audited.
