# Gap from the first and main Pell norms

`Absorb88TwoNormGap.gap` proves the following inside Lean for the indicated
models of IΣ₁. Let `P=XY²`, with `X,Y,eta,zeta>0`, `k=eta+zeta`, and suppose
both displayed equations hold for model elements `tau,g`:

```
tau² = 1 + P(P+1)k²
g²   = 1 + delta(XY+Y)(eta+Yk)².
```

Then `k ≥ 8P+4`. The first Pell classification writes
`k=2*ycoord n B` with `B=2(P−1)+1=2P−1`. The library's unit abscissa is
`B+2=2P+1` (not `B`), and `ycoord 2 B=2(B+2)`. If `n=1`, then `k=2`
and positivity forces `eta=zeta=1`. The main ordinate would be `2Y+1`,
strictly between its first two positive Pell ordinates `1` and
`2(XY+Y+2)`, a contradiction. Thus `n≥2` and the stated bound follows.

This theorem explicitly assumes both norms; it does not itself extract
the main norm from an 88-graph zero. That graph binding is separate work.
It does not establish transport positivity, the reverse 88/89 implication,
or an iPRA endpoint.

## Observed check

On 2026-11-04, Lean 4.32.0 exited 0 and reported dependencies
`[propext, Classical.choice, Quot.sound]`, with no `sorryAx`. The command was
run from the repository root:

```sh
TASK_LEAN_PATH=$(python3 -c 'import json; print(json.load(open("Computability/DiophantineConsistency/research/ordinary12-absorb88-signed-divisibility-draft/observations/attempt02/terminal.json"))["lean_path"])')
LEAN_PATH=/tmp:$TASK_LEAN_PATH /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -M3000 -j1 -DElab.async=false \
  --root=Computability/DiophantineConsistency/research/ordinary12-absorb88-two-norm-gap-draft \
  Computability/DiophantineConsistency/research/ordinary12-absorb88-two-norm-gap-draft/Absorb88TwoNormGap.lean \
  -o /tmp/Absorb88TwoNormGap.olean
```

Source SHA-256:
`d82f02bd4c6fd8f1b51d6e72b8f3868ed382768c840762936936b7f47ca7027d`;
output SHA-256:
`ff1f89e6c669f00370641823a9a0f6c841eb0411ecb7db1d225d10efc04c5536`.
The imported `ArithmeticPellFirstIndex.olean` hash was
`20d3769d891a42810c1985203768b122bf936884494d2829415e3140d6deb9c2`.
The check inherits temporary prebuilt providers; their complete project,
package, dynamic-library and search-path ancestry was not audited.
