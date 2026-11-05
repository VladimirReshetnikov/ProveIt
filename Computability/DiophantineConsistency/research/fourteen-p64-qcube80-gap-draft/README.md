# Remainder bound for actual 80-candidate zeros

`graph_remainder` proves in Lean that every positive zero of the generated
80-operation graph, at arbitrary natural ports in any indicated IΣ₁ model,
satisfies `v 7 < v 9`: the q³ quotient witness `s` is strictly smaller
than the independent first-root remainder `r0`.

The proof splits the actual five-square equation with an arbitrary first
residual, transports the other four residuals to the lifted package-64
tuple, and extracts both the transport inequality and the main Pell norm.
The transport inequality also forces `beta>0`. The actual reduced first
residual supplies the first Pell norm; the checked model remainder lemma
then gives the inequality. This is the guard needed to set `rho=r0−s`
positive in a possible 80→81 witness map.

The theorem does not itself construct the 81 witness, establish the reverse
existence equivalence, or provide an iPRA endpoint. The source's `Draft`
comment predates the observed check.

## Observed check

On 2026-11-04 Lean 4.32.0 exited 0 under a 180-second bound. The theorem
reported axioms `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`
or warnings. From the repository root, with the prior local objects in `/tmp`:

```sh
LEAN_PATH=/tmp/p64-independent-captured-replay/lib:/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  timeout 180 /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -M4000 -j1 -DElab.async=false \
  --root=Computability/DiophantineConsistency/research/fourteen-p64-qcube80-gap-draft \
  Computability/DiophantineConsistency/research/fourteen-p64-qcube80-gap-draft/P64QCube80Gap.lean \
  -o /tmp/P64QCube80Gap.olean
```

Source SHA-256:
`2f16e7d371f497db9c64adc16490438dc912a9e178369a0477b884e2d2ea6fa4`;
output SHA-256:
`78f59a089ed23816fa9b5c75b4806e9c16b54344ddbcb816b95443b77624f06c`.
Direct local inputs:

```text
P64QCube80.olean              e8829517e10e4c3d2423594dd884b86466834d7714038660030d16861c8abd68
P64QCubeBinding.olean         b0a32668e5e6869e4067d7813b9142ad3465b941cc174452c08579938deda07d
P64NormFirstReplacement.olean da38a424ac91ea386fbe0129b4a700684ebf51e3388ef8c65f1d753f2e25f51e
P64ModelRemainderGap.olean    bb9d8daa37634ddf0a66c6d0dce250f3316c81c6e73891c5829cce58d5ee5460
```

The captured-provider overlay's full transitive source/object, package,
dynamic-library and search-path ancestry was not independently audited.
