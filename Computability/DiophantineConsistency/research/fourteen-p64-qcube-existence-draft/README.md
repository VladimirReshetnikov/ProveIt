# Positive-zero equivalence for the q³ quotient graph

`positive_zero_iff` proves in Lean that, for **every** natural port tuple
and every indicated model of IΣ₁, the generated `P64QCube81` graph has a
positive 14-tuple zero if and only if the package-64 graph has a positive
14-tuple zero. The graph's new coordinate `s` replaces the old `Y` through
`Y=q³*s`.

The new→old proof lifts the tuple, applies the arbitrary-first residual
split to the candidate's five-square equation, and uses the checked
`A0_old=q⁶*A0_new` identity. The old→new proof extracts a positive quotient
from the old first residual, cancels the nonzero `q⁶`, and transports the
remaining residuals. Both directions are separately named in the source.

This is a model-level existence equivalence for the Lean graph expressions.
It does not by itself establish the iPRA proof-existence endpoint, prove a
PDF rendering corresponds to the graph, or authenticate the full ancestry
of captured providers. The source's `Draft` comment predates the check.

## Observed check

On 2026-11-04, Lean 4.32.0 exited 0 under a 180-second bound, with no warnings
or `sorryAx`. All four printed declarations reported axioms `[propext,
Classical.choice, Quot.sound]`. From the repository root:

```sh
LEAN_PATH=/tmp/p64-independent-captured-replay/lib:/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  timeout 180 /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -M4000 -j1 -DElab.async=false \
  --root=Computability/DiophantineConsistency/research/fourteen-p64-qcube-existence-draft \
  Computability/DiophantineConsistency/research/fourteen-p64-qcube-existence-draft/P64QCubeExistence.lean \
  -o /tmp/P64QCubeExistence.olean
```

Source SHA-256:
`40bea77b56a19feb5b8c3145c0d4f6bb069fafb5885f70d52b6e557b1cd67e08`;
output SHA-256:
`74ef2f50d92729ca37cea7aaa5ea1d21df54eeaa6314aeb0fe5138818f23b8f2`.
Direct local inputs were `P64QCubeBinding.olean`
`b0a32668e5e6869e4067d7813b9142ad3465b941cc174452c08579938deda07d`
and `P64NormFirstReplacement.olean`
`da38a424ac91ea386fbe0129b4a700684ebf51e3388ef8c65f1d753f2e25f51e`.
The captured-provider overlay's full transitive source/object, package,
dynamic-library and search-path ancestry was not independently audited.
