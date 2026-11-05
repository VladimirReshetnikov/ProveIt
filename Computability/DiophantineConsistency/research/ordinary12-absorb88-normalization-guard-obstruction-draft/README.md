# Necessary conditions for the b-step normalization guard

In the indicated models of IΣ₁, `guard_requires_large_inputs` proves that
the natural-model portions of the checked
[normalization guard](../ordinary12-absorb88-guarded-normalization-draft/README.md)
force

```
F ≥ 1+b  and  alpha ≥ 1+b².
```

Precisely, from positive `Fnew,anew,t` and
`F=Fnew+b*j`, `alpha=anew+b²*j`, `D*j=u+t`, the proof obtains `j>0`, hence
`j≥1` by model discreteness, and derives both inequalities. It assumes no
graph zero and is therefore applicable to the guard independently of the
other graph constraints.

In particular, a tuple with `F<q=1+b` or `alpha≤b²` cannot satisfy this
specific b-step guard. This is an obstruction to that witness construction,
not a proof such a tuple is a full 88 zero and not a counterexample to an
alternative normalization or 88/89 existence equivalence. Whether the full
88 graph forces the guard's inequalities, or supplies another construction,
remains open. The source's `Draft` comment predates the check below.

## Observed check

On 2026-11-04 Lean 4.32.0 exited 0; the theorem reported axioms
`[propext, Classical.choice, Quot.sound]`, with no `sorryAx` or warnings.
From the repository root:

```sh
TASK_LEAN_PATH=$(python3 -c 'import json; print(json.load(open("Computability/DiophantineConsistency/research/ordinary12-absorb88-probe/observations/conditional-attempt01/result.json"))["lean_path"])')
LEAN_PATH=/tmp:$TASK_LEAN_PATH /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -M3000 -j1 -DElab.async=false \
  --root=Computability/DiophantineConsistency/research/ordinary12-absorb88-normalization-guard-obstruction-draft \
  Computability/DiophantineConsistency/research/ordinary12-absorb88-normalization-guard-obstruction-draft/Absorb88GuardObstruction.lean \
  -o /tmp/Absorb88GuardObstruction.olean
```

Source SHA-256:
`ec82f0aabbf5325e0c2fb2e8dcc8cb75e3961f27d538b48435f83a72e325f6c5`;
output SHA-256:
`43907d46e12d8e2191390c184b56d329780803f770b18587f236e67504f5b236`.
The directly imported `Absorb88Conditional.olean` input hash was
`eb29868c7558f0c5de32b47f5ef926a62890d0dda0be034881dbf1a13100ddb2`.
Full transitive source/object, package, dynamic-library, and search-path
ancestry of the captured providers was not independently audited.
