# Guarded normalization: checked ring identities

`Absorb88NormalizationRing.lean` checks identities over an arbitrary
commutative ring for the actual 88 graph. With `b=J*beta`, `q=1+b`,
`A=K0+w`, `D=q(qA+1)` and old `Bt=−b*u`, the replacement changes

```
F′=F−b*j,  alpha′=alpha−b²*j,
r′=first+(1+k*b)*(D*j−u).
```

The checked lemmas show that the main and ordinary residuals are unchanged,
the new transport is `b*(D*j−u)`, and the new first residual vanishes when
`first` satisfies the first Pell norm. These are ring identities; they do
not establish that the replacements are positive natural-model elements or
that any guard witnesses exist. The later checked
[`Absorb88GuardedNormalization.lean`](README.md) model/89 bridge supplies a
same-port 89 zero under explicit guard hypotheses; it does not establish
those hypotheses for every 88 zero.

On 2026-11-04, Lean 4.32.0 checked the ring module with exit 0; its six
printed declarations depend on `[propext, Quot.sound]`, with no `sorryAx`.
The run emitted numerous unused-simp-argument warnings; the linter was not
suppressed. From the repository root:

```sh
TASK_LEAN_PATH=$(python3 -c 'import json; print(json.load(open("Computability/DiophantineConsistency/research/ordinary12-absorb88-probe/observations/conditional-attempt01/result.json"))["lean_path"])')
LEAN_PATH=/tmp:$TASK_LEAN_PATH /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -M3000 -j1 -DElab.async=false \
  --root=Computability/DiophantineConsistency/research/ordinary12-absorb88-guarded-normalization-draft \
  Computability/DiophantineConsistency/research/ordinary12-absorb88-guarded-normalization-draft/Absorb88NormalizationRing.lean \
  -o /tmp/Absorb88NormalizationRing.olean
```

Source SHA-256:
`a10346f288052cc0081dfd7da3bac872026a334c7471ac0776019c41795b2ce7`;
object SHA-256:
`e9864486b2ed0ed7478b6367405458df92c80f5cb36da9976202ef75058a2bc7`.
The direct `Absorb88First.olean` input SHA-256 was
`1332d8aa708a4f9163451dac1a6e844f3da2623b62d27e4ea952de242d2359fd`.
Temporary provider transitive source/object, package, dynamic-library and
search-path ancestry was inherited and not independently audited.
