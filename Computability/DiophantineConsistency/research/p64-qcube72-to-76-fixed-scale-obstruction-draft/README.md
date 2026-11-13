# Conditional fixed-scale obstruction from 72 to 76Y

`FreeMain72To76FixedScaleObstruction.no_fixed_scale_target` proves in every
IΣ₁ model that the following cannot all hold for the same fixed compact44
beta, masks and natural K:

- an actual positive 72-graph zero and an actual positive 76Y-graph zero;
- the 72 zero has `3|q`;
- their `X,Y,c,k` values are equal.

Other target coordinates may differ. The proof reconstructs the checked
76Y-to-72 update and exact target old-carrier identity, then applies the
checked two-zero scale obstruction. It does **not** prove that a source 72 zero
with `3|q` exists, rule out a target that changes one of the four values, or
disprove the existential reverse implication. It is not an iPRA endpoint.

Attempt01 passed with Lean exit 0, stable direct guards, no warnings or
`sorryAx`, and the expected `[propext, Classical.choice, Quot.sound]` axiom
report. The unchecked-draft source header predates the check. Direct guarded
providers are the 76Y-to-72 forward package and two-zero scale obstruction.
Transitive/dynamic ancestry and sampled monitoring are inherited; this is not
a source-only rebuild.

| Artifact | SHA-256 |
| --- | --- |
| `FreeMain72To76FixedScaleObstruction.lean` | `5ddc1fbd656e2ad92c32c3db8c8bc474dba563854f43fb94cf80a5b873e5263c` |
| `check01.py` | `74336a37f4dda2acaad3d38280327649bd6d4d8c749989a1aff1abc0b41d6d35` |
| `observations/attempt01/compile.log` | `0d9017aacb657fed9f10467132691b26fe65b41925c6ed99928eb6f133c25349` |
| `observations/attempt01/result.json` | `9468a7a98cbb2c755f3209303bc793fae65f3fc15ad4377762065ea5864edeaa` |
| `/tmp/p64-qcube72-to-76-fixed-scale-obstruction-priority-check01/FreeMain72To76FixedScaleObstruction.olean` | `a64cc4b23331213e9d8d9440e8ffd0ca7254199cfa7c9842c0c4141347f49b43` |

The run used a 2,400 MiB Lean limit, 120-second timeout, sampled 3.5 GiB
process-group RSS limit, minimum 10 GiB available memory, and low CPU/I/O
priority.
