# Conditional X,Y,c obstruction from 72 to 76Y

`FreeMain72To76ThreeScaleObstruction.no_fixed_scale_target` proves in every
IΣ₁ model that the following cannot all hold for the same fixed compact44
beta, masks and natural K:

- an actual positive 72-graph zero and an actual positive 76Y-graph zero;
- the 72 zero has `3|q`;
- their `X,Y,c` values are equal.

Other target coordinates may differ. The proof constructs the checked
76Y-to-72 witness update and exact target old-carrier identity. The checked
actual first-ordinate uniqueness theorem derives equality of k from the
common X,Y,c; the checked two-zero scale obstruction gives the contradiction.
This strengthens the earlier four-value X,Y,c,k result.

Both actual zeros and source `3|q` are explicit assumptions. The theorem
does not prove that such a source zero exists, rule out a target that changes
one of X,Y,c, disprove existential reverse implication, or supply an iPRA
endpoint.

Attempt01 passed with Lean exit 0, stable direct guards, no warnings or
`sorryAx`, and expected `[propext, Classical.choice, Quot.sound]` axioms.
The unchecked-draft source header predates the check. Direct guarded
providers are the 76Y-to-72 forward package, two-zero scale obstruction,
and actual first-ordinate uniqueness object. Transitive/dynamic ancestry and
sampled resource monitoring are inherited; this is not a source-only rebuild.

| Artifact | SHA-256 |
| --- | --- |
| `FreeMain72To76ThreeScaleObstruction.lean` | `47d94b987688def621bd44a3cfa6b93901caba7db3bccfb8d784acb7c971f6fa` |
| `check01.py` | `e3567a92398f98664c61e193aacff69f70d27d8214114aeb89a4a6879a506347` |
| `observations/attempt01/compile.log` | `b9107a0a1791c0b1b5ac384c5a37282259a1a53a23f8376348cc2ee16a437aa8` |
| `observations/attempt01/result.json` | `03a3f965de715b6058b95b1913e74fbf76e9bb045d9db753c083a557c4f6d643` |
| `/tmp/p64-qcube72-to-76-three-scale-obstruction-priority-check01/FreeMain72To76ThreeScaleObstruction.olean` | `c989d12b1a41a9965e0b392a0b625dd9f46724683ca0214bf7083e11044b9de3` |

The run used a 2,400 MiB Lean limit, 120-second timeout, sampled 3.5 GiB
process-group RSS limit, minimum 10 GiB available memory, and low CPU/I/O
priority.
