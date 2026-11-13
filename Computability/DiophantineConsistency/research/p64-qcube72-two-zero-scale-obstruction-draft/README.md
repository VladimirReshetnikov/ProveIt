# Fixed-port two-zero scale obstruction

`FreeMainTwoZeroScaleObstruction.two_zero_no_old_gamma` proves in every IΣ₁
model: for two actual positive 72-graph zeros at the same fixed compact44 beta,
masks and K, if the first has `3|q` and the two have equal `X,Y,c,k`, then
no model element gamma satisfies the old-carrier equation for the second.
The proof identifies the main rank and h through the checked generic scale
rigidity and fixed-port main-index theorems, then applies the checked
same-witness no-gamma theorem to the first zero.

Both zeros and all four coordinate equalities are explicit hypotheses. This
theorem does not assert that either zero exists, involve a 76Y zero directly,
or disprove an existential reverse implication. The separately described
[partial scale swap](../p64-qcube72-scale-swap-partial-normalization/README.md)
remains an external conditional argument until its 76Y application is checked.

Attempt02 passed with Lean exit 0, stable direct guards, no warnings or
`sorryAx`, and the expected `[propext, Classical.choice, Quot.sound]` axiom
report. The source's unchecked-draft header predates the check. Direct
providers are the checked generic scale-rigidity and fixed-port no-gamma
objects. Transitive/dynamic ancestry and sampled monitoring are inherited;
this is not a source-only rebuild.

| Artifact | SHA-256 |
| --- | --- |
| `FreeMainTwoZeroScaleObstruction.lean` | `ed297bb51695c2cf985a945fdd299f3888ee44be603c906373ae3d5c219c24a6` |
| `check02.py` | `66b6f86561e448620211b75532df69d25ccb3a62c72fa4912d7b3777f04512bc` |
| `observations/attempt02/compile.log` | `904506a9114d85b14a96d4d578eaeac81d8c5073885227f8af2371156fc28f52` |
| `observations/attempt02/result.json` | `b123c72d05826febd36924fd04d98e410ed0369452a78c45611b0d2c0c751df0` |
| `/tmp/p64-qcube72-two-zero-scale-obstruction-priority-check02/FreeMainTwoZeroScaleObstruction.olean` | `c4d54c546d6fa15cd0a98434776e0afa2517d766025c32bd8503be37ada9999f` |

The run used a 2,400 MiB Lean limit, 120-second timeout, sampled 3.5 GiB
process-group RSS limit, minimum 10 GiB available memory, and low CPU/I/O
priority. Attempt01 failed on definitional-normalization mismatches, with no
object and `sorryAx` in its report; its source, runner, log and receipt are
retained in `observations/attempt01/`.
