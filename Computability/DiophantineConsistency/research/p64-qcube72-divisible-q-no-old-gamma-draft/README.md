# No same-witness old gamma when 3 divides q

`FreeMainDivisibleQNoOldGamma.fixed_no_gamma` proves in any IΣ₁ model: for
an actual positive zero of the 72 graph at the fixed compact44 beta and masks,
with arbitrary natural K and the explicit hypothesis `3|q`, there is no
model element `gamma` satisfying the same-witness old-carrier equation

```
v₁₃+k = Y²*gamma+(R+1).
```

Here `q=p₀v₀+1`, `Y=q³v₇`, `k=v₁₀+v₁₁`, and `R` is the actual graph
rank. Gamma is allowed to be any model element, making the conclusion stronger
than excluding positive gamma. The proof combines the conditional
old-carrier-to-index-equality result with the same-index Pell residue and the
actual-zero theorem `¬(Y²|v₁₃)` under `3|q`.

This does **not** prove that an actual positive zero with `3|q` exists, that
all compact zeros have `3|q`, or that an alternative witness with different
coordinates cannot yield a 76Y zero. It does not disprove existential
reverse implication or establish an iPRA endpoint.

Attempt02 passed with Lean exit 0, stable direct guards, no warnings or
`sorryAx`, and two expected `[propext, Classical.choice, Quot.sound]` axiom
reports. Its direct guarded providers are the conditional old-carrier and
actual-divisible-q obstruction objects. Transitive/dynamic ancestry and sampled
resource monitoring are inherited, so this is not a source-only rebuild. The
source's unchecked-draft header predates this check.

| Artifact | SHA-256 |
| --- | --- |
| `FreeMainDivisibleQNoOldGamma.lean` | `c986b3c588a74730991681805d906e611435915fb54fd81128a4e67779720564` |
| `check02.py` | `d8cd1436fda76ce8517ce1a43bddd86c756695d6e3d62aabbbee6986eec94f66` |
| `observations/attempt02/compile.log` | `b066d7f7b1858fb4d950aff4384fb978b720337c1738a0c067b3bac3c6aa2c32` |
| `observations/attempt02/result.json` | `e3086bb59b11ea022391c038dbc04275045f8aad9bf9f9eb8fbf87ab5f7edbe4` |
| `/tmp/p64-qcube72-divisible-q-no-old-gamma-priority-check02/FreeMainDivisibleQNoOldGamma.olean` | `80d54d2773c0baf82ccadaffef7b2dc70ce551a28d91f6ca53f7ea81d949a528` |

The run used a 2,400 MiB Lean limit, 120-second timeout, sampled 3.5 GiB
process-group RSS limit, minimum 10 GiB available memory, and low CPU/I/O
priority. Attempt01 failed while destructing an unexposed outer let; the
generic helper checked but the client report contained `sorryAx`. Exact
source, runner, log and receipt are retained in `observations/attempt01/`.
