# Conditional old carrier forces the first-index equality

`FreeMainConditionalOldCarrier.index_eq_of_witness` proves in any IΣ₁ model
that `2n=R+1`, assuming `n<R`, `R+1<mu`, `mu>0`, `U=e*mu`, `mu|h`,
`k=2n+4(XU)*s`, and the explicit same-witness old-carrier equation

```
h+k = U*gamma + (R+1).
```

It derives the needed congruence from these assumptions; it does not assume
it. `fixed_of_witness` obtains the other premises from an actual positive
72-graph zero at the fixed compact44 beta and masks, with arbitrary natural K,
and retains the first Pell-coordinate identities for the same `n`. Its
`gamma` and the old-carrier equation remain **explicit caller inputs**. The
theorem does not prove that a suitable `gamma` exists, nor any reverse
witness map, 72-equation equivalence or iPRA endpoint.

Attempt02 passed with Lean exit 0, stable direct guards, no warnings or
`sorryAx`, and two expected `[propext, Classical.choice, Quot.sound]` axiom
reports. The source's unchecked-draft header predates the check. The direct
providers are the same-zero fixed-compact cancellation object and the
captured `P72Exact` object; the closing arithmetic was inlined from the source
because `index_close` was unavailable under the attempted captured name.
Transitive/dynamic ancestry and sampled resource monitoring are inherited;
this is not a source-only rebuild.

| Artifact | SHA-256 |
| --- | --- |
| `FreeMainConditionalOldCarrier.lean` | `a9cd0475ef4eab492a974fd37fc93c8752b1571be59ac7c50bf0aeabdf995cf6` |
| `check02.py` | `e7ad76681a0069160123d8ce7b4b7e5e0f36d0af9cf6b717e5e8951985998bd5` |
| `observations/attempt02/compile.log` | `f7b48d86639955508309172d48fdd7ed3f45948868be0b6a15e263ff425c7aca` |
| `observations/attempt02/result.json` | `e6349811f43aa395de6058b1771a1e5a6f4fdd12b41a18fd9927e003901f7183` |
| `/tmp/p64-qcube72-conditional-old-carrier-priority-check02/FreeMainConditionalOldCarrier.olean` | `cf77a2a51742d9dc22e20d2e766df715d4318557848602bb2790466feb82fa2e` |

The run used a 2,400 MiB Lean limit, 120-second timeout, sampled 3.5 GiB
process-group RSS limit, minimum 10 GiB available memory, and low CPU/I/O
priority. Attempt01 failed on unavailable names and produced no object;
its report contains `sorryAx`. Its exact source, runner, log and receipt are
retained under `observations/attempt01/`.
