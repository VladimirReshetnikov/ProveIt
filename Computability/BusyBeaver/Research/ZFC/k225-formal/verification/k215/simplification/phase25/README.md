# Phase25: concise calculus, simulator and absoluteness proofs

**The full Lean kernel build, independent actual readback, evidence capture and
independent archive review pass.** Five proof-only edits remove **101 lines /
2,322 bytes** against published commit `593c05920f751e6696fd2bc9bb583225b128f359`.
Imports, computational definitions and public statements are unchanged.

The calculus reuses existing context lemmas and renaming equations. The simulator
extracts successful optional executions directly and simplifies residual-time
arithmetic. Tape scans normalize their endpoints in place; peeling shares its
constructor elimination. Constructible absoluteness transports the existing
function-on-domain property once instead of rebuilding its three fields.
No helper declaration is added. See the [source review](source-review.md).

| Scope | Before | After | Reduction |
|---|---:|---:|---:|
| Five edited files, physical lines | 2,452 | 2,351 | 101 |
| Five edited files, source bytes | 112,526 | 110,204 | 2,322 |
| Primary K215 closure, project modules | 172 | 172 | 0 |
| Primary selected source bytes | 1,726,277 | 1,723,955 | 2,322 |

These measures overlap and must not be added. [Metrics](integration/metrics.json)
bind the exact sources. This succeeds the accepted [phase24 checkpoint](../phase24/README.md).

The full check covers **230 providers**: 215 project modules and fifteen unchanged
typed clients, with **110 fresh / 120 exact phase24 reuses**, plus **two fresh
endpoint audits**. All selected logs have zero warnings; the exact 93/5/10 reports
match. The observed outer duration is **1,330.62 seconds**, not a speed comparison.
The [actual readback](lean/result-review.json) checks 1,259 owner inputs,
111 present pins and sixteen absences, with 227 raw records and three disclosed
inherited absences. The [Lean evidence](lean/README.md) records the full bindings.

The direct calculus probes find an improvement: **`cons_sub` is now axiom-free**,
dropping `propext`; six other ordered profiles are identical. The strict equality
comparison remains a recorded FAIL. A [separate readback](integration/calculus-profiles/reduction.json)
verifies exactly that reduction without recompilation or changes to the full
profile gates. The failed first focused elaboration and its two repairs are retained.

The [batch219 review](../phase24/follow-ups/batch219/README.md) covers all eight
proposals in commit `56b37bde8b064d852154ad8478d58ec9ab5375d6`. Its
[decrement-prefix experiment](follow-ups/decrement-prefix/README.md) now compiles
and passes three literal blocks: baseline **19.46s**, shared prefix **17.03s**,
in one ordered sample. It adds 36 lines / 1,580 bytes and changes the computational
checker, so it remains unadopted and is excluded from the 101-line reduction.

The literal machine remains **215 states**. The internal PA endpoint and minimum-state
theorem remain open. No incoming checker, generator or supplied proof was executed.

The [phase26 proof cleanup](../phase26/README.md) continues from this frozen
checkpoint, removing 126 lines / 3,711 bytes across five proof files. Its full
kernel build, independent actual readback, capture and archive review pass;
this phase25 eleven-file Lean leaf remains unchanged.
