# Phase24: shared runtime, selector and semantic proofs

**The full serial Lean kernel check, independent actual readback, capture and
independent capture review pass.** This continues the published
[phase23 checkpoint](../phase23/README.md) at
`3b5376377b0a282d225675550437f4aae8c5e7f8`. The literal 215-state machine and
its halting/nonhalting endpoint statements are unchanged.

The change combines four bounded proof cuts:

- Attributed runtime cleanup shares constructor elimination, matching branches
  and existing reachability steps in `KRuntimeCore`, `KZip` and `KBoot`.
- Four program-parametric selector lemmas in `L2Lib254` replace repeated dispatch
  constructions in the 254/222 roots; the seven Dom/Perm helper names remain wrappers.
- Existing subtype and well-founded semantic transports replace repeated witness
  bookkeeping; the private duplicate `raw_rel_iff` is removed.
- The calculus reuses `update_comm`, `Kalmar.cases_on` and the existing top-bound
  theorem instead of repeating local reasoning or formula induction.

Claude's upstream `303ecd816c89021f29ae88084545a63bc785c893` is integrated by
attributed `-x` cherry-pick `1b30c178dd01a20957c7260fee74cfc7c3b842bb`, retaining
Vladimir Reshetnikov's author and Claude coauthor trailers. Its three-file physical
reduction is 31 lines; the historical commit message's conflicting net line is
not used for the combined measure.

## Final frozen source measures

| Scope | Phase23 basis | Frozen final source | Reduction |
|---|---:|---:|---:|
| All 13 maintained files, physical lines | 3,000 | 2,825 | 175 |
| All 13 maintained files, source bytes | 131,004 | 122,569 | 8,435 |
| Primary K215 endpoint, project modules | 172 | 172 | 0 |
| Primary selected source bytes | 1,728,487 | 1,726,277 | 2,210 |

The maintained measure charges the shared library, retained wrappers and six
explicit WF annotation lines costing 298 bytes. The primary closure is a
separate overlapping measure; the two savings must not be added. The selector
cut alone grows the primary path by 1,509 bytes while reducing other maintained
roots. The combined final batch reduces the primary bytes above. See the
[source review](source-review.md) and [compatibility notes](compatibility.md).

The full run checks **230 providers**: 215 project modules and fifteen unchanged
typed clients, with **121 fresh providers / 109 exact phase23 reuses** and **two
fresh endpoint audits**. Eleven clients, nine site batches and thirteen boot
chunks compile fresh; all sixteen source-forward batches retain exact phase23
bindings. The run takes **1,307.98 seconds**, an observed duration rather than
a comparative speedup. All selected provider and audit logs have zero warnings;
the exact 93/5/10 profiles match. The [actual readback](lean/result-review.json) checks 1,250 owner inputs,
102 present pins and sixteen absences. It binds 218 adjacent raw provider records
and twelve disclosed inherited absences; no record is fabricated.

The [terminal result](lean/result.json) has SHA-256
`c9bcee3023ea879ad0dcc353d1435aae8aef92963a4b79f51fda1506f518c910`.
The deterministic [capture](lean/capture.json) passes for **640 blobs, 1,078 logical
entries, 1,071 source aliases and 611 raw evidence files**. The archive is
**1,828,563 bytes**, SHA-256
`09d3ee5d9a8d7fba84e0ac0ee7c25af034a758c19f16a69d2b554542056b1ed5`.
The [independent capture review](integration/capture-review.json) passes.
Phase23's eleven exact external Lean leaves remain immutable; executable proof
objects are not shipped.

The first focused plan was rejected for row order before any compiler ran.
Focused-v2 and native-diagnostic-v1 then failed at separate WF inference seams.
Explicit subtype and raw Sat annotations complete the same proof mathematics;
native-diagnostic-v2 passes sixteen providers, two fresh and fourteen exact
phase23 reuses, in 2.74 seconds. No diagnostic is full endpoint acceptance or a
reuse basis. See the [Lean evidence](lean/README.md) for receipt and runtime bindings.

The separate new batch219 review of commit
`56b37bde8b064d852154ad8478d58ec9ab5375d6` reads proposal sources and historical
evidence only. It is outside these thirteen checked sources; this phase does not
claim to compile or adopt its future control or scheduler leads.

The literal 215-state machine and halting/nonhalting statements remain unchanged.
The internally encoded PA endpoint, minimum-state theorem and uncompiled
[control lead](../phase23/leads/README.md) remain outside this proof-cleanup scope.
