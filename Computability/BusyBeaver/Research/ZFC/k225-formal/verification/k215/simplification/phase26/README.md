# Phase26: shared arguments in completeness, ranks and satisfaction

**The full Lean kernel build, independent actual readback, evidence capture and
independent archive review pass.** Five proof-only edits
remove **126 lines / 3,711 bytes** against published phase25 commit
`3b9e7eddac0a9edbdbe2df16fe0c35e6b0173b5c`. Imports, computational definitions,
public statements and attributes are unchanged. Two private single-use helpers
are inlined; no helper declaration is added.

Completeness reuses existing context constructors and sentence-renaming
identities. Rank approximations share their symmetric inclusion and extension
arguments. Satisfaction transports the existing semantic clauses through
constructive congruences and decodes truth bits directly. Tape normalization
reuses existing head and tail lemmas. See the [source review](source-review.md).

| Scope | Before | After | Reduction |
|---|---:|---:|---:|
| Five edited files, physical lines | 2,758 | 2,632 | 126 |
| Five edited files, source bytes | 119,134 | 115,423 | 3,711 |
| Primary closure, project modules | 172 | 172 | 0 |
| Primary source bytes | 1,723,955 | 1,720,244 | 3,711 |

These measures overlap and must not be added. [Metrics](integration/metrics.json)
bind the exact sources. The full check covers **230 providers**: 215 project
modules and fifteen unchanged typed clients, with **56 fresh / 174 exact phase25
reuses**, plus **two fresh endpoint audits**. All selected logs have zero warnings;
the exact 93 client / 5 WFTheory / 10 audit reports match. All nine site batches
compile fresh; thirteen boot chunks and sixteen source-forward batches retain
exact phase25 bindings. See the [Lean evidence](lean/README.md),
[actual peer](integration/actual-peer.json) and [archive review](integration/capture-review.json).

Both failed focused elaborations and their narrow repairs are preserved. The
final focused check passes twenty providers, with eleven fresh and nine exact
reuses; it remains diagnostic and supplies no full-run reuse basis.

The eight packets in user commit `56b37bde8b064d852154ad8478d58ec9ab5375d6`
are covered by the [batch219 review](../phase24/follow-ups/batch219/README.md).
The [existing decrement-prefix experiment](../phase25/follow-ups/decrement-prefix/README.md)
passed three literal blocks and remains unadopted. A further proof-only draft
removes five lines / 138 bytes from that prototype; it is uncompiled, captured
as research and excluded from the reduction above.

This succeeds [phase25](../phase25/README.md). The machine remains **215 states**;
the internal PA endpoint and minimum-state theorem remain open. No submitted
checker, generator or supplied proof ran for this checkpoint.
