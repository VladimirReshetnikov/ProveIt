# Ninth K215 proof-simplification checkpoint

A single shared Home return theorem now replaces repeated symbolic execution of the leftward scanner. All nine site batches were freshly checked, covering the same 4,751 leaves and 6,176 branch outcomes. Their kernel compilation took **984.608 seconds (16.41 minutes)**; the historical phase-six records total 1,649.340 seconds (27.49 minutes). This is a historical comparison, not a new controlled paired benchmark.

The machine still has 215 working states and 430 actions. Its exact table, source program, and external halting/refutation and nonhalting/ZFC-consistency statements are unchanged.

## Shared proof and exact decoder entry

[`KHome`](../../../../../../../Lean/BusyBeaver/ZFC/KHome.lean) proves the scanner contract for every natural gap, every register list and an arbitrary right frame. Its guard examines the current left segments, including true runs that can disappear at gap zero; it rejects unsupported interior blank runs and boxes. The separate eighteen-step boundary restores the entire tape. [`KHomeReady`](../../../../../../../Lean/BusyBeaver/ZFC/KHomeReady.lean) checks fifteen scan rows and that boundary before enabling the shortcut. A failed table check uses the original stepper. Every accepted shortcut has positive physical progress.

[`KRuntimeCore`](../../../../../../../Lean/BusyBeaver/ZFC/KRuntimeCore.lean) has one executor induction parameterized by its step function. The original executor and theorem remain as instances. An explicit equality client and unchanged KEngine224/KEngine225 clients pass. The readiness controls also show that a broken boundary is rejected even when all fifteen scan rows pass. The unused `sim_stop` parameter was removed after a caller census.

[`KDecoderPrefix215`](../../../../../../../Lean/BusyBeaver/ZFC/KDecoderPrefix215.lean) binds the shared decoder to the literal source and maintained table, then reaches one exact primitive-entry zipper for all gap/register values. The chosen full prefix and control port precede those universal quantifiers. Its clock may be zero; it stops before the primitive action. Seven unused forgetful wrappers were removed, saving 81 lines / 4,858 bytes against the checked prototype. These five auxiliary modules are groundwork for replacing repeated primitive proofs; all existing branch checks remain in the endpoint.

The framing starts with Source178 from `aa66d0a33f`, extended by the later source-path proposal. The HomeReturn proposal supplies the shared return idea; the all-natural guard, concrete boundary, source/role binding and zipper adapters were completed here. Original machine and calculus attribution remains in [K215's notice](../../../../../candidate-k215/NOTICE.md). Draft headers and failed logs retain their original historical status; the accepted receipts identify the checked successors.

## Verification and records

The selected union contains **197 modules**: the **192-module endpoint closure** plus five decoder-prefix modules. Its raw ledger has 20 freshly compiled providers, 13 reused from checked isolated work and 164 reused directly from phase eight. Six of the isolated providers cover changed/new source ancestry; seven carry unchanged earlier providers. All 26 affected source descendants are freshly checked or have exactly matching transitive source/import bindings. Every site batch is fresh.

Both unchanged closed endpoint clients pass, with ten reports using only `propext`, `Classical.choice` and `Quot.sound`, and zero audit warnings. The selected new components have 27 named standard-axiom reports and zero warnings; inherited project logs retain 21 linters. The additional 18-provider executor/control check passes with eight named reports and both legacy engine clients. The earlier five-client legacy audit has the same [46-module source/import closure](legacy-unchanged.json); no new legacy build is claimed.

The [portable evidence packet](lean/README.md) preserves exact sources, commands, raw logs, failed attempts, source peers and independent terminal review. It references the published phase-eight ancestry in place and contains no compiled objects. The first combined run is explicitly rejected: byte-identical intermediary objects had masked a transitive executable-definition change. The accepted successor forces source-dependent recompilation and freshly checks every site. Reproduction from canonical source uses the [serial Lean driver](../../lean/README.md).

| Site batch | Historical phase6 seconds | Phase9 seconds |
|---|---:|---:|
| 000 | 78.535 | 48.620 |
| 001 | 160.262 | 94.881 |
| 002 | 197.897 | 118.682 |
| 003 | 194.844 | 114.857 |
| 004 | 233.858 | 137.511 |
| 005 | 254.056 | 151.881 |
| 006 | 255.667 | 152.618 |
| 007 | 233.871 | 141.270 |
| 008 | 40.349 | 24.288 |
| Total | 1649.340 | 984.608 |

The [timing data](timings.json) bind the raw logs. Fresh site objects are byte-identical to their predecessors; the improvement is reduced kernel conversion work, not a compiled-object size saving. This checkpoint adds shared proof infrastructure. It establishes no smaller machine, lower bound or internal PA endpoint.

The next step is to factor primitive/continuation contracts behind the exact decoder port. A source-only first CB1 suffix design, with 86 literal occurrences and an explicit length guard, is preserved in the packet as uncompiled research. It does not yet replace Boolean coverage.

The [bounded single-use census](next-inlining/README.md) considers fifteen proof files. Four small private inlinings are proposed (335 bytes / nine lines), with retained public statements and executable definitions unchanged in the source comparison. These candidates are uncompiled and the generated core still needs producer synchronization; named invariant and seed-semantic boundaries are retained.
