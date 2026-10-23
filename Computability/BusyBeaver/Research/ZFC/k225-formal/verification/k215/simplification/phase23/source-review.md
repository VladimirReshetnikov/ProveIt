# Phase23 source review

**The production kernel check, independent actual readback, capture and independent
capture review pass.** The baseline is published phase22 at
`017861249e7da624c007e0dd6d170e32433be549`. The final 33-file source map and
canonical bytes match the [independent source peer](integration/source-peer.json).
That receipt and the [source specification](integration/source-spec.json) retain
their original pre-full-run status labels. They are source evidence; the later
[terminal result](lean/result.json) and [actual readback](lean/result-review.json)
establish the accepted full check.

## Complete maintained-file comparison

Zero before lines on a Core row means the file is newly added. Its moved generic
proofs are counted once in the original wrapper row and once in the new Core row;
all wrapper and Core files are included in the totals. Positive byte removal is
a saving; negative removal is growth.

| Source | Before lines | After lines | Bytes removed |
|---|---:|---:|---:|
| `ConstructibleAbs` | 911 | 906 | +195 |
| `DeepPositiveClosure` | 184 | 178 | +355 |
| `FiniteSets` | 163 | 15 | +6,318 |
| `FiniteSetsCore` | 0 | 150 | -6,325 |
| `InductiveAttempts` | 347 | 38 | +15,977 |
| `InductiveAttemptsCore` | 0 | 262 | -12,935 |
| `InternalOrd` | 161 | 155 | +205 |
| `InternalRank` | 457 | 452 | +225 |
| `KEind222` | 320 | 316 | +216 |
| `KLowerQHyp` | 251 | 251 | +15 |
| `KLowerRel` | 87 | 84 | +77 |
| `KLowerTag` | 211 | 203 | +381 |
| `KQ1Basic` | 149 | 137 | +561 |
| `KQ1Replacement` | 142 | 59 | +3,900 |
| `KQ1ZF` | 66 | 66 | -4 |
| `KTableCore` | 39 | 32 | +248 |
| `KTape` | 401 | 398 | +116 |
| `KUpper222` | 239 | 231 | +513 |
| `KZip` | 228 | 226 | +88 |
| `NamedZF` | 166 | 162 | +229 |
| `PositiveClosure` | 183 | 178 | +160 |
| `ProfileAxioms` | 250 | 244 | +331 |
| `ProfilePairs` | 109 | 99 | +503 |
| `RMEquiv` | 672 | 670 | +46 |
| `SingletonInfinity` | 154 | 29 | +6,006 |
| `SingletonInfinityCore` | 0 | 116 | -5,164 |
| `TarskiComplete` | 503 | 505 | +0 |
| `TarskiDerived` | 207 | 196 | +568 |
| `TupleOrder` | 320 | 311 | +363 |
| `WFModel` | 21 | 22 | -38 |
| `WFRelativization` | 166 | 166 | -4 |
| `WellFoundedPart` | 235 | 28 | +9,604 |
| `WellFoundedPartCore` | 0 | 214 | -9,714 |
| **Total** | **7,342** | **7,099** | **+13,016** |

This is a net **243-line / 13,016-byte maintained-source reduction**, including
the attributed upstream work once. The four Core headers and compatibility
adapters are charged to this measure. It is not inferred from a smaller import
closure, proof-object size or elapsed checking time.

The primary `KEndpoint215` closure separately changes from 179 project modules /
1,768,101 bytes to 172 modules / 1,728,487 bytes. It gains the four Core modules
and stops importing eleven generic facades or CP/GIC adapter modules through that
route. Those files remain maintained; the full validation plan still selects
215 project modules plus fifteen typed clients. No module or writer is retired.

## Reused proof mechanisms

The generic split moves the four existing namespace bodies into Core modules and
keeps the old quotient adapters in their original modules. Core consumers such
as `KQ1ZF` and `WFRelativization` import the generic files directly; compatibility
consumers retain the old facade path. This integration deliberately preserves the
phase22 `KLowerQHyp` premise omissions and the `_witness` binder in
`KQ1Basic.interpreted_pair` while adopting the upstream deletions.

The native Replacement proof applies existing formula-indexed quotient Collection
to `fAnd (fMem 0 2) (rename replacementRename phi)`. Its semantic relation is
`qm x a ∧ relOf qm phi env y x`. The domain guard is essential: Collection's support
clause may choose an arbitrary input witness, so the formula must itself require
that input to belong to the requested domain. Renaming uses native `phi`, swaps
its output/input slots and skips the inserted domain parameter. The support
clause proves the image's forward direction. Coverage gives a chosen output `z`,
and the existing global `Functional` premise yields `z = y`, transporting
membership to the requested output. No totality premise or Collection for an
arbitrary semantic relation is introduced.

The two quotient endpoint types and the `replacementRename` definition are exact.
Both native endpoint declarations are byte-identical to reviewed native v1. Six
now-unused raw helpers are deliberately removed rather than retained as an unused
parallel proof. The remaining declarations are `replacementRename`,
`quotient_replacement` and `quotient_repl_form`. The existing 19-module direct
import closure is acyclic.

Eight surviving formula-satisfaction proofs share constructive atom transport:
`sat_attemptForm`, `sat_agreeForm`, `sat_valueForm`, the three singleton semantic
lemmas, and `sat_kpairForm`/`sat_appForm`. Their public types remain exact and no
helper declaration is added. Explicit proposition shapes and existential
predicate/witness arguments repair the rejected elaboration; root's final
`hsz ▸ hv` transports an application witness along `s = singleton B z`.

The larger attempt simplification removes an unnecessary existence resource.
Agreement still proves that Value is functional. `base_attempt` places `a` in
the Value image, and an image witness `f,z,v` extends directly to an attempt
containing `(singleton z,G v)`. Index closure puts the new index in `N`, so the
same image contains `G v`. No proof that every index has an attempt is needed.
Thus `closure_of_instances` drops `hEx`, its caller drops the existence-separator
subgoal, and five unused helpers are retired. `closure_of_forms`,
`successor_closure` and `ordinary_infinity_of_container` keep their exact types.
The construction now uses one agreement Separation instance and one functional
Replacement image, together with the existing finite graph resources.

The direct-extension cut removes 49 lines / 2,486 bytes relative to the first
frozen candidate. The original author's explicit elaboration boundaries add
five lines / 307 bytes; root's final witness transport adds another ten bytes.
The combined revision therefore removes 44 lines / 2,169 bytes beyond v1.
These annotation costs are included in the 33-file totals above. The earlier
25-line ten-body count described v1, including a helper now retired; it is not
an additional final saving. Exact old axiom profiles remain a separate gate.

The warning cleanup keeps all other proof bodies literal: scoped `omit hC hz in`
strengthens only `Tarski.gam_list` and `gam_complete`; four direct applications lose
the redundant arguments. Internal binders in `memD` become `_`, and only the
unused `zc` entry in the second `KZip.step_zc` simp branch is removed. The seven
inherited warning occurrences motivate fresh checking rather than suppression.

## Evidence boundary

The two attributed cherry-picks preserve their upstream commit trailers. Source
censuses cover the deleted declarations, maintained consumers and all fifteen
accepted clients. The independent native review reads every current Lean source
in the four maintained roots and all 221 selected provider/client/audit report
names; none refers to the six retired raw helpers. Historical proposal/report
copies remain provenance and are not compiled as current consumers.

The accepted run checks 230 providers: 199 fresh and 31 exact reuses, plus two
fresh endpoint audits. Fourteen unchanged typed clients and all 25 site/Fwd
batches are fresh. Every provider log and both audits have zero warnings; exact
accepted profiles remain unchanged. Independent actual readback checks 1,259
owner inputs, 146 present pins and sixteen absences. Its 218 present raw provider
records and twelve inherited absences retain their distinct evidence boundaries.

The failed full-v1 prefix and failed mathematical-v1 diagnostic are preserved.
Mathematical-v2 passes 107 fresh modules and is diagnostic only, not a full-run
reuse basis. Its three stale informational byte/line fields remain disclosed in
the source peer: exact source hashes bind the repaired bytes, and the final full
plan has correct counts. The accepted full run uses its own frozen inputs.

Capture and its independent review pass. The 3,389,911-byte archive has SHA-256
`573012336488f152e622798d08f7782ea90310b6dc994864c51c1315f9001dd6`. The version4 reader's alias repair checks live canonical bytes,
archived workspace bytes and historical source labels for all 33 overlays. It
changes the reader alone; the archive, configuration and index are unchanged.
The prior [reader failure](integration/reader-history/failed-review.stderr) is
separate from both compilation failures. The
[reviewed reader](integration/review_capture.py) and
[capture review](integration/capture-review.json) retain their exact bindings.

Phase22's eleven published evidence leaf files remain immutable external history.
The [uncompiled control lead](leads/README.md) is not part of this accepted source
or kernel scope. No state count, checking speedup or internal PA endpoint follows
from the source reduction.
