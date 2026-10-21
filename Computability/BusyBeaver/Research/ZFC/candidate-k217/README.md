# K217: 217 working states for ZFC consistency

**Accepted after five selected fresh checks passed.** The exact table and full blank-start result were accepted at the ordinary reviewed mathematical-proof level.

The exact binary machine below has **217 working states and 434 transition rows, including blank initialization**, with a separate halt. Its reviewed ordinary proof, composed with the pinned inherited numerical-calculus calibration, establishes

```text
ZFC proves: not Halt(K217, blank) ↔ Con(ZFC).
```

This is the accepted 217-state predecessor. The new [primary K216](../candidate-k216/README.md) retains this fold and adds a partial-selector reduction; the continuing target is **215 or fewer working states**. The statement is an equivalence proved by ordinary mathematics formalizable in ZFC; it does not assert unconditional nonhalting, a minimum-state bound, or a newly compiled exact-table Lean/Rocq or internal PA endpoint.

## Exact machine

- [Canonical table](k217.tm): initial state 0, working labels 0–216, halt 217.
- [Native table](k217.native.tm): inherited labels, initial state 0, dispatcher 84, halt 254.
- [Canonicalization](canonicalization.json): complete native-to-canonical bijection.
- [Complete source](sites217.json): 4,751 primitive occurrences, 203 distinct subtrees, depth 45, maximum zero run 6.
- [Rotated 218-state intermediate](unfolded218.native.tm), [proof exposition](proof.md), and [provenance](provenance.json).

The convention is a deterministic two-symbol machine on one two-way infinite tape, initially all zero, with the head at position 0 and only L/R moves. Every noncomment table row is `state read write direction next`. The distinguished halt has no outgoing rows and is excluded from the working-state count.

| Artifact | SHA-256 |
|---|---|
| Canonical table | `522a71c067afe8862c9aab98e0f7f93eac747f5ef91d26bd3568760e1c1c478f` |
| Native table | `b235f7d0403460ff00d274d7d030fec6ba3562127035165e3ead555237c83088` |
| Source | `9eac900e83742470893ea433cb0868e9ff6296f905cd6f3359b7a2c0e3114655` |

## What saves the state

The immediate parent is the [dominated-rho8 K218](../candidate-k218/alternatives/dominated/README.md), whose numerical axiom restriction and 203-subtree source are inherited. Three closed source reassociations expose native state 213 as a selector with branches `0 R 92` and `1 R 90`. States 69 and 400 share their read-one branch; their unique incoming transitions write different origin bits immediately left of the head. Rereading that bit selects the old zero continuation in exactly three steps, preserving the complete tape and head at the endpoint.

This removes state 400, adds no state, and changes nine retained rows relative to the parent. The source's entire primitive word and guarded ordinal control graph remain equal. The final local merge also has a separate all-initial-tape theorem from state 0, with positive one- or three-step matching blocks. This is a new physical reduction of the dominated layout, not a direct patch to the earlier primary K218.

## Verification and reproduction

All five selected fresh leaves passed on the exact released bytes: deterministic reconstruction, independent source/fold audit, independent blank audit, independent local-fold checker, and full quantified runtime. The [actual-record review](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake192-fresh/actual-review.json) confirms that every regenerated ordered runtime case equals its delivered counterpart; only the runtime timing field differs.

| Obligation | Exact scope/result |
|---|---|
| Reconstruction | Three rotations, nine retained-row changes, delete 400, exact source/native/canonical bytes |
| Independent source/fold audit | Full guarded CFG and expected decoder-role relation; both origin markers and positive complete-tape blocks |
| Blank startup | 312,617 transitions, native dispatcher 84 / canonical 83, head −5, gap 80 |
| Complete startup frame | Registers `[3,0,0,0,3,0,0,0,0]`, 130 one-valued spare blocks, exactly 277 one cells and zero exterior |
| Independent window fold | 962,479 inductive contexts, arbitrary initial tapes, corrupt initial halt rejected |
| Quantified primitive runtime | 6,176 cases, 1,616,558 symbolic rules, all 434 rows, minimum duration constant 13 |

The runtime domain contains independent arbitrary natural register values and gaps and an arbitrary nonempty finite list of natural spare values. Literal transitions, unary induction and finite-list induction produce complete tape endpoints. The 4,000-rule cap bounds construction of a case derivation; it does not bound the represented register values, list lengths or concrete running time. Positive durations are needed to relate infinite source and binary executions.

The blank audit independently recomputes the whole prefix with sparse and dense interpreters, then checks the canonical presentation and the complete expected support. In this fresh invocation it compares **zero stored trace rows**: there is no stored full-trace input. Its 312,617 newly computed transitions and trace digest are recorded separately.

The [five-leaf actual record](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake192-fresh/actual.json), [source/fold result](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake192-fresh/source-fold.json), [blank result](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake192-fresh/blank.json), [window-fold result](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake192-fresh/fold-window.json), [runtime result](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake192-fresh/runtime/runtime.json), and [compressed ordered case receipts](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake192-fresh/runtime/runtime_cases.json.gz) retain the exact fresh evidence. See the [recovery and reproduction guide](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-192-reproduction.md) for the selected commands and preserved raw logs. Those five leaves do not replay the manifest wrapper, parent suites, logical certificate, broad searches or proof-assistant builds; the separately accepted [Source149 evidence](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake191-source149/actual.json) supplies the inherited logical/source predecessor.

## Independent corroboration and provenance

An independently authored reconstruction by `opening_encoder` found the same source among 48 closed variants and a 217-state table equal under the label cycle `188→213→210→188`. Its full source/decoder/fold checks and complete startup are preserved in [the separate research packet](research/independent-helper-reconstruction/README.md). That result corroborates this construction; it supplies neither a second state saving nor a second full primitive-runtime replay.

Source152 arrived as `K217_Dominated_Continuation_2026-10-20.zip` in commit `8a1796545e`; its inspected upstream snapshot was `704b87442afbd571833a628cd558f1d207fd8b2f`. The exact dominated parent archive has SHA-256 `080b4fe855c109ab77588c01c9e012d9572afa7721682306370ccb2eb22cbea9`. [Intake192](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-192.md) and its recovery guide preserve the original report, proof sections, supplied reviews and embedded predecessor without duplicating them here.

The submission contributes the three rotations, marker fold, exact machine and verification packet. The dominated numerical theorem, parent source, native calculus, compiler and symbolic runtime are inherited. [NOTICE.md](NOTICE.md), [the original new217 attribution](provenance/ATTRIBUTION.md), [the parent notice](provenance/parent-NOTICE.md), and [licenses/](licenses/) preserve that ancestry. `drop_contract` authored this exposition and independently reviewed the ordinary proof; `review_upstream_reflection` independently reviewed the new source and code closure; root selected and executed the fresh checks. The exact [first proof/code review](reviews/first-proof-review.json), [second ordinary proof review](reviews/second-proof-review.json), [code-closure comparison](reviews/code-closure.json), and [independent reconstruction receipt](reviews/independent-helper-review.json) are retained. These roles do not transfer authorship of the submitted construction.

The [omit-zero composition and first 216 searches](research/omit-zero-fold-search/README.md)
retain a reviewed source/startup combination and two bounded negative searches.
The modified layout still has 217 states; no fresh shortened-source universal
runtime or 216-state result is claimed there.

The [cache-return composition](research/cache-return/README.md) further shortens
the successful-MP suffix to three leaves. Exact source bindings and the whole
parent startup check, but it still has 217 states and lacks a fresh modified
universal runtime. Its 645,408 bounded fold specifications yielded no survivor.

The later [exposed-marker presentation](presentations/exposed-marker/README.md)
from `673c87a878` has the identical source and the same 434-row machine under
`188→213→210→188`. Its saving cannot stack; its separate fixed-label theory
appendix remains source-only research.
