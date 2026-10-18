# Batch 166: a compensated 244-state reduction

Source 70 supplies *A 244-State Turing Machine Calibrated to Con(ZFC)*, delivered in `248bc0593651331065ae558802a914110562d20a`. Its principal table removes one state from the exact maintained Routing245 machine. The ordinary mathematical proof supports **ZFC ⊢ (¬Halt(M244) ↔ Con(ZFC))**, by a direct halting equivalence and the inherited 245-state calibration. Independent ordinary review found no mathematical blocker in that argument. The new table has no complete Lean endpoint or internal PA calibration at this intake checkpoint; the [closed external 245-state endpoint](../../../../../../Computability/BusyBeaver/Research/ZFC/routing245_binary.md) remains the checked baseline.

Placement `6619bd0002a0771284cfda26d0e734f76cffaaa4` preserves **170 ancillary files** unchanged, with **21 manuscript/delivery/TeX files archive-only**, totaling **191 recoverable members**. Only this committed ZIP was retired. Its 177 distinct Git blobs include inherited inputs; 99 distinct blobs and 107 member occurrences have prior history, checked against 44 original placement trees. The new proof, literal patch and equational branch make this a new manuscript, not a repeat. The [placement map](data/intake-166-placement.json), [history inventory](data/intake-166-inventory.json) and [recovery instructions](intake-166-reproduction.md) preserve the distinction. Eighteen other queued archives remain outside this batch. The existing article is unchanged, and the collection remains at 290 reports, with 70 sources in this host.

The separate [maintained candidate](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-compensated244/README.md) promotes exact machine inputs and ordinary proof references. It does not replace this collection intake or confer a proof-assistant result.

## Exact saving and all-tape proof

The binary, single-tape machine has 244 working states, 488 rows, start 0, dispatcher 88 and separate target-only halt 244. It starts at head 0 on an all-zero two-way infinite tape; all initialization is counted and every move is left or right. The canonical SHA is `2ea5521fa7d0fc24b4f3dc07d497b10de2532147225820033d9c96f247444187`. In original labels it starts at 95, dispatches at 96 and halts at 254; its SHA is `d603bc3793ac9373f510a05d4e898f4ee7b4cac492821406a665554dca5c6daf`.

The supplied baseline is byte-identical to the current maintained Routing245 old table, SHA `f8dbeacdad5fd89c57e3f240781324b09110be8e0ccdb838a9c710fb28d2a267`. Delete old state 122 and make exactly these retained-row changes:

| Row | Before | After |
| --- | --- | --- |
| 92/1 | `1 L 24` | `1 R 66` |
| 104/1 | `1 R 122` | `1 R 92` |
| 106/1 | `1 R 122` | `1 R 92` |
| 167/1 | `1 L 92` | `1 L 151` |

Every other surviving row is unchanged. The [static literal review](data/intake-166-literal-identity.json) checks the patch and all 488 canonical rows against the exact bijection. The allocation becomes 116 framework plus 128 grammar states. Canonical labels and old labels are different conventions: old halt is 254, not canonical halt 244.

From shared start 95, the old and new machines preserve halting for **every initial binary tape and every head position**. They are not claimed equivalent from every arbitrary initial control state. The old computation maintains a local invariant: at 68, 122 or 167, the cell immediately left is one; at 81, a one immediately left implies another one two cells left. Complete incoming-edge inventories establish this invariant, vacuous at start 95. Equal-configuration comparison boundaries exclude 92 and 122.

There are 482 identical ordinary one-step rows. The exceptional entries split into seven whole-tape identities:

| Entry and local context | Old/new transitions | Common endpoint |
| --- | --- | --- |
| 104/read1, next0 | 2/4 | state25, head+2 |
| 104/read1, next1 | 2/2 | state66, head+2 |
| 106/read1, next0 | 2/4 | state25, head+2 |
| 106/read1, next1 | 2/2 | state66, head+2 |
| 167/read1, preceding1 | 2/2 | state24, head−2 |
| 81/read1, preceding0 | 2/2 | state107, head−2 |
| 81/read1, preceding11 | 6/4 | state2, head−2 |

Only the last case changes cells: both sides erase offsets −1 and 0. No trace reads or writes outside its stated finite context. Thus the endpoints agree on the entire tape, including arbitrary exterior values. Positive bounded block lengths give both halting directions by induction. The clock formula `t244 = t245 + 2A − 2B`, with `(2/3)t245 ≤ t244 ≤ 2t245`, applies at completed aligned blocks. It is not a microstep correspondence.

The blank specialization uses finite coded tapes and arithmetic induction; the report's reverse argument compares an old prefix of length `6t` with a proposed new halt by time `t`. This justifies arithmetic formalizability of the local reduction. It does not complete the inherited proof-search calibration inside PA. The [ordinary review](data/intake-166-ordinary-review.json) keeps that boundary explicit. The direct reduction reuses the existing 245 source, logical seed and consistency theorem without requiring another 3,013-pair source bisimulation or complete interpreter proof.

## Fresh executable evidence

Root's portable replay passes in **1.367 seconds**: exact reconstruction of all three delivered variants, both local proof checkers, principal sparse/dense initialization, archived full-runtime input binding, **one** symbolic dependency smoke case, the equational backend and its artificial contradiction demo. The [portable execution](data/intake-166-portable-execution.json) and [separate existing-evidence review](data/intake-166-portable-review.json) expressly exclude a fresh full replay from that invocation. The optional delivery-checksum loop is omitted by removing `SHA256SUMS` only on the disposable copy; semantic identity checks and every supplied source remain unchanged.

A separate full invocation passes all **8,391** universally guarded cases in **540.786 seconds**, under its original 600-second process-group bound. It checks **2,315,075** symbolic rules, all **488** rows and positive instruction duration at least **13**. Every complete certificate field matches the delivered result except elapsed time. The [full execution](data/intake-166-full-runtime-execution.json), [fresh result](data/intake-166-full-runtime-verification.json) and [existing-output review](data/intake-166-full-runtime-review.json) retain the exact command, raw logs and source identities. This is one fresh complete replay, not two independent symbolic engines.

The whole-frame contract covers nine independently arbitrary natural primary values, distance `64+n`, and any nonempty finite spare list of arbitrary natural values, with complete tape comparison. The source has 6,460 leaves; the delivered abstract closure checks 8,384 nonhalt edges. In `--all-values` mode the register values are not restricted to that source invariant. Unary and list induction contracts justify unbounded traversals; literal steps cover the remaining finite control.

Independent sparse/dense simulations agree on the entire blank tape after **407,951 steps**: old state96, head−5, marker−6, header176, distance181, physical values `(0,0,0,3,0,0,3,0,0)`, logical seed `(3,0,0,0,3,0,0,0,0)`, 167 spare ones and exactly 351 one-cell coordinates, with zero elsewhere. This is Routing245's root frame, reached 36 steps later. It checks initialization, not nonhalting.

The default driver's temporary directory discards detailed child outputs. Root therefore repeated reconstruction, the two local checkers and the boot check to retain their [permanent records and streams](data/intake-166-retained-local-execution.json); the resulting tables and three JSON certificates are byte-identical to delivery. This repeat preserves evidence and is not an additional independently implemented checker. The first local checker checks 7,784 Boolean invariant implications; the second checks all required incoming edges and 18 old/20 new literal transitions across seven cases. Both reject reading outside the fixed context. Python finite checks are accompanied by the printed global induction, not represented as kernel theorems.

## Other results retained from the report

The useful search move is a merge combined with one compensating row change. The tape records which entry occurred; an existing state repairs the affected backward route. The isolated merge and isolated repair need not each be correct. The final ordinary proof removes dependence on the finite search screen.

The recorded discovery family starts with 54 merge seeds and tests 6,032,656 compensation choices: 18,816 repair the first failing fixture, 42 pass expanded quick probes, and three pass all 8,385 finite instruction fixtures. Fuel is 6,000/20,000 and the tape window is −64 through 1983. Those finite fixtures are different from the 8,391 universal guarded cases. The discovery search was not rerun and supplies no global minimality or lower bound.

| Variant | Deleted label / repair | Delivered rules | Delivered blank prefix |
| --- | --- | --- | --- |
| Principal 1 | 122 / 167/1 | 2,315,075 | 407,951 |
| Supplemental 2 | 149 / 167/1 | 2,312,543 | 407,951 |
| Supplemental 3 | 149 / 170/1 | 2,313,659 | 407,993 |

All three tables are freshly reconstructed, but only the principal complete runtime and startup are replayed here. Variants2/3 retain their delivered complete certificates and do not automatically inherit the principal all-tape proof. The inequality-tail source simplification also stays on record: clearing a residual in place preserves the stated routine contract under the zero-target premise, but its standalone decoder adds a clear control and costs one more state. It is not used by this machine.

The equational branch is a separate ordinary result. A finite equality-free universal clause theory with a constant is satisfiable exactly when its one-sorted equational encoding has a nontrivial model, equivalently when ground contextual rewriting does not connect zero and one. The forward construction uses a powerset embedding/retraction. The reverse uses an ultrafilter on predicate values without requiring arbitrary original functions to preserve its kernel. Ground-term congruence proves completeness of the explicit bidirectional substitution/context certificate language. The included equality completion handles native equality before the equality-free encoding.

This argument depends on the cited Boolean single-axiom theorem and the inherited FC13B calibration; finite Boolean tests do not prove that cited theorem. The supplied input has 23 clauses and 57 literals, producing 21 grouped equations, 42 orientations and a complete **2,324-bit** packet, compared with a **1,499-bit** clause payload. The demo deliberately adds an artificial contradiction and is not a ZFC refutation. The packet still needs a binary initializer, codecs, substitution, contextual replacement and fair enumerator, with all control charged. It yields no further machine state bound.

## Attribution and remaining work

The manuscript was written against ProveIt `cb7984df14aed713269d5a596a27d33321cc2c19`, with inherited upstream `c132d7eae8158cd3a9850ea3eb7251158c3dd821`. It correctly recognizes the closed 245 external endpoint rather than repeating the older open status. Existing arithmetic table/startup results for earlier246 do not become244 internal results merely by this ordinary reduction. The [project's accepted benchmark criterion](../../../../../../Computability/BusyBeaver/Research/ZFC/README.md) remains in force; this source keeps the same theory rather than increasing its strength.

Credits follow the delivery: Mira-Cult's original calculus/program, Jeff Ketchersid's verification, Andrew James Wade's compiler framework, ProveIt's Routing245 and preceding reductions, and the incoming 18 October contribution's compensated fold, proof/checks and equational experiment. It was prepared for Vladimir Reshetnikov and ProveIt; no additional individual author is inferred. The Boolean basis is credited separately to McCune, Veroff, Fitelson, Harris, Feist and Wos. Inherited notices and licenses remain unchanged in the placed reference material.

The next small Lean route is a literal table/bijection plus positive-block transfer, the local invariant, exact ordinary-edge classification and seven whole-tape identities, composed with `BinaryRouting245`. New proof work is published separately with actual execution evidence. This intake confers neither that complete244 endpoint nor an internal PA theorem, absolute consistency, unconditional nonhalting or two-sided independence from consistency alone. The complete [source dossier](intake-166-source-70.md) preserves source locations, current-tree comparisons and all scopes.
