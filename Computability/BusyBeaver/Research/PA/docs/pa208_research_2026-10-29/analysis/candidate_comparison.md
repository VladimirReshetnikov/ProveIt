# Independent comparison of the five current U208 packages

Scope: the five ZIP archives at ProveIt commit `c086b5adaa6228009365768946d691dfc49a20bb`, retrieved by the parent agent. All observations below are from the literal downloaded files, not the incoming README's descriptions.

## Main finding

The five submitted constructions yield exactly **two** rooted, read-symbol/write-symbol/move-preserving transition-graph isomorphism classes. Their state reductions are the **same contextual merge of historical states 172 and 211**. Keeping 172 versus keeping 211 is just choosing a name for the merged vertex. The reported savings therefore cannot be composed to obtain a 207-state machine.

The primary machines of ConPA, Conditional Context, Entry Context, and History lie in class A. The Research primary lies in class B; its `variant_plain` lies in A. The Compatibility alternatives of Conditional Context, Entry Context, and History lie in B. All nine tables have 208 working states and 416 transitions; every working state is reachable in the action-labeled graph from start 0. This graph fact does not imply blank-tape reachability.

Canonical breadth-first numbering starts at state 0, explores read 0 before read 1, records writes/moves exactly, and distinguishes halt as `H`. Full canonical encodings were compared. The canonical SHA-256 identities for this precise serialization are:

- A: `5d858b5d7528dd98c5272f83d308c782ae323a47fc394a73ad9efda1096a5284`
- B: `f0c6098fabd68fce3fca0c6ac78a1b4e9dbb4ded60437b84d3e9d9ccda74f11d`

`analysis/comparison/compare_current.py` is an independently written classifier. Its complete input paths, raw SHA-256 identities, state maps, and classes are in `analysis/comparison/current_comparison.json`.

## Exact primary identities

| Package | Class | Native SHA-256 | Dense SHA-256 |
| --- | --- | --- | --- |
| ConPA | A | `527c2a6065ba7c9adb09294eed2b532810d812e46df4b5b912bae99ae6fb3a3a` | `9f4ea95849c5e1d01fa3f740023092230cd7006eed650b94a2d5da537e25212c` |
| Conditional Context | A | `b348a466a2c316511e0037ea3824de29d4c6ad37338404fbc98a3968fdb25135` | `a2fee9e41311c0d43aaac871ea411be24eada17e6b3633c55f40b437101144e1` |
| Entry Context | A | `b348a466a2c316511e0037ea3824de29d4c6ad37338404fbc98a3968fdb25135` | `a2fee9e41311c0d43aaac871ea411be24eada17e6b3633c55f40b437101144e1` |
| History | A | `36b58fea7a184b1050914170e8f5240c8a13da218dbbfa7e1985cd73d516e5c7` | `926d15c43daebdafd099723f265b073c25bf21a15e4c5593e669ccac6f70f8d0` |
| Research | B | `bdf724e5a4c5d25567a8b51d50db8ff8b6da3e42b0f03a73794f470171fdcbbe` | `5d487fb3ea29a84bedffec600af660ffeb8de3711838d67c41b01aec50c2a4ed` |

Conditional Context and Entry Context have byte-identical primary machines and byte-identical Compatibility alternatives. The latter alternative native/dense identities are `5f936da0cf393548cdd1eeebcaf7490d7a42f4ccca115f865a7bcc045463eb52` / `9865dcd7bd44deece098c16dcec7b90a96cf111592cbd37e3531b50f7b09276c`.

## Mathematical comparison and audit

Each package applies the same local theorem to one of two U209 decoder layouts. At every old-state-172 entry the two cells immediately left of the head are `10`. At old state 211, reading zero implies that the immediately preceding cell is one. These predicates follow from the *complete* incoming-edge census of the old machine, with only two or three predecessor steps; they do not depend on a sampled computation or on the semantics of Theory U.

The new representative's zero transition moves left to a shared selector. Its complete local simulation has four cases:

| Old state/read | Required context | Replacement length | Endpoint |
| --- | --- | --- | --- |
| 172/0 | preceding bits `10` | 7 | old `0 L 67` endpoint |
| 172/1 | scanned bit 1 | 1 | old `1 R 184` endpoint |
| 211/0 | preceding bit 1 | 3 | old `0 R 157` endpoint |
| 211/1 | scanned bit 1 | 1 | old `1 R 184` endpoint |

All writes on the longer blocks preserve the bit read. The finite proof never reads an unspecified exterior cell; equality therefore holds for the *whole* tape. All other 414 old rows commute with the quotient state map. Every replacement block is positive-length and has no internal halt.

I checked the incoming inventories, macro endpoints, and bounded-stuttering proof on inspection. No flaw was found in this local theorem. The reflection argument can be written without appealing to an actually infinite computation: if the child first halts by time S, then S nonhalting old steps would generate a child nonhalting prefix of length at least S, contradiction. This supports a PA-formalizable blank-tape halting equivalence. The exact old-to-new clock is

`T208 = T209 + 6*N(172,0) + 2*N(211,0)`.

That theorem is independent of the inherited consistency calibration. All packages explicitly distinguish their ordinary mathematical / custom symbolic checks from a new end-to-end Lean, Rocq, MM0, or exported PA proof. They inherit the U/PA finite-refutation translations and the numerical proof-search interpretation. A report should preserve this evidence boundary rather than describing any of the five as a new kernel-certified Con(PA) result.

## Differences that matter for further research

- Class A source depth is 42; class B source depth is 41. Both use 3,909 ordered primitives and the same 5,083 ordinal control edges.
- The Conditional Context presentation gives an especially clear five-state inductive invariant, with the crucial predicate `t0=1 or t[-1]=1` at 211. The name “Conditional Context” refers to this tape predicate, not to an unproved hypothesis in the new local reduction.
- The History package supplies two local checkers, portable transfer of the fold to all five U209 parents, and a reproducible failed source-reassociation counterexample.
- The Research package carries both classes and provides a single full verification command covering both, while retaining a compact selection of the older calibration lineage. It is therefore a convenient baseline for a new research package.
- ConPA and History keep historical state 172; Conditional Context, Entry Context, and Research keep 211. This explains several different raw hashes without changing the transition graph.

## Fresh reproduction

All five delivered quick verification drivers were inspected before execution and rerun with outputs outside the sealed package, with bytecode writes disabled. All returned exit code 0:

- ConPA: exact reconstruction, normal and optimized local check, independent local check, comparison, startup, binding to retained parent archive.
- Conditional Context: parent quick replay, both constructions, normal/optimized local audits, independent history check of alternative, comparison, startup.
- Entry Context: both constructions, normal/optimized fold check, alternative, comparison, source/startup.
- History: two local implementations both normal and optimized, comparison, source/startup, both variants, portable fold on each U209 parent, rejected-source counterexample.
- Research: finite local proof, both source CFGs, both constructions, startup, negative controls, inherited dependency binding.

The driver and machine-readable receipts are in `analysis/comparison/replay_quick.py`, `quick_results.json`, and the per-package JSON/log files. Full symbolic replay status is recorded separately; see the addendum below when completed.

## New source-layout exploration

A fresh source inventory finds 51 closed, pure-selector rotations with a single incoming edge to the inner state in class A. Independent finite testing of every primitive from zero registers, including both decrement branches, accepts 9 individual rotations and rejects 42. None of the 51 creates an immediate duplicate state.

Accepted finite regressions (outer,inner,side; 0 means left child) are:
`(18,100,0)`, `(142,143,1)`, `(156,162,1)`, `(52,154,0)`, `(162,203,1)`, `(207,7,1)`, `(132,222,0)`, `(129,146,0)`, `(135,221,0)`.

These 5,084-case finite tests are exploratory screens, not arbitrary-register symbolic proofs. The checker is derived from the supplied independent finite C++ interpreter with one register assignment per branch and without the blank-run appendix. The generator and finite outputs are retained under `analysis/comparison/rotations/`.

The old tempting pair `(155,85,0)`, `(52,154,0)` creates identical suffix states 85 and 154, giving a 207-state exploratory table after the accepted 208 fold. It fails: the arithmetic path `76 -> 152 -> 159 -> 118 -> 155` accesses the source decoder from a backward operation, so the source-only reassociation shortens a zero scan by one and begins writing one cell too early. Changing `152/0` from `0 L159` to `0 R118` repairs the earliest failing CD1 case but fails the next CD1 branch (`0011001001000`). This is a rejected repair, not a usable candidate.

### Full runtime addendum

The Research `verify.py --full` replay completed successfully in 332.59 seconds. It rederived the primary class B and secondary class A contracts from the literal tables, checking each of the 5,084 arbitrary-natural primitive contracts and all 416 rows per table. The inference counts are 1,250,564 (B) and 1,251,865 (A). The retained dependency checker also passed 167 member hashes and the nested Theory U binding. Receipt: `analysis/comparison/full_research.json`; log: `analysis/comparison/full_research.log`. The result is a fresh custom symbolic derivation, not a proof-assistant kernel certificate.

## Further novel research addendum

See `analysis/directional_associativity.md` for the new weaker source reassociation theorem and complete proof. It replaces the older demand that A,B,C all be closed in `((A,B),C) <-> (A,(B,C))` by the sufficient directional conditions `F(A)=0`, `B(C)=0`; the middle factor is unrestricted. All58 initially eligible class-A rotations preserve both independent source CFG resolvers and all5,084 target-resolution checks. Physical shared-decoder correctness remains a separate obligation.

The subsequent closed breadth-first search examined24,321 tables through3 rotations and rejected all50 exact207-state contractions. Connected directional searches covered939 class-A layouts throughdepth12 and5,729 class-B layouts throughdepth9 with no new exact duplicate fold. A source-zero-run beam covered19,136 layouts through20 rotations, reaching17 six-zero leaves from33 but retaining maximumzero run6. Detailed scripts and receipts are under `analysis/comparison/`.

An unrestricted reassociation inventory for maximal islands of single-entry, pure selectors with closed atoms found17 islands in either class. A's largest has16 selectors over17 atoms, B's18 over19. No outside existing selector represents a multi-atom interval of any such island. Across all island words, the only repeated multi-atom factor is `[12,150]` in the islands rooted at52 and155. It is precisely the known, physically invalid85/154 suffix-sharing attempt. This explains why deeper searches restricted to these closed islands repeatedly rediscover that failure; it is not a statement about arbitrary TM reductions or contextual sharing.

A new affine macro analyzer recognizes25 total linear transformations of the nine registers, including closed transfer and copy/restore loops. None has another existing decoder root with an identical universal matrix. Checking all24 uniform orderings of the four registers occurring in adjacent single-entry increment runs also yields no source-DAG improvement: the baseline197 nodes is minimal within that search. These are further negative results with explicit, bounded scope.

## New dedicated-helper layouts (final literal result)

A final search added a fresh selector state while merging one pair of old
states. It produced four elementary families, with nine donor signatures per
baseline class. All eighteen resulting 208-state machines have different
rooted transition graphs, including after arbitrary state relabeling, and are
distinct from both supplied graph classes. This is a genuine new collection
of equivalent literal tables, but does not improve the state count.

In History native labels, the representative constructions are:

| Delete→retain | Changed retained row | New helper 500/0 | New helper 500/1 | Old affected-row block lengths |
|---|---|---|---|---|
|127→124|0 L 500|0 R 8|1 R 59|3,3|
|190→160|1 L 500|0 R 86|1 R 193|3,3|
|178→168|0 L 500|0 R 154|1 R 176|3,3|
|301→88|0 L 500|0 R 122|1 R 500|5,3|

The first helper's last target may instead be109 or125. The third helper's
zero target may instead be159 and its one target may instead be225. The
needed preceding-bit tags follow from complete one-step incoming censuses,
so their proof does not require sampled reachability or finite-window data.
Every changed old step has a positive exact whole-tape block, and all other
old rows commute with the quotient. Thus each new machine is PA-formalizably
halting-equivalent to its original208 baseline on every initial tape.

All18 tables pass exhaustive local symbolic branching and all5,084 finite
canonical primitive cases. The root's independent standard-library checker
`code/verify_helper_machines.py` rechecks exact construction, all incoming
edges, two-cell block traces, whole-tape equality, ordinary-row commutation,
state census, and graph-class census, without using the exploratory context
files. It emits `evidence/new_helpers_independent.json` in the deliverable.
Full new-table arbitrary-natural primitive replay is separate from this
local quotient proof; the already verified baseline calibration transfers
through the latter.

The dedicated-helper right-moving family screened48,455,680 choices per
class; it found exactly18 oriented survivors per class, which differ only by
nine donor signatures and the representative name. Testing a second
disjoint fold with the same helper rejected4,832 combinations per class.
Fresh radius-seven contexts and ordinary one-row fold searches on each of
the18 new layouts also yielded zero survivors. These are scoped negative
results and do not prove a208-state lower bound. The additional exploratory
helper-direction extension was interrupted and is not counted as a completed
search.

Artifact entry point: `analysis/comparison/double_helper/README.md`; exact
machines, local certificates and receipts are in its `augmented_A_*` and
`augmented_B_*` directories. Canonical hashes and all18 unique graph classes
are bound in `machine_hashes.json`.
