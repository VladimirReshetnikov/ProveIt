# Scanner deletion and source-only rebalancing

## Status and provenance

The **37-occurrence census is inherited**, recorded in `research/rejected-return214/all-runtime-summary.json` within the pinned `docs/incoming/ZFC_Conditional_Marker_215_2026-10-21.zip`. The compressed concrete trace and original summary are included; their provenance and hashes are in `provenance.json`.

The inherited symbolic check proved **6,104 of 6,176 contracts**. It left **72 contracts unproved at 37 source occurrences**: **22 CD1, 11 CD2, two CD8, and two CI1**. Only one of those cases is supplied as a semantic counterexample: zero-case CD1 at ordinal 26. The other 71 are failures to prove, not asserted semantic counterexamples. `inherited-rejection-README.md` preserves this original distinction.

In that concrete case, deleting native scanner state 50 gives a wrong program-counter bit: the accepted table reaches the correct next dispatcher frame after 588 transitions, while the altered table reaches its first clean frame after 662 transitions with a one at cell 12 instead of 14. Every other one-cell agrees. This disproves the stated arbitrary-frame primitive contract; it does **not** establish the altered machine's blank-run halting behavior or inconsistency equivalence.

`check_counterexample_and_census.py` retains the inherited literal trace-checking algorithm, changes file paths to explicit CLI arguments, and adds a census check. It imports no compiler or binary runtime proof engine. `rejected214.native.tm` is included only to replay this rejected experiment.

The preserved early-stage `scanner_research_original.md` predates discovery of GC215. Its original workspace paths and its opening status refer to that earlier source-search subtask; the runnable package paths are those below. Its auxiliary diagnostic and comparison-census references are historical, not required dependencies.

## Replay the inherited concrete counterexample and census

Run from the packet root, with Python assertions enabled:

```sh
python3 research/physical-search/scanner/prepare_scanner.py --out /tmp/gc215-scanner
python3 research/physical-search/scanner/check_counterexample_and_census.py --baseline-table reference/corpus/9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2.tm --baseline-source /tmp/gc215-scanner/primary.sites.json --failed-table research/physical-search/scanner/rejected214.native.tm --witness /tmp/gc215-scanner/inherited-concrete-counterexample.json --summary research/physical-search/scanner/inherited-all-runtime-summary.json
```

## New exact source layouts

The two selected source-only layouts eliminate every zero run of length six:

| Layout | Primitive occurrences | Distinct subtrees | Maximum zero run | Recorded global rotations |
|---|---:|---:|---:|---:|
| Primary K215 rebalanced | 4,751 | 205 | 5 | 13 |
| ST215 rebalanced | 4,732 | 204 | 5 | 12 |

Their exact sources, original search-result/rotation recipes, and independently checked source receipts are supplied. All large JSON inputs are compressed without discarding recipe information. Neither layout was allocated to a complete binary machine, so these are not 214- or 215-state candidate claims.

The standalone checker reconstructs the selected source from its baseline and every recorded rotation, compares the complete ordered primitive word, and checks the complete guarded control-flow graph with two independent resolvers. This reproduces the exact source result without rerunning the heuristic search:

```sh
python3 research/physical-search/scanner/verify_scanner_sources.py /tmp/gc215-scanner/primary.sites.json /tmp/gc215-scanner/primary205.recipe.json /tmp/gc215-scanner/primary205.sites.json
python3 research/physical-search/scanner/verify_scanner_sources.py reference/st215.sites.json /tmp/gc215-scanner/st204.recipe.json /tmp/gc215-scanner/st204.sites.json
```

The archived searches considered 164,486 and 216,486 proposed rewrites respectively. Those trial counts describe bounded beam searches; they do not prove that 205 or 204 is a minimum. The tree-rotation verifier proves only the selected layouts' properties. `sixzero_occurrences.json` preserves the exact 37 indexed source occurrences from the original source.
