# Bounded shifted-head folds of six K219 layouts

All six finite candidate families completed with **no survivor**: 1,031,840 candidates across 247,506 eligible pair-shifts, in 152.664 cumulative seconds. No 218-state machine was obtained. Every rejection means that this bounded positive-diagram filter did not close; it is not a semantic counterexample or a lower bound.

| Input layout | Candidates | Pair-shifts | Seconds |
|---|---:|---:|---:|
| zero_terminal | 173,266 | 41,576 | 26.006 |
| zero_terminal-row157 | 172,408 | 41,360 | 24.708 |
| retagged | 171,532 | 41,142 | 25.641 |
| retagged-row157 | 170,674 | 40,926 | 25.013 |
| composed | 172,409 | 41,359 | 25.388 |
| composed-row157 | 171,551 | 41,143 | 25.908 |

The exact inputs are the [three Source 141 alternatives and their checked row157 stacks](../candidate-k219/alternatives/README.md). Each run used radius 7, fuel 97, an internal 110-second budget and external 120-second timeout. None timed out; there are no partial pairs. The [summary](data/summary.json), [execution record](data/shifted-executions.json), and per-layout [results](results) preserve exact counts and every first rejection in gzip form.

## Candidate relation and complete finite family

For a removed noninitial state `drop`, the new configuration uses state `keep` with head displaced by δ=±2 and the same tape. Other states preserve the head. Every incoming edge from outside `{keep,drop}` must have direction −δ/2; it is redirected to `keep` with its direction flipped and write unchanged. Every distinct keeper is considered, including initial state 0. The two keeper rows are chosen from the old keeper/drop actions after target renaming, with additional direction-offset versions when an old target is `drop` and the resulting motion is valid. All other rows are exact prescribed copies.

The filter checks the keeper/drop obligations on an independently recomputed all-initial-tape window overapproximation. Old trajectories are cached; candidate-dependent state/head mapping is reapplied every time. Both old and new block lengths are positive. A survivor must pass the separately authored [shifted checker](code/check_shifted.py), which always recomputes its own complete domain and compares whole tapes at related endpoints, or proves both paths halt. No real survivor reached that acceptance stage.

Both mirrored synthetic 6→5 folds and their early-halt/wrong-direction negative controls pass in the [portable checker receipt](data/portable-controls.json). The discovery family also contains both positive controls. A separate metadata reader independently re-enumerated every pair's allowed action combinations and matched all 1,031,840 compressed rejection entries, including uniqueness and complete pair counts. It did not rerun the semantic search.

## Fresh reproduction

From this directory, use a fresh output path:

```sh
python3 -B code/search.py --table ../candidate-k219/alternatives/machine/composed/k219.native.tm --name composed --output /tmp/k219-shifted-composed-fresh --seconds 110
python3 -B code/check_shifted.py --controls --output /tmp/k219-shifted-controls-fresh.json
```

The search will preserve any candidate that passes its filter and invoke the independent checker before accepting it. Source histories retain the exact executed scripts, original checker controls and the unexecuted initial drafting version. The [portable diff](history/portable.diff) changes only checker locations and its corresponding hash; no proof/search logic changed. The portable checker was actually tested on both signed controls after relocation. The earlier trusted-domain interface is preserved only in checker-v1 history; the final checker always recomputes its domain. Original scripts and their absolute paths are historical evidence, not the recommended reproduction entry point.

This relation is a different family from the equal-head folds/delayed joins in Source 143. It still excludes arbitrary synthesized actions, arbitrary multirow rewrites and alternative relation invariants. The original mathematical calibration is unchanged; no compiler, Coq/Rocq or Lean proof was run for this search. Root authored the checker; [review_upstream_reflection independently reviewed it](peers/checker-review.json). Drop_contract authored discovery and the separate finite-family metadata audit. [Provenance](provenance.json) binds Sources 141–143 and placement 99fbf38bbd.
