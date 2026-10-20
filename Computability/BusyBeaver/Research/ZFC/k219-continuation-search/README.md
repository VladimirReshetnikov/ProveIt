# Bounded decoder-state sharing after K219

This search found no certified 218-state machine. The initial search enumerated 344,648 candidate specifications on the published [K219](../candidate-k219/README.md) and its [row157 variant](../candidate-k219/variant-row157/result.json), then repeated the same family with wider diagram bounds. Later searches covered engine pairs and deletion of single-entry checkpoints. Every such candidate failed its bounded filter. These failures are neither semantic counterexamples nor a lower bound on the number of states.

## Candidate family

For each seed, the search considers all 14,196 unordered pairs of its 169 allocated decoder states. It deletes the higher native label, redirects every incoming transition to the retained label, and chooses the retained state's two actions. All other actions remain mapped copies of the seed. The initial state is outside the decoder allocation.

The inherited-action family takes each branch from either original state, removing duplicate choices. The tag/helper family applies when one mapped branch already agrees: it retains that branch and synthesizes the other over both writes, both directions, and all 218 remaining working states plus halt. This includes left-moving helpers and non-decoder targets. It does not synthesize both branches independently when neither branch agrees.

| Seed | Inherited choices | Tag/helper choices | Total |
|---|---:|---:|---:|
| K219 | 56,518 | 116,242 | 172,760 |
| K219 row157 | 56,520 | 115,368 | 171,888 |
| Both | 113,038 | 231,610 | 344,648 |

Only the four old rows belonging to the merged states can differ from their mapped new rows. The filter computes an inductive finite-window overapproximation from **all initial tapes**, then seeks strictly positive old/new blocks with a common mapped state, head and complete window. Untouched exterior cells are arbitrary. Leaving the window before a join rejects this search attempt; a larger window, different invariant or blank-specific proof may still work.

A survivor would be submitted to the unchanged [Source 139 joint-diagram checker](../candidate-k219/variant-row157/check_joint_fold.py), with its negative initial-halt control, before any acceptance. No K219 candidate reached that stage. The checker was exercised only on the small synthetic controls described below.

## Actual results and retained evidence

| Run | Search source | Filter radius / fuel | Seconds | Surviving candidates |
|---|---|---:|---:|---:|
| [1](results/run1/result.json) | [v1](search.py) | 3 / 9 | 11.851 | 0 |
| [2](results/run2/result.json) | [v2](search_v2.py) | 5 / 97 | 20.371 | 0 |
| [3](results/run3/result.json) | [v3](search_v3.py) | 7 / 97 | 20.027 | 0 |

Each pass completed the same 344,648 specifications within its 350,000-candidate and 1,200-second limits. The process was additionally bounded by a 1,240-second external timeout. Each run preserves the exact executed source, checker snapshot, input descriptor, result, and gzip JSON-lines stream containing every rejected candidate and its first failed window. The [summary](results/summary.json) records stream hashes and failure categories.

In the final pass, 341,567 candidates exited the window before a join, 1,598 reached new halt without a proved old halt, and 1,483 repeated a new configuration before joining. None of its first failed windows was all zero. A separate helper-focused extension below then covered pairs outside the decoder allocation.

The original [controls](results/controls-v2.json) exercised v2. The separate [v3 controls](results/controls-v3.json) exercised the current cached filter and existing checker at radii 3, 5 and 7, all with fuel 97: a synthetic six-to-five-state merge has a three-old-step/one-new-step join, and an invalid early halt is rejected. The controls share the old-path cache between the positive and negative case, as the search does. They establish those cases only.

[inputs.json](inputs.json) preserves the initial v1 defaults (filter 3/9 and proposed certificate 5/97). The **actual result fields above govern each run**. In v3 a survivor's checker radius is the selected filter radius; its checker fuel remains 97. All four pinned input files were unchanged after each pass. These are fresh Python search results, not Lean/Rocq checks or a PA endpoint.

## New/shared helper extension

The separate [helper search](search_helpers.py) covers every pair involving native state 302, 301 or 108 against every other noninitial working state: 648 pairs per seed. States 301 and 108 occur in the decoder allocation; state 302 does not. Its [actual result](results/helpers-run1/result.json) completed in 5.240 seconds at radius 7 / fuel 97, rejecting all 19,136 specifications in the filter. Each seed contributed 2,576 inherited and 6,992 synthesized choices. Of these specifications, 7,736 are new nondecoder-pair cases and 11,400 overlap the previous family. Across both families, 352,384 different specifications were considered.

All 19,136 failed windows are retained. The reasons were 18,990 window exits, 92 unproved new halts, and 54 repeated configurations. No candidate reached the full checker. The [diff](search-helpers.diff) changes only the pair set and corresponding scope metadata from v3.

State 302 clears a terminal string of ones, crosses its preceding zero, and calls state 4 to increment the remaining source prefix. It serves both right-child zero-decrement returns and the new comparison's B1 exits. State 4 itself has a different zero branch. Sharing their one branch alone does not establish interchangeable entry contracts: a future proof must preserve the distinction between crossing the marker and incrementing a prefix. The present bounded failures do not rule out such a source-aware redesign.

## Reproduce

From the repository root, use fresh output paths and enabled Python assertions:

```sh
timeout 1240s python3 -B Computability/BusyBeaver/Research/ZFC/k219-continuation-search/search_v3.py \
  --output /tmp/k219-state-sharing-fresh --filter-radius 7 --filter-fuel 97
timeout 1240s python3 -B Computability/BusyBeaver/Research/ZFC/k219-continuation-search/search_helpers.py \
  --output /tmp/k219-helper-sharing-fresh
python3 -B Computability/BusyBeaver/Research/ZFC/k219-continuation-search/control_checks_v3.py \
  --output /tmp/k219-state-sharing-controls-fresh.json
```

The top-level scripts resolve the exact maintained candidate files relative to this directory. Copies under `results/run*/` preserve executed bytes; they are historical snapshots rather than standalone relocated packages.

## Equality hit2 compiler follow-up

The separate [hit2 source](../k219-source-search/candidates/hit02.sites.json) has 207 DAG nodes and 4,744 leaves, with no right-child decrement. Its [all-natural source proof](../k219-source-search/proof.md) is separate from these compiler measurements.

The unchanged [incremental compiler](compiler-inputs/measure.py) and its [protected variant](compiler-inputs/measure_protected.py) both reproduced the original 219 table exactly, then [rejected hit2](results/hit2-compiler-run1/result.json): its new right-child CI6 occurrence had no supported generic entry. No candidate table was emitted by that attempt.

A separate exploratory successor proposes `1R13` for that occurrence, symmetric to the unique generic left-CI6 entry `0R13`. **Its right-context runtime contract is unverified.** With only that explicit hypothesis added, [measurement](results/hit2-ci6-compiler-run1/result.json) passes decoder-prefix binding and gives 220 states with origin reuse, or 240 with old states protected. Both retain state 302. Removing right-child decrements alone therefore does not remove this helper from these allocations; B1 and other retained routes still reach it. Because neither count improves on 219, no full symbolic-runtime or startup replay was run on these exploratory tables. They are not calibrated candidates.

The [first measurement script](measure_hit2.py), [one-entry successor](measure_hit2_ci6.py), exact imported utility snapshots and both outcomes are preserved. Reproduce them with fresh output paths:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/k219-continuation-search/measure_hit2.py \
  --output /tmp/k219-hit2-original-fresh
python3 -B Computability/BusyBeaver/Research/ZFC/k219-continuation-search/measure_hit2_ci6.py \
  --output /tmp/k219-hit2-ci6-fresh
```

The compiler adaptation and protected policy were authored by `opening_encoder`; these two measurement wrappers and the CI6 hypothesis were authored by `drop_contract`. Source utilities are retained from the pinned K221 package with their existing attribution. The alternative source and its mathematical proof were prepared independently by `review_upstream_reflection`.

## Selective allocator protection on experimental R variants

Three [fourth-parameter sources](../k219-pivot-fusion/README.md), RAB-left, RBC-left and RCA-right, have 205 DAG nodes but an **open consistency calibration**. Their original incremental allocations fail decoder-prefix checks; protecting all old states gives 230-state layouts. These sources do not currently satisfy the goal of a ZFC-calibrated machine with at most 218 states.

The [selective allocator](selective_protection.py) keeps the original leaf-entry choices and protects reused state IDs implicated by the first failing prefix. Protection applies to the entire state, including all subtree aliases and incoming branches. It retains exact failed tables, prefix words, tape snapshots and transition traces. Each of the three sources is bounded to 64 attempts, with a shared 120-second limit and an external 125-second process bound. Each potential success is checked again by the unchanged full prefix walker and table roundtrip. The baseline control reproduces K219 exactly.

The [first run](results/selective-run1/result.json) protected 15 states appearing in the failing prefix and produced 229-state layouts. A [narrow successor](selective_protection_v2.py) checks node-to-state binding at each node entry, exposing an earlier wrong-node arrival rather than descending until a later tape failure. Its [actual run](results/selective-run2/result.json) needed only states 131 and 145 protected and produced 222-state layouts for all three sources. Each run took two allocation attempts per source, completing in 1.215 and 1.226 seconds respectively. The [focused diff](selective-early-binding.diff) preserves the earlier run.

The common bad prefix is `1110100100110111111100`: it arrives at state 303 instead of the required state 165. Its final edge originally follows `188/0=0L131`, `131/0=0R145`, `145/0=0R165`. In the failed allocation the last target becomes 303. State 131's encountered zero row is unchanged; the successor conservatively protects both reused state IDs on this edge. This is a concrete dependency of a context-sensitive decoder helper, not evidence that every protected state is necessary.

These are greedy allocation measurements, not a minimum or a primitive/runtime proof. No layout reaches 219, so no full symbolic-runtime or startup replay was performed. Arithmetic helper preservation beyond the checked decoder prefixes and the proposed R-calculus calibration remain separate obligations. The unchanged-theory 219 candidate is unaffected.

```sh
timeout 125s python3 -B Computability/BusyBeaver/Research/ZFC/k219-continuation-search/selective_protection_v2.py \
  --output /tmp/k219-selective-allocation-fresh
```

The [independent source review](results/independent-source-peer.json) concerns the original decoder merge enumerator, its limits and historical controls. It does not claim independent review of these later compiler measurements. Root reviewed the hit2 packet before its separate commit; the new selective packet has its own retained sources and results.

## Engine entries and hidden checkpoints

These follow-ups preserve the accepted 219 source theory. They operate on both exact published seed tables and leave candidate publications unchanged. Every run used radius 7 and fuel 97. The counts below overlap earlier families and each other; they are not a census of globally distinct machines.

| Family | Specifications, both seeds | Seconds | Survivors |
|---|---:|---:|---:|
| [Engine anchors 198, 113, 66, 40, 54](results/engine-helpers-run1/result.json) | 19,064 | 5.611 | 0 |
| [Two-action merge 198 → 66](results/66-198-run1/result.json) | 95,922 | 6.425 | 0 |
| [Hidden checkpoint 198](results/hidden198-run1/result.json) | 1,752 | 4.221 | 0 |
| [Every strict single-entry checkpoint](results/hidden-states-run1/result.json) | 190,092 | 8.644 | 0 |

The [engine-anchor search](search_engine_helpers.py) applies the inherited-action/one-common-branch family to all 1,075 pairs per seed involving one of those five states and any other noninitial working state. Each seed supplies 4,288 inherited and 5,244 synthesized choices. No candidate reached the full checker. Its [diff](search-engine-helpers.diff) changes only the anchor family and corresponding metadata from the prior helper search.

The [two-action experiment](search_66_198.py) maps old state 198 to 66, synthesizing both merged actions as write 1 / move left with independently chosen targets among the 218 remaining states and halt. This gives 219² choices per seed. The entry invariant is checked throughout the finite-window domain: state 66 has immediate-left 0 and second-left 1, whereas state 198 has immediate-left 1 and second-left 0. Both rows are still subject to the quotient relation, so this experiment is distinct from hiding state 198 entirely.

The [hidden-198 experiment](search_hidden198.py) instead deletes state 198 and varies only its unique incoming action, `66/0`, over both writes, both directions and all remaining targets. Its boundary relation requires identical state, head and complete tape **only outside the deleted checkpoint**. At the changed entry it seeks positive old/new blocks to a common boundary, or a proof that both halt. All other boundary rows are exactly unchanged. It imposes no relation on arbitrary configurations in old state 198. Each seed has 4,096 entry windows in the inductive overapproximation.

The [generalized search](search_hidden_states.py) applies this last method to every noninitial state with exactly one incoming row, counting self-loops and requiring a distinct predecessor. There are 109 eligible states in K219 (95 allocated decoder states and 14 other states), and 108 in row157 (94 and 14). Every eligible state completed all 876 actions; none had an empty entry domain. The result lists all eligible states, excluded states and reasons, and explicit completed/attempted counts. Old positive endpoints are cached separately for each hidden state and entry window. Its [synthetic controls](results/hidden-states-run1/controls.json) accept a three-old-step/one-new-step detour removal and reject an invalid early halt using the same cache. These controls cover those examples only.

The engine-anchor run had a 1,200-second bound and an external 1,240-second timeout; each later run had a shared 120-second bound and external 125-second timeout. Exact executed sources and complete compressed rejection streams are retained beside each result. Hidden-state survivors would require a separate independent boundary-macro verifier; none was produced. No new full symbolic-runtime, startup, Lean or PA check is claimed by these searches. In particular, state 0 has incoming engine rows and is not a disposable startup-only state.

```sh
timeout 1240s python3 -B Computability/BusyBeaver/Research/ZFC/k219-continuation-search/search_engine_helpers.py \
  --output /tmp/k219-engine-sharing-fresh
timeout 125s python3 -B Computability/BusyBeaver/Research/ZFC/k219-continuation-search/search_66_198.py \
  --output /tmp/k219-two-action-fresh
timeout 125s python3 -B Computability/BusyBeaver/Research/ZFC/k219-continuation-search/search_hidden198.py \
  --output /tmp/k219-hidden198-fresh
timeout 125s python3 -B Computability/BusyBeaver/Research/ZFC/k219-continuation-search/search_hidden_states.py \
  --output /tmp/k219-hidden-states-fresh
```

The [additional v3 peer](results/decoder-v3-source-peer.json) covers the original merge filter only. The [hidden-state source peer](results/hidden-state-source-peer.json) independently reviewed the generalized boundary filter and its completion metadata, without rerunning it or issuing a candidate certificate. The [follow-up metadata audit](results/followup-metadata-review.json) checks source snapshots, all recorded rejection specifications, eligibility, input hashes, raw allocator state counts and local links; it does not rerun or independently prove the failed diagrams.

## Scope and next direction

The result exhausts only the stated candidate specifications under the recorded bounded filters. It leaves source reassociation, occurrence splitting, multistate changes, general independently synthesized two-branch merges, and blank-specific invariants open. The two-action experiment above covers only its fixed write/direction family. Window-exit failures dominate, so a useful next step is a source-aware proof of decoder-entry contexts or a coordinated source/allocator change, rather than interpreting these failures as proof of minimality. Source transformations are being investigated separately from this binary-state family.

The two inputs and universal checker come from the maintained K219 publication and Source 139. The enumerator, bounded filter, controls and recorded runs were authored/executed by `drop_contract` on 20 October 2026; source review is recorded separately. The accepted candidate files were not edited.
