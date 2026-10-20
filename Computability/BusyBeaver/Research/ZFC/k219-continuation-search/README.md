# Bounded decoder-state sharing after K219

This search found no certified 218-state machine. It enumerated 344,648 candidate specifications on the published [K219](../candidate-k219/README.md) and its [row157 variant](../candidate-k219/variant-row157/result.json), then repeated the same family with wider diagram bounds. Every candidate failed the bounded filter. These failures are neither semantic counterexamples nor a lower bound on the number of states.

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

## Scope and next direction

The result exhausts only the stated candidate specifications under the recorded bounded filter. It leaves source reassociation, occurrence splitting, multistate changes, independently synthesized two-branch merges, and blank-specific invariants open. Window-exit failures dominate, so a useful next step is a source-aware proof of decoder-entry contexts or a coordinated source/allocator change, rather than interpreting these failures as proof of minimality. Source transformations are being investigated separately from this binary-state family.

The two inputs and universal checker come from the maintained K219 publication and Source 139. The enumerator, bounded filter, controls and recorded runs were authored/executed by `drop_contract` on 20 October 2026; source review is recorded separately. The accepted candidate files were not edited.
