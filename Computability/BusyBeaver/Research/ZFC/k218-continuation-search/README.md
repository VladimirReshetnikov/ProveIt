# Bounded state sharing after K218

The [published K218](../candidate-k218/README.md) and its [row157 alternate](../candidate-k218/variant-row157/README.md) were freshly searched for a 217-state fold. Both bounded families completed without a survivor. **This is a negative proof-search result, not a lower bound or a semantic refutation of every tested table.**

| Exact seed | Ordered state pairs | Candidate specifications | Time |
| --- | ---: | ---: | ---: |
| K218 | 47,306 | 644,056 | 37.154 s |
| K218 with row157 | 47,306 | 642,320 | 35.894 s |
| Total | 94,612 | 1,286,376 | 73.048 s |

Each seed has 218 states. Every ordered pair of distinct keeper/deleted states is included, including the 434 ordered pairs involving initial state 0. When 0 is deleted, the emitted table's declared start is the keeper. Opposite keeper/deleted orientations may describe overlapping machines up to relabelling; the total counts specifications, not provably different transition systems.

## Family and verification boundary

For each pair, every other state's rows are exact mapped copies of the original table. All destinations to the deleted state are redirected to the keeper. The keeper's two actions are chosen from the respective original keeper/deleted actions. If one mapped branch already agrees, the other action is also synthesized over both write bits, both directions, and every remaining working state or halt target. The search includes both decoder and arithmetic states.

The two runs tested 376,356 inherited-action specifications and 910,020 additional one-common-action specifications. Radius 7 gives 15-cell windows. The original-machine domain is computed inductively from **all initial tapes**, allowing either fresh exterior bit at each window shift. A candidate is rejected if the local filter fails to find positive matching blocks within 97 transitions and the known window. Old paths are cached without applying any candidate state map; each candidate's map is applied separately.

Only the keeper and deleted states need nontrivial diagram checks; all other rows are mapped copies. An accepted diagram would match the entire known window and head, while leaving arbitrary exterior tape unvisited. Both-halt endpoints are also allowed. Every survivor would then run the unchanged independent Source139 checker in a separate process, with a freshly recomputed invariant and its corrupted-initial-halt negative control. **No candidate survived the filter, so no independent candidate certificate was produced.**

The finite window, fuel, restricted row synthesis and equal-head boundary relation are incomplete. Their failed joins are not claimed as machine counterexamples. The separate shifted-head family and source reallocation are outside this run. Each seed had a 110-second soft bound and a 120-second external process bound; neither limit was reached.

## Evidence and reproduction

The complete [baseline result](baseline-run1/result.json), [row157 result](row157-run1/result.json), [summary](summary.json), raw logs and compressed per-candidate first failures are retained. The [own metadata audit](metadata-audit.json) independently enumerates the family counts and reads every compressed record, checking sequential IDs, permissible actions, uniqueness within each ordered pair, initial-state mapping and pair completion. It does not rerun candidate simulations or turn failed joins into semantic counterexamples.

From this directory, use new output directories:

```sh
timeout 120s python3 -B search.py \
  --seed ../candidate-k218/k218.native.tm \
  --output /tmp/k218-fold-fresh-baseline

timeout 120s python3 -B search.py \
  --seed ../candidate-k218/variant-row157/k218-row157.native.tm \
  --output /tmp/k218-fold-fresh-row157
```

The driver pins both possible seed hashes and the two imported source files. `filter_source.py` is a byte-exact snapshot of the previously reviewed K219 `search_v3.py`; only its `local_filter` and table serializer are used. The new driver expands enumeration to every state and handles a deleted initial state explicitly. `check_joint_fold.py` is the unchanged Source139 submitted checker. The new driver, packaging and metadata audit were authored and source-read by `drop_contract`; no new independent full-source peer or proof-assistant check is claimed.

## Structural obstruction retained separately

Deleting state 301 with the earlier 87/0, 88/0 and 51/0 changes would leave 217 states, but the exact earlier 85-step blank prefix still applies. It enters state 35 and then writes right forever. The [literal transfer evidence](../candidate-k218/research/comparison.json) already records that failed route. This search did not repeat it or promote initialized-frame runtime correctness to a blank-tape theorem.

## Every initial state fails for the exact delete301 table

The follow-up [all-start packet](all-starts/README.md) rules out repairing this particular 217-state table merely by changing its initial state. Every one of its 217 working states, when started on blank tape, reaches a zero-reading self-loop moving into an entirely blank half-line. All future writes stay behind the head, so this is an inductive nonhalting obstruction, not a timeout classification.

The 216 newly scanned starts require 1,702 transitions in total; start0 retains the earlier 85-step failure. A separate Python implementation replays all 217 complete tape prefixes, checks the ray hypotheses, and reproduces accepted K218's 312,909-step startup as a positive control. This proves only the stated obstruction for this exact table. Further row repairs and other 217-state constructions remain open.

## Two bootstrap repairs fail a reachable source contract

The [row36 repair packet](row36-repairs/README.md) tests Source146's `36/0 → 1 L 6` and `1 L 10` repairs on that delete301 core. The disputed CD8-zero interface is the first instruction of the accepted initialized source, so source reachability cannot exclude it. Both repairs jump through `CB1` and skip the transfer that should change `(R0,R8)` from `(3,0)` to `(4,3)` before source ordinal9. Six complete traces and a separate 5,576-transition replay establish this counterexample to the accepted interface and whole-block interpretation. A different modified-source calibration is not ruled out.
