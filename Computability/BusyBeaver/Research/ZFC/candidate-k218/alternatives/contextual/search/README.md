# Bounded fold search on the contextual allocation

Both the [contextual K218](../README.md) and its [row157 variant](../variant-row157/README.md) completed the same bounded state-sharing family previously tested on primary K218. **No candidate survived the filter.** This is a proof-search result, not a lower bound or a semantic refutation of the tested tables.

| Exact seed | Ordered state pairs | Inherited actions | One-common-action additions | Total specifications | Seconds |
| --- | ---: | ---: | ---: | ---: | ---: |
| Contextual K218 | 47,306 | 188,180 | 454,140 | 642,320 | 36.986 |
| Contextual K218 with row157 | 47,306 | 188,184 | 452,400 | 640,584 | 37.351 |
| Total | 94,612 | 376,364 | 906,540 | 1,282,904 | 74.337 |

The primary and contextual allocations differ on 65 common rows. Consequently the earlier primary-table result did not cover these two exact seeds. Reverse keeper/deleted orientations can describe overlapping transition systems up to renaming; the totals count specifications, not proven distinct machines.

## Exact family and limits

Every ordered pair of distinct working states is included, covering decoder and arithmetic states and all 434 pairs involving initial state 0 per seed. Delete one state and redirect all its incoming targets to the keeper. All other states' actions remain exact mapped copies. The keeper's actions are chosen from the original keeper/deleted actions. When one mapped branch agrees, the other branch is additionally synthesized over both writes, both directions, and every remaining working target or halt. If initial state 0 is deleted, the candidate's declared start is the keeper.

The old-machine invariant is computed from every initial tape with radius 7 windows, allowing arbitrary new exterior bits on each shift. The unchanged filter seeks positive old/new blocks within 97 transitions, with matching mapped state, head and complete window, or matched halting. Cached old paths remain independent of the candidate map. Failed joins are incomplete: a larger window, longer block, different state relation or other row changes may succeed.

Each seed had a 110-second soft limit and 120-second external limit. Both finished every pair without reaching either limit. Any survivor would have been serialized and passed to the unchanged Source139 checker in a separate process, recomputing its own invariant and requiring rejection of a corrupted initial-halt control. There were no survivors, so no independent candidate checker was invoked and no 217-state certificate is claimed.

## Evidence and reproduction

The [base result](baseline-run1/result.json), [row157 result](row157-run1/result.json), [summary](summary.json), raw stdout/stderr, and compressed first-failure streams are preserved. The streams contain every specification and its first bounded-filter failure, not semantic counterexamples. Absolute input paths in actual records are historical execution paths; source hashes identify the exact published inputs.

The [driver delta](seed-pin-only.diff) changes only the two accepted seed hashes from the previously reviewed primary K218 driver. The original filter and Source139 checker are byte-identical. The [source provenance](source-provenance.json) records those identities. `drop_contract` authored this adaptation and read the complete driver; this source history is distinct from any later independent peer receipt.

The [metadata audit](metadata-audit.json) independently enumerates family counts and reads all 1,282,904 compressed records, checking actions, IDs, uniqueness within a pair, complete ordered-pair coverage, initial-state mapping, current code/seed hashes and stream hashes. Its [small delta](audit-portability.diff) uses published relative seed paths and also rejects repeated whole pairs or missing runs. It does not rerun candidate transitions or strengthen negative-search conclusions.

From this directory, choose fresh outputs:

```sh
timeout 120s python3 -B search.py --seed ../machine/k218.native.tm \
  --output /tmp/contextual218-fold-fresh
timeout 120s python3 -B search.py \
  --seed ../variant-row157/k218-contextual-row157.native.tm \
  --output /tmp/contextual218-row157-fold-fresh
```

The search driver refuses existing output directories, pins the seed and supporting code, stops at the first independently certified survivor or a bound, and records completion or partial progress explicitly. No source reallocation, shifted-head relation, unrestricted row synthesis, proof-assistant check or new calibration was performed here.
