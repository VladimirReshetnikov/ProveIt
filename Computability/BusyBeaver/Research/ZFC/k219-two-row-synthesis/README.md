# Demand-driven two-action folds of K219

Two completed bounded searches covered **21,486,528 complete action assignments** across 14 selected ordered state pairs on each of the two accepted K219 tables. No candidate survived the radius-7, fuel-97 discovery filter. This is a negative result for these bounded local diagrams, not a proof that no 218-state machine exists.

For each pair, the dropped state maps to the retained state. All other rows are mapped unchanged. Both actions of the retained state may vary independently over two writes, two directions, and all 219 remaining-or-halt targets: `876² = 767,376` assignments per pair and seed. The seeds are the accepted [K219 table](../candidate-k219/README.md) and its [row157 variant](../candidate-k219/variant-row157/result.json).

| Run | Ordered pairs per seed | Complete assignments | Seconds | Survivors |
|---|---:|---:|---:|---:|
| [1](results/run1/result.json) | 1 | 1,534,752 | 4.454 | 0 |
| [2](results/run2/result.json) | 13 | 19,951,776 | 69.745 | 0 |

Run 1 tests `66:198`. Run 2 tests `4:302,40:302,113:198,40:198,54:198,108:302,0:66,0:94,0:198,113:302,198:302,40:66,54:66`, where `keep:drop` specifies the state map. These lists are disjoint.

The search fills an action only when a tested trajectory reads it. If a bounded failure occurs before an unassigned action is read, every completion has that same failure, so the whole partial assignment can be rejected. Passed partial branches still enumerate their unused actions. Cached old trajectories depend only on the fixed seed and window; they do not depend on the synthesized actions. This replaces enumeration of every complete table with a partition into rejected partial assignments.

The [independent source review](reviews/source-peer.json) checked that pruning argument. A separate [existing-record audit](reviews/result-review.json) checked all 250,278 recorded rejection prefixes: their actions belong to the declared family, their completion counts are correct, their represented sets are pairwise disjoint, and they cover all 767,376 assignments in each seed/pair group. That audit did not replay failure trajectories. The compressed streams are retained for [run 1](results/run1/rejections.jsonl.gz) and [run 2](results/run2/rejections.jsonl.gz).

Each actual run first executed the same [synthetic control](results/run1/controls.json): all 576 complete toy tables agreed with the earlier filter, with six survivors and 570 rejections. The unchanged independent checker also accepted the known three-old-step/one-new-step fold and rejected an early-halt corruption. The [second control record](results/run2/controls.json) is preserved separately. A real filter survivor would require that independent checker before receiving a relative all-initial-tape halting-equivalence claim; there were none.

From the repository root, reproduce each run into a fresh directory:

```sh
timeout 120s python3 -B Computability/BusyBeaver/Research/ZFC/k219-two-row-synthesis/search.py \
  --output /tmp/k219-two-row-fresh1 --seconds 110 --pairs 66:198

timeout 120s python3 -B Computability/BusyBeaver/Research/ZFC/k219-two-row-synthesis/search.py \
  --output /tmp/k219-two-row-fresh2 --seconds 110 \
  --pairs 4:302,40:302,113:198,40:198,54:198,108:302,0:66,0:94,0:198,113:302,198:302,40:66,54:66
```

The 110-second internal deadline is checked between partial evaluations; the external `timeout` supplies the process limit, including controls and any survivor verification. A stopped run is incomplete. The portable source changes only its [sibling-input path](history/portable-path.diff), retaining the execution logic. It was source-checked but not rerun during publication. It uses the existing pinned inputs and checker from [continuation search](../k219-continuation-search/README.md).

The [publication map](publication.json) preserves every original result, control, source/input snapshot, and captured [run 1 stdout](results/run1/stdout.txt)/[stderr](results/run1/stderr.txt) and [run 2 stdout](results/run2/stdout.txt)/[stderr](results/run2/stderr.txt). Identical input snapshots are stored once under `history/inputs`; historical absolute paths remain in the original records. A corrected, unshared source-peer line-count draft is retained as history.

Attribution: `root` authored and executed this extension of `drop_contract`'s prior filter; the independent joint-fold checker comes from Source 139. `review_upstream_reflection` reviewed the new pruning logic and existing prefix records and packaged the two completed runs. No search, simulator, compiler, or proof-assistant invocation was repeated for this publication.
