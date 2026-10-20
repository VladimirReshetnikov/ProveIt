# Fresh checks for Source 147 (intake 190)

Six direct jobs passed on a fresh disposable copy: source bisimulation, full deterministic lineage, canonicalization and startup, independent startup, all generic runtime cases, and the independent runtime audit. The full-runtime job also invokes its audit; the sixth job repeats only the finite audit explicitly. No wrapper terminal status is claimed.

The actual result is `../../data/intake190-fresh-k218/execution/result.json`; all raw output and log files are alongside it. The final review is `../../data/intake190-fresh-k218/review/review.json`. Absolute scratch paths in those files record the actual run and are preserved verbatim.

After recovering the original Source 147 archive with its `K218_Construction_2026-10-20` inner directory, run from the repository root:

```sh
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake190-fresh-k218/prepare.py --packet /path/to/recovered/K218_Construction_2026-10-20 --output /tmp/intake190-fresh-new
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake190-fresh-k218/run.py --work /tmp/intake190-fresh-new
```

The output directory must not exist. Preparation copies the packet, reads pinned nested ZIPs as data to recover two K219 baseline inputs and five K221 runtime dependencies, and emits the exact direct-job plan. It never runs an ancestor suite or a delivered reproduction/manifest wrapper. Python assertions must remain enabled. The serial runner enforces a 240-second process-group cap for the full runtime job and 60 seconds for each other job, retaining stdout, stderr and terminal records. It checks input identities before and after each process and compares eleven regenerated outputs with the delivered bytes.

Observed totals: 218 working states, 436 rows, 205 source DAG nodes, 4,744 occurrences, 6,167 cases, 1,514,325 symbolic steps, minimum duration constant 13, and all 436 rows used. The complete startup is 312,701 transitions with 277 ones. This is executable mathematical checking, not a Lean/Rocq check or a 217-state result.

`review_actual.py` is an inert reader of an already completed work directory. `publish.py` preserves the author's one-time publication operation and its original scratch paths; it is historical code, not the portable replay entry point. The first reviewer preparation's old-layout path failure is retained under data history; no delivered proof job failed.
