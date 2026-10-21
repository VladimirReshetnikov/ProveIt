# Reproduce the selected Source153 leaves

Recover Source153 from batch193, preserving its internal
`ZFC_218_Research_2026-10-20` layout. The two unchanged baseline files are already
retained under the host data directory; no ancestor script needs to run.
From the repository root, using a nonexistent scratch output path:

```sh
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake193-source153/run_selected.py \
  --packet /tmp/recovered153/ZFC_218_Research_2026-10-20 \
  --plan SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake193-source153/review/replay-plan.json \
  --reviewed-inputs SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake193-source153/review/reviewed-inputs.json \
  --baseline-table SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/140-k219-machine-k219.native.tm \
  --baseline-source SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/140-k219-machine-sites219.json \
  --output /tmp/source153-fresh
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake193-source153/audit_actual.py \
  --execution /tmp/source153-fresh \
  --review SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake193-source153/review \
  --output /tmp/source153-fresh/actual-review.json
```

Replace only the recovered packet and scratch output locations. Python assertions
must be enabled; no `-O`/`-OO`. The adapter preserves the exact six selected argv
leaves, fresh disposable packet copy, inherited environment with optimization
removed,120-second per-process cap, separate streams and stop-on-first-failure.
It adds portable explicit paths and preflight checks of reviewed code/baseline
bytes, and saves its exact runner in the fresh output for the audit. An unexecuted
first adapter draft omitted that runner copy; it remains in history/portable-draft1.
The corrected adapter was source-reviewed and AST-parsed but not executed. The original
executed root runner is retained in `history/`; `runner-portability.diff` discloses
all changes. None changes delivered code or mathematical checks.

The own audit reads records only: no delivered imports, tests, simulator or
compiler. On a new execution directory it verifies both process and semantic
result gates and records new hashes/timing. It can also read the preserved
original execution directory while present. Published compressed evidence is a
storage format; it is not itself the expected live execution layout.

The actual run and independent record audit are under
[the evidence directory](../../data/intake193-source153/README.md). Original
absolute scratch paths inside historical plans/results remain provenance, not
instructions to reuse or overwrite those locations.
