# Recovering and replaying the K218 construction

Run from the repository root, choosing new paths outside the repository:

```sh
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/recover-intake188.py /tmp/k218-recovered
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake188-fresh-k218/prepare.py --packet /tmp/k218-recovered/K218_Construction_2026-10-20/K218_Construction_2026-10-20 --output /tmp/k218-direct
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake188-fresh-k218/run.py --work /tmp/k218-direct
```

Recovery restores the original wrapper layout from arrival commit
`c4568161bf0eafeabc9e6f5a4a5c8c0a90c22f70`. Preparation copies it to fresh
scratch space, extracts baseline data and the five pinned runtime dependencies,
and records the exact six-job plan. The serial runner regenerates the table and
source, independently checks source equivalence and the state fold, checks
canonical and separate blank startup, regenerates all 6,167 symbolic primitive
cases, and runs the independent runtime audit. The full runtime has a
180-second process cap; each other leaf has 60 seconds. Assertions remain on.

Successful output is `FRESH_DIRECT_LEAVES_PASS` in the new `result.json`.
`output/` contains the exact regenerated artifacts and receipts, with raw
stdout/stderr in `logs/`. This is the direct six-leaf suite: the delivered
wrapper's manifest phase and inherited predecessor suites are not replayed.
There is no Rocq, Coq or Lean execution. Do not describe this as the delivered
wrapper's complete terminal status.

The recorded run used the exact original adapters retained under
`code/intake188-fresh-k218/actual-adapter/`. Their portable successors above only
parameterize packet/work paths; the exact diffs are retained alongside them.
Portable preparation was tested for normalized-plan equality. The heavy runtime
was run once, using the preserved original adapter.


The [placement map](data/intake188-placement.json) accounts for every delivered
member. The [fresh recovery receipt](data/intake188-recovery.json) restores all
99 files with their wrapper and executes nothing. Main article PDFs and TeX
inputs, including the formalism supplement, remain recoverable this way.
Historical paths in delivered receipts remain unedited; use the new commands
above instead of invoking flattened archival filenames.

The [actual record](data/intake188-fresh-k218/actual.json) and
[evidence review](data/intake188-fresh-k218/review.json) bind six passing jobs,
6,167 guarded cases, 1,515,158 symbolic rules, minimum duration constant 12,
all 436 rows and the complete 312,909-step blank startup. Rebuilt table, source,
canonicalization and case arrays match the delivery. Runtime metadata differs
only in elapsed time and the recorded Python version. The evidence-reader's
first overstrict comparison and narrow correction are retained separately;
they did not change the supplied checker or actual outputs.

The case receipts are not a standalone kernel proof. The inherited
finite-refutation calibration and ordinary source/fold proof remain separate
prerequisites. Exact-K218 Lean and internal PA endpoints are open.

For the intake's additional row157 layout and later 217-state searches, use the
[candidate publication](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-k218/README.md).
Its equivalence check is separate from the six submitted-construction jobs.
The two other failed-218 research archives remain queued for batch 189 and are
not silently included in this recovery command.
