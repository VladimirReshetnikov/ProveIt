# Source162 selected fresh checks

`run_fresh.py` is an original standard-library launcher for the seven source-reviewed leaves listed in `fresh-inputs.json`. It accepts a pristine extracted Source162 packet plus the three exact existing parent files. It creates a new output directory and copies only the 23 selected packet inputs and three parents. It checks their frozen identities before use and rechecks both originals and copies after every job. All child interpreters retain assertions, run with `-B`, and have `PYTHONOPTIMIZE` removed from the environment.

```sh
python3 -B run_fresh.py \
  --packet /path/to/K215_Composed_Selector_2026-10-20 \
  --parent-table /path/to/candidate-k216/k216.native.tm \
  --parent-source /path/to/candidate-k216/sites216.json \
  --reference-source /path/to/candidate-k216/alternatives/permuted/sites216.json \
  --out /path/to/new-output-directory
```

The selected sequence is reconstruction, full decoder-prefix binding, sparse-native/dense-canonical blank replay, two restricted propositional countermodels, rejected-versus-corrected CB1 control, full universal symbolic runtime, then the independent supplied saved-interface reader. Their process caps are respectively 30, 30, 30, 10, 10, 360 and 30 seconds. Any failure stops the sequence, leaves the output directory and logs intact, and records a failed actual receipt. A retry requires a fresh output directory.

`actual.json` records original input locations, before/after hashes, copied-input postchecks, actual argv/cwd, per-job limits and elapsed times, exits/timeouts, raw stdout/stderr identities, and every result artifact. The final gates require the reconstructed table/source/canonicalization to equal the delivered files, fresh complete runtime cases and startup to equal the delivered compressed bytes, and the fresh runtime report to equal the delivered report apart from elapsed seconds. The saved-interface audit is explicitly a review of stored receipts; the preceding fresh runtime job is the actual symbolic proof replay. The rejected CB1 control confirms a wrong primitive return in an older table and the corrected return in this exact submitted table; it is not a blank-run counterexample.

No archive wrapper, manifest suite, inherited proof-certificate replay, solver/discovery search, Lean, or Rocq is invoked. These are ordinary mathematical/source and runtime checks, not a new proof-assistant endpoint. Source162 is not graph-isomorphic to the earlier accepted215 table. The independently frozen complete Source162–Source164 bijection allows this one new full runtime to serve those two exact presentations; that transfer is a separate record, not an additional runtime job.

The initial live execution is under `fresh-run1/`; its terminal status is authoritative. The earlier `review.json` and `selected-plan.json` remain frozen source-only records and do not claim that a future execution passed.
