# One neutral row, then a fresh-invariant fold

This is a completed discovery experiment on the **original237** table, before the later source-rotation236 construction was observed. It uses finite radius5 all-tape inductive windows and old/new local trace caps65. Replacement row targets exclude the halt outcome; the separate halt-aware experiments in the parent package address that omission.

The retained catalogue has578 neutral row alternatives. The scanner tests567 eligible alternatives whose old target is a noninitial working state and actually changes. After each patch it recomputes the sliding-window invariant and seeks a direct fold involving that old target. It completed133,382 pairs,204,601,616 row checks and563,932,090 context tests, with zero candidates. This is not a lower bound and does not cover arbitrary source rotations or larger edit sets.

To replay, copy this directory into a writable temporary location **within the same package layout** or run in a temporary copy of the whole package:

```sh
g++ -O3 -std=c++17 fold_after_redirect.cpp -o fold_after_redirect
python3 -B scan_neutral_plateau.py
```

The runner writes its scratch table and result files beside itself. The baseline path resolves to `../../baseline/zfc_composed237_old.tm`. The original evidence is separately retained under `../../evidence/neutral_plateau_scan.json` and its log. The inherited `neutral_domains.cpp` is included as provenance for catalogue construction; it is not imported by the scan.

All outputs are discovery evidence. An actual survivor would still require an independent local/source/runtime proof. There were no survivors in this run.
