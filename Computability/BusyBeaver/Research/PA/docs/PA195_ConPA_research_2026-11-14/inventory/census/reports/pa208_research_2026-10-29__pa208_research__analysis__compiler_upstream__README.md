# Composition and allocation history

This directory preserves the original source/allocator work and its failed checks. The published machine and source were held unchanged after `allocation210-run2/candidate.native.tm` and `sites-210.json` were written.

- `compose.py` reproduces the submitted command-local source and both command permutations exactly, then applies the same four closed splices and permutations to the accepted partial-selector source. `result.json` records complete word/CFG agreement for three source presentations; only order210 was physically allocated here.
- `allocation210-run1.stderr.log` records the initial missing-NumPy environment failure, before allocation. The disposable solver environment is described by `solver-environment.json` and `solver-install.log`; its binaries are not vendored.
- `allocate-v1.py` produced the held 215-state table. Its final global-node gate rejected eight old state108 aliases, preserving `allocation210-run2/allocation.json` with `PREFIX_FAIL`.
- `allocate-v2.py` records the local-alias gate correction and zero-new-role identity-control support. The accepted216 identity control passes with exactly the local81 row repair; no second allocation is claimed.
- `check_allocated-v1.py` found the deliberate local81 change while requiring retained entries to be literally unchanged. The successor adds its exact three-step equivalence. That successor's first parser typo is retained as `check_allocated-v2.py`; the final `check_allocated.py` passes. `entry-review-v2.diff` and `entry-review-v3.diff` show both corrections.
- `held-candidate-review.json` checks all 4,750 internal prefixes, 4,751 primitive entries, the exact local81 blocks and eight local108 contexts. It remains explicitly a finite source/entry result, preceding the separate full runtime.
- `rebuilt-run1/` records exact deterministic source/table reconstruction. The later portable source/reconstruction and archived-view checks are recorded separately.
- `history/held-publication/` preserves the pending-status prose. `history/pending-map-v1.json` preserves the first external copy map. The top-level candidate README and actual review state the later accepted result.

The independent prospective receipt is preserved under `peers/`; the final actual/blank review is at the candidate's `reviews/` directory. Original absolute paths in historical scripts and receipts describe the actual experiment. Portable public entry points are the candidate's `reconstruct.py`, `code/check_source.py`, `code/fresh_check.py`, and `code/prepare_actual_view.py`.
