# Grill universal-input semantic audit

Start with `AUDIT.md`. Verdict: **PASS for the semantic gate**, with the explicitly stated native-theorem imports and without claiming an emitted universal circuit or its ledger.

## Independent tests

From this directory:

    python independent_outer_checks.py
    python -O independent_outer_checks.py
    python normalization/check_normalization.py

The outer checker automatically compares its deterministic receipt. The normalization command prints its receipt for comparison with `normalization/check_normalization.json`; it uses assertions and must be run without `-O`. Neither checker imports or executes any of the repository files in `sources/`.

`outer-normal.log`, `outer-optimized.log`, and `normalization/independent-parent-replay.json` retain fresh successful replay results.

## Files

- `reviewed_semantic_contract.md`: exact reviewed subject snapshot
- `AUDIT.md`: main theorem-interface, arithmetic, and source review
- `independent_outer_checks.py` / `.json`: independent boundary tests and receipt
- `normalization/AUDIT.md`: independent persistent-phase/unique-H proof review
- `source_pins.json`: exact Git blob IDs and SHA-256 of 17 fetched pinned sources
- `sources/`: inspected source snapshots and primary-paper evidence; any saved upstream Python is evidence only and was never executed
- `MANIFEST.json`: relative-path SHA-256 inventory of this completed audit packet, excluding the manifest itself

No repository edits, whole-repository clone, publication, upstream Python execution, or large circuit emission occurred.
