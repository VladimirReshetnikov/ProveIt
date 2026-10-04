# Emitted-quartic audit addendum

Verdict: PASS. Read `AUDIT-ADDENDUM.md` for exact coefficient identities, artifact semantics, source/export pins, regression counts, and limits.

Files:

- `check_exported_quartics.py`: independent standard-library checker; reads author source bytes inertly and JSON data only
- `receipt.json`: successful independent receipt
- `AUDIT-ADDENDUM.md`: proof-level artifact review
- `SHA256SUMS`: hashes of this addendum's four files, excluding the hash list itself

Safe command, from this directory:

    python check_exported_quartics.py --source-dir /workspace/shared/substrate-semantics56-20261004

Run without `-O` or `-OO`; this checker explicitly refuses optimized execution. The `--source-dir` path can change, but the pinned emitter and two exported JSON files must retain their bytes and relative locations. This does not execute or import the emitter.

The parent audit's original five files and `SHA256SUMS` remain unchanged.
