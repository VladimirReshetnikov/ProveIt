# Portable replay of the independent repeated-firing audit

Place `replay_audit.py` in the release's `audit_replay/` directory. From the release root, run:

```sh
python3 -I audit_replay/replay_audit.py --output /absolute/path/to/a/fresh/external/directory
```

The output directory must not exist and must be outside the release. All logs, unchanged temporary checker copies, receipts, and preservation snapshots are written there. Python 3.10 or newer is sufficient for the adapter and frozen checkers; the separately supplied packaging test additionally uses the current standard-library tar extraction filter.

## Required unchanged release layout

- `science/evidence/polynomial-dag.json`
- `independent_audit/audit_source.py`
- `independent_audit/source-audit-receipt.json`
- `independent_audit/audit_arithmetic.py`
- `independent_audit/arithmetic-audit-receipt.json`
- `independent_audit/semantic-challenge/independent_checks.py`
- `independent_audit/semantic-challenge/independent-check-results.json`
- `dependencies/pell-pinned-fetch.json`

All eight executable/data/expected-receipt inputs are pinned in the adapter. The Pell dependency must be the unchanged inert JSON source wrapper expected by the frozen arithmetic checker, not a replacement serialization of the accompanying `.lean` text. Its SHA256 is `9c8f8911f4435fbaaa4216e1f949eca920b49594192719e6128f3c0c7b85f2c8`.

Other release files are included in the whole-release preservation guard but are not executed. The original source/audit reports and their manifests should remain unchanged in the release. The portable entry point is this adapter; direct execution of a frozen historical checker still uses its historical path constants.

## Exact behavior

1. Snapshot every release entry, including SHA256 and size for regular files and mode/mtime for files and directories; reject symlinks and nonregular entries
2. Verify all frozen checker, expected-receipt, DAG, and Pell-wrapper pins
3. Copy each frozen independent checker byte-for-byte to its own external work directory
4. Start each checker in a fresh Python `-I` child and execute its exact bytes, without AST edits, text replacement, or code transformations
5. Redirect only the two exact historical `Path` reads to their root-relative packaged data targets. There is no existence probe or fallback to a historical source location. Self-hash reads use the unchanged external checker copy. Only the named external receipt path is allowed through the checker's patched `Path` write methods
6. Compare all three generated receipts byte-for-byte with their pinned originals
7. Re-snapshot the entire release and require file bytes, sizes, modes, mtimes, directory modes/mtimes, and entry inventory to be unchanged, including after a worker error

All structured output metadata uses bundle-root-relative paths or replay-output-relative paths. The worker traces record each exercised redirect. Source/arithmetic each use exactly one data redirect; the semantic checker uses none.

The guard is a before/after preservation check for this fixed, inspected checker set. It is not a generic OS sandbox for arbitrary untrusted programs; Python `-I` isolates imports, not filesystem permissions. The wrapper does not claim to prevent transient writes that a different malicious program could undo. The exact pinned checkers were inspected and have only the allowed filesystem accesses.

## Scope

This replays the independent exact-source checker, arithmetic-interface finite checks, and separate semantic finite checks. It never executes the submitted builder, author-side checkers, upstream programs, saved schedules, or Lean. It does not turn the mathematical proofs into a new formal proof, materialize a complete physical/Pell witness, or re-audit the published universality circuit. The scientific scope and conditional dependencies remain those in the frozen audit.

## Packaging evidence

`PORTABILITY_REPORT.md` and `portability-receipt.json` record successful ordinary and moved/extracted/read-only-bundle tests, exact receipt equality, negative-control rejection, and preservation checks. The development-only `test_portability.py` creates copied fixtures from the historical author workspace; it is evidence generation code, not the portable release entry point.
