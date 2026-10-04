# Portable independent-audit replay

This adapter replays the three frozen independent unrestricted finite-global-stabilization auditors. It does not execute the submitted builder, the author's checkers, upstream schedules or Lean. It neither rewrites checker source nor changes any frozen input.

## Release layout

Place this directory's release files in `BUNDLE/audit_replay/`. Preserve these exact root-relative inputs:

- `science/evidence/polynomial-dag.json`
- `independent_audit/check_exact.py`
- `independent_audit/check_semantics_fresh.py`
- `independent_audit/challenge_checker.py`
- `independent_audit/exact-receipt.json`
- `independent_audit/fresh-semantics-receipt.json`
- `independent_audit/mutation-receipt.json`

All seven inputs have independent hardcoded SHA256 pins in the adapter. The full bundle may include additional regular files and directories; the adapter snapshots and checks their preservation too. Symlink and nonregular bundle entries are rejected.

## Run

From anywhere, with any supported relocation of the bundle:

`python3 -I /path/to/BUNDLE/audit_replay/replay_audit.py --output /absolute/fresh/external/directory`

The output directory must not exist. It must be outside the bundle and must not contain the bundle. Symlinks in its path are rejected. The bundle may be read-only.

The runner copies the exact pinned checker bytes to separate external working directories. The exact checker receives its existing `--dag` and `--receipt` arguments. The semantic checker writes beside its external copy. The mutation harness's single historical DAG read is redirected, with no fallback, to the pinned bundled DAG using a tightly scoped `Path.read_text` adapter in an isolated worker. The harness and child-checker bytes remain unchanged; its twenty child executions are additionally isolated with `-I`, preserving their requested normal versus `-O` modes.

The adapter compares each regenerated receipt byte-for-byte with its frozen expected receipt. It checks the whole bundle's entry inventory, bytes, sizes, modes and nanosecond modification times before and after replay, including when replay fails. It writes a PASS receipt only after all checks pass.

Results are in external `exact/`, `semantic/` and `mutation/` subdirectories, plus `replay-receipt.json` and before/after bundle snapshots. Receipt metadata uses bundle-root-relative and replay-output-relative paths. Source files naturally retain their historical literals, but the replay does not depend on those files existing.

## Scope

This replays the mathematical audit's independent exact polynomial and finite semantic checks; it does not reproduce a full Pell witness or formally prove mathlib. The theorem remains conditional on the explicitly pinned Pell characterization. The byte-equal scientific receipts and preserved source remain authoritative. The adapter adds portability and preservation evidence only.

## Development tests

`test_portability.py` is a separate development tool, not needed for normal replay. It requires an existing valid bundle and a fresh external test directory:

`python3 -I test_portability.py --bundle-root /path/to/BUNDLE --output /fresh/external/test-directory`

It creates a minimal pinned-input fixture, replays it, packs and extracts it elsewhere, removes the initial fixture, makes the extracted bundle read-only, and replays again. It also checks tampered-input, destination, symlink, nonregular-entry and preservation guards. No original bundle bytes or metadata are changed.
