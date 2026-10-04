# Portable isolated replay of the binary target-firing audit

This is a separate path-only adapter for the frozen scientific audit. It does not edit the submitted source or either frozen checker. It runs both independent checks, reproduces their scientific receipts byte-for-byte, and verifies that input trees, file contents, permission modes, and modification times stayed unchanged.

## Inputs

Supply the complete frozen directories, wherever the release has been moved:

- Source: `sandpile-target-firing-20261004`, or its unchanged release copy such as `science`
- Audit: `sandpile-target-independent-audit-20261004`, or its unchanged release copy such as `independent_audit`

The authenticated audit-manifest SHA256 is:

`dd6a27229d204f993b36e3f74a794353fa925e34926fd60fa3974eb1c50a33ab`

The adapter authenticates that manifest and every file in its `source_files` and `audit_files` groups before running the checks. The manifest's absolute `source_directory` and `inherited_dependencies` entries are provenance records, not active filesystem paths. The adapter does not access the old workspace or rerun the inherited Pell/Report50 dependency. All active scientific source reads use the supplied `--source-root`.

## Replay

Use Python 3 in isolated mode, with assertions enabled. For an extracted release with sibling `science`, `independent_audit`, and `audit_replay` folders:

```sh
python -I audit_replay/replay_audits.py \
  --source-root science \
  --audit-root independent_audit \
  --output /tmp/report52-audit-replay-new
```

The output directory must not exist. Its parent must already exist. It must be disjoint from the source, audit, and adapter directories, including not containing any of them. Relative input paths are permitted; literal parent traversal (`..`), symlink components, internal symlinks, and nonregular input objects are rejected. Choose an actual nonsymlink filesystem path if a platform's temporary directory is exposed through a symlink.

The adapter refuses ordinary nonisolated Python, `-O`, `-OO`, and effective environment-requested optimization. Use `-I`, not `-I -O`. It compiles authenticated source bytes directly and does not trust cached bytecode. Submitted science programs are never imported or run.

Successful output contains:

- `audit-receipt.json` and `audit-run.log`, each byte-identical to the frozen main audit result
- `semantics-receipt.json`, byte-identical to the frozen second semantic audit result
- `semantics-run.log`, byte-identical to that semantic receipt
- `replay-receipt.json`, recording checker pins, output hashes, and the preservation result

If a scientific check fails after creating the output directory, the partial directory is retained for diagnosis. Use another fresh output directory after resolving the failure. The adapter never deletes or overwrites an existing result directory.

## Exactly what the adapter redirects

For each frozen checker, the adapter:

1. Authenticates and compiles its original file bytes with a module name different from `__main__`, leaving its terminal main guard inactive
2. Confirms that there is exactly one ordinary terminal main guard with no else clause
3. Changes only filesystem globals: `SOURCE` and `HERE` in `independent_check.py`, or `ROOT` in `semantics_check.py`
4. Executes the original unmodified statements inside that final main guard

No arithmetic expression, test, count, assertion, expected hash, receipt constructor, or self-hash code is replaced. The semantic checker's receipt assembly is its own original code, not an adapter reconstruction. Its `__file__` remains the authenticated frozen checker path, so its self-hash still describes exactly the unchanged scientific bytes.

## Safety and relocation checks

Run the separate harness with a new external output directory:

```sh
python -I audit_replay/test_replay_adapter.py \
  --source-root science \
  --audit-root independent_audit \
  --output /tmp/report52-adapter-tests-new
```

The final adapter passed 27 fresh tests. The harness first runs against the original inputs, copies source/checkers/adapter into a temporary bundle, renames that bundle, and replays from its moved location. All five replay products agree byte-for-byte. A further run uses read-only relocated source and audit trees. Refusal tests cover optimized and nonisolated Python, preexisting output, every output overlap category, missing output parents, parent traversal, symlink paths and internal symlinks, a FIFO, and tampered science/checker/manifest pins. An unlisted fake bytecode cache is ignored and preserved. Original trees, bytes, modes, and modification times are checked afterward.

These checks establish the tested local filesystem contract, not a sandbox against an adversarial concurrent filesystem race. Frozen checker and scientific input files should remain immutable throughout a replay.

`replay-pin-manifest.json` authenticates this adapter package and its final test evidence. The scientific audit manifest and every scientific file remain unchanged.
