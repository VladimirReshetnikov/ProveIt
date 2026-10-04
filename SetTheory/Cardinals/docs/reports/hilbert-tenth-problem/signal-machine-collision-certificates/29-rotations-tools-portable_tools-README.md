# Portable replay of the frozen independent family59 audit

This adapter replays the **owned independent checkers**, not the science constructor. It preserves every original science and checker byte. The science packet, original proof/audit documents, previous-source dependencies, and Pell source remain inert data.

## Required layout and dependencies

All input and output roots are required command-line arguments. They may be moved anywhere; no current-working-directory inference or historical-path fallback is used.

- `--packet`: the exact 60-file frozen science packet, including `PACKET_MANIFEST.json`
- `--audit`: the exact nine-file frozen independent audit
- `--dependencies`: the exact seven-file dependency directory using the filenames listed in `DEPENDENCY_FILES` in the adapter
- `--output`: an absent output directory whose parent already exists, disjoint from all input roots

Tested with Python 3.12.14 and SymPy 1.14.0 on Linux as an unprivileged uid 1000. Python and SymPy must already be installed. The adapter does not download, install, or update anything. Other runtimes are not certified by this test record; every run still must reproduce the expected bytes exactly before reporting success.

## Run from an extracted release

Substitute the actual extracted release directory and an absent output directory. For the supplied release layout:

```sh
python -B /path/to/release/tools/portable_tools/replay_family59.py \
  --packet /path/to/release/science \
  --audit /path/to/release/independent-audit \
  --dependencies /path/to/release/dependencies \
  --output /path/to/new-replay-output
```

The tools may instead be installed in another location; invoke their actual path. Input roots need only be readable and may be recursively read-only. A successful replay exits zero and writes exactly these five files:

1. `STATIC_INDEPENDENT_RECEIPT.json`
2. `AUTHOR_PACKET_SNAPSHOT.json`
3. `GEOMETRY_INDEPENDENT_RECEIPT.json`
4. `DEPENDENCY_RECEIPT.json`
5. `REPLAY_RECEIPT.json`

The first four must be byte-identical to their counterparts in the authenticated frozen audit. The fifth is the adapter's new summary. The conventional prose audits and original `AUDIT_RECEIPT.json` are authenticated, not computationally reproved or rewritten.

## Trust chain and redirection

The adapter embeds the frozen packet-manifest hash and frozen audit-receipt hash. It authenticates those anchors before trusting their complete inventories. It rejects empty path arguments, missing files, extra files or empty directories, symbolic links, special files, altered bytes, overlapping roots, and existing output locations. Parent-traversal components (`..`) are rejected before path normalization so they cannot hide a symbolic link. The seven dependency copies are authenticated against the already-authenticated `SOURCE_PINS.json`. Updating a file and its local manifest together does not bypass the embedded trust anchor.

The original independent checker source hashes are checked again immediately before compilation. Only the top-level path assignments are replaced in memory:

- `audit_static.py`: `ROOT` becomes the supplied science root and `OUT` becomes the supplied output root
- `audit_geometry.py`: `OUT` becomes the supplied output root

The original AST shapes and occurrence counts must match exactly. No source byte is changed on disk. The remainder of each checker is compiled unchanged with `optimize=0`, retaining its assertions even if the adapter is launched with `python -O`. Original historical paths remain inside authenticated provenance metadata and the route-shape comparison; they are never followed as a fallback. Reconstructing the dependency receipt preserves its source-identity strings while opening only the explicitly supplied relocated copies.

After execution the adapter compares all four regenerated files byte-for-byte and rechecks every input file's bytes, mode, and modification time, plus directory modes and modification times. It creates no bytecode cache in the frozen input directories.

## Re-run the relocation and rejection tests

The new test directory must not exist. Tests copy inputs into isolated staging trees; they do not chmod or edit the originals.

```sh
python -B /path/to/release/tools/portable_tools/test_replay_family59.py \
  --packet /path/to/release/science \
  --audit /path/to/release/independent-audit \
  --dependencies /path/to/release/dependencies \
  --adapter /path/to/release/tools/portable_tools/replay_family59.py \
  --work-dir /path/to/new-portability-test-directory
```

The recorded suite ran three positive replays from unrelated working directories with all input files mode 0444 and directories 0555; one replay used Python optimization. All five output files agreed byte-for-byte across the three runs. Python audit hooks denied historical-path opens, input opens for writing, and socket operations. The suite rejected 39 adapter negative controls before changing their default, effective, or normalized output targets, including self-consistent forged manifests, altered checkers/expected receipts, missing flags/roots/files, extra inventory entries, overlapping roots, links, parent traversal, and a FIFO. Three additional test-harness controls rejected work directories placed inside each original input root before any write.

The test result includes the original 12 static-checker mutation controls and the exact algebraic/geometry checks through their regenerated receipts. It does not rerun the author's fixture constructor or arithmetic-review programs. The copied `PORTABLE_TEST_RECEIPT.json` contains staging paths in negative-control diagnostics; those are an execution record, never required input locations.

## Limits

- This is an authenticated replay of a conventional mathematical audit, not a Lean proof certificate, physical simulation, or independent proof of all mathematical claims by computation
- Finite fixtures and synthetic multi-contact polygons retain the exact original scope limits; the synthetic polygon is not a physical family fixture
- The arithmetic claim remains a literal polynomial template, with no emitted general arithmetic DAG/compiler or source-specific gate ledger
- SHA-256 authentication relies on the trusted adapter/pins and collision resistance. An attacker who can replace the adapter or its runtime can replace this trust chain
- The code is not a sandbox for arbitrary Python. Only the authenticated, previously inspected owned checker sources are executed
- The test hooks are Python audit hooks, not OS-wide filesystem/network isolation. No network operation was needed. No network namespace or kernel security isolation is claimed
- Ordinary non-adversarial filesystem stability is assumed during a run. The adapter rejects links and checks metadata before/after, but is not a race-proof defense against a concurrent privileged attacker
- Input access times are not compared, since reads may update them. Input bytes, modes, modification times, and complete inventories are checked
- A failure after successful input validation may leave partial files in the newly created output directory; it never reports PASS without exact-output and final-input checks. Validation failures tested here create no output directory
- The original dependency names identify frozen earlier sources. Rechecking relocated copies proves byte identity to those pins, not independent upstream history/provenance or literature priority

The accompanying `PORTABLE_TOOLS_MANIFEST.json` records the shipped adapter, test program, documentation, review, and successful test/replay receipts. It is an inventory for release integration; the release's outer authenticated manifest should cover this manifest and all these files.
