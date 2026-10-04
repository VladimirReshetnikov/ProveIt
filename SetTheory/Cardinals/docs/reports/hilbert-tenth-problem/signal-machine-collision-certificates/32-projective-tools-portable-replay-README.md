# Portable replay of the report-62 independent audit

This release-only adapter authenticates complete relocated science and audit trees and runs the **unchanged independent reviewer checker**. It does not run the author checker, a compiler, a physical simulator, or a stored collision schedule. The replay reproduces the audit's 157 named algebraic, structural and authentication checks.

## Inputs and trust anchors

- Science tree: the complete frozen `projective-signal-shears62-20261004` packet, 14 files and three directories including its root. Both copied prior proof dependencies are included and remain inert
- Audit tree: the complete `audit-projective-signal-shears62-20261004` packet, nine files and two directories including its root
- `PINNED_INPUTS.json`: explicit complete file/directory inventory of both trees, with file byte lengths and SHA-256 values
- Pinned inventory SHA-256: `d20b85535be14fb12c2494447b8326dc260310c2d9441677f48866eb6e2658f8`
- Unchanged checker: `independent_static_audit.py`, SHA-256 `a945491e115e5f96dfc11e3d6e714ef367ecc0daddfce425d8310cb5949f4fec`
- Frozen main proof: SHA-256 `502e90e091eabc0a6c8eb6092e73f4407ae84f143d337be8a4a633a3f85a7c47`

The pins include the source manifests and checksum files themselves; they do not rely on those self-excluding manifests as the input inventory. Extra and missing entries fail. The pins file is authenticated against the constant in `replay.py` before parsing, and the parser additionally rejects malformed schemas and duplicate keys.

Use a trusted Python runtime with **SymPy 1.14.0 already installed** on a POSIX filesystem supporting `O_NOFOLLOW`. No package installation or network action occurs during replay. The version is part of the exact expected mathematical evidence. Another SymPy version is deliberately rejected rather than assumed equivalent.

## Run after relocating a complete report release

The report release layout is:

- `science/frozen-proof/`: full unchanged science tree
- `audits/scientific/`: full unchanged independent audit tree
- `tools/portable-replay/`: this adapter, pins, tests and review

From any working directory, substitute the canonical absolute release root and a fresh external output path:

```sh
RELEASE=/absolute/path/to/report62-projective-signals-release-20261004
python -I -B "$RELEASE/tools/portable-replay/replay.py" \
  --science-root "$RELEASE/science/frozen-proof" \
  --audit-root "$RELEASE/audits/scientific" \
  --pins "$RELEASE/tools/portable-replay/PINNED_INPUTS.json" \
  --output-root /tmp/report62-replay-new
```

The output path must **not already exist**, its parent must already exist, and it must be outside the science tree, audit tree, adapter directory and pins file. Use a different fresh name for each replay. All supplied paths must be absolute with canonical spelling: no symbolic-link component, `..`, repeated slash or trailing slash. Spaces and Unicode are supported when shell-quoted.

The adapter prints a JSON success object pointing to `replay_receipt.json` only after all comparisons pass. A rejected or failed run exits with status 2 and a `REJECTED:` diagnostic. Preflight rejection creates no output. A failure after execution starts can leave a partial fresh output directory as evidence; it has no success receipt and must not be reused.

The adapter also accepts direct paths to separately relocated complete science and audit copies. The tools-only bundle does not itself duplicate those two input trees; they accompany it in the complete report release.

## Exactly what runs and what changes

The independent checker contains historical absolute bindings for its science root and output directory. The adapter reads its authenticated source bytes and passes them unchanged to `compile(..., optimize=0)` and `exec`. It does not rewrite, patch, reformat, copy-modify, or regenerate the checker. `optimize=0` preserves the checker's assertions even if the adapter is invoked under `python -O` or `python -OO`.

A narrow import facade affects only that execution's `from pathlib import Path` statement. It maps the historical science root to the explicit relocated science tree, keeps the checker's `__file__` at the actual authenticated audit source, and sends its evidence-directory operations to the new external output. No global Python module is monkeypatched. Actual source stat results are used; metadata is not invented to make relocation pass.

All mathematical code executed belongs to the independently owned checker. The full author `static_algebra.py`, `RULES44.json`, original evidence, proof dependencies and other science files are authenticated and read only as inert data. The facade's checks are tailored to this authenticated fixed checker and its authenticated fixed manifest; its lexical path membership checks are **not a general-purpose traversal or execution sandbox**.

## Evidence comparisons and preservation

These outputs match the frozen audit evidence **byte-for-byte**:

1. `evidence/independent_checks.json`
2. `evidence/rule44_static_review.json`
3. `execution_stdout.json`, compared to the audit's `evidence/run_stdout.json`

Relocated filesystem modes, directory sizes and modification times can legitimately differ from the original machine. Accordingly, the adapter supplies a freshly measured science metadata baseline in the external output's `evidence/frozen_before.json`. The unchanged checker produces `evidence/frozen_after.json`; those two **actual relocation-specific snapshots** must be byte-for-byte identical. The original two snapshot files remain authenticated, unmodified, inert audit inputs. No claim is made that transport metadata must equal its historical values.

In addition, the adapter reauthenticates **both complete science and audit inventories** after execution, rehashing every file and comparing exact before/after in-memory metadata tuples: device, inode, full mode, link count, size and nanosecond modification time. The pins file receives the same stability check. The science before/after JSON pair is serialized; the extra audit-tree preservation check is an in-memory tuple comparison recorded in the receipt, not a second serialized JSON snapshot pair. Access times are intentionally excluded because reads can update them.

The fresh output inventory is checked explicitly. Generated files are created exclusively, so an existing path is never silently overwritten. Hard-linked regular files, symbolic links, nonregular files, overlapping/aliased roots and output ancestry aliases are rejected.

## Verification included

`TEST_RESULTS.json` records 42 release tests, including:

- Ordinary and optimized Python relocation
- Read-only source/audit/pins relocation, also under optimized Python
- Corruption of proof, author source, rule table, each proof dependency, checker, expected evidence, old snapshots and audit manifest
- Extra and missing files/directories
- Symbolic links, hard links, special files, lexical aliases and overlapping output/input roots
- Malformed pins and direct schema rejection checks

A separate reviewer supplied 24 additional CLI cases, including read-only relocation with changed nanosecond times, Unicode and spaces, and `python -OO`. Its source-bound report and evidence are in `independent_review/`.

To rerun the owned release test harness, provide the complete original or relocated inputs and a results path outside those inputs:

```sh
python -I -B /absolute/path/to/tools/portable-replay/test_replay.py \
  --science-root /absolute/path/to/science/frozen-proof \
  --audit-root /absolute/path/to/audits/scientific \
  --results /tmp/report62-release-tests.json
```

The tests modify only disposable copies. They retain their temporary test tree for diagnosis and never run author/upstream code. Test results are release evidence, not additional mathematical theorems.

## Limits

This is an authenticated replay adapter, **not an OS or network sandbox**. It assumes trusted Python, the standard library, installed SymPy 1.14.0 and its dependencies, trusted adapter/checksum distribution, and a quiescent filesystem. `-I -B` avoids ordinary Python environment/path and bytecode surprises but does not create operating-system isolation. File-descriptor checks and post-run authentication detect ordinary changes; there is no security claim against hostile runtimes, kernel/mount manipulation, concurrent adversarial races, or alteration of the adapter itself. Pins prove identity only relative to the trusted adapter and supplied release seals.

Replay acceptance confirms reproducibility of this bounded static audit. The conventional proof, inherited GL₂ compiler, exact chamber and phase arguments remain essential. It does not certify novelty, arbitrary GL₃ realization, minimal counts, or continuation after a Zeno accumulation.
