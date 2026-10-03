# Report 17: portable startup-optimization reproducibility

The literal source is exactly the new optimized machine, SHA-256
`fa61d06178d718511232a80a05e02192d940fde3c273f0c202f0623253b2ade3`.
Only four incoming history-label pairs change at the five-counter layer.
All three-counter data operations and the complete clean-loader domain remain.
The expanded source still has 122,622 controls and 141,561 literal branches.

## Offline replay

The replay was tested with Python 3.12 on Linux; the scripts use Python 3.9+
standard-library features and LF text output (use a Unix-like environment).
No package installation,
network access, external release, primary-paper PDF, or user-specific path is
needed. Allow about 0.5 GB of temporary disk and 1 GB of free memory. Run from
this directory after extracting the complete release:

```sh
python -B verify_manifest.py
python -B run_checks.py
```

The aggregate checks all known scientific-input SHA-256 pins, verifies the exact
manifest inventory, then runs every verification stage in **separate fresh
normal and `-O` copies**, with isolated Python startup. It checks identical
normal/optimized results, canonical receipt/trace equality, and unchanged
non-generated inputs. Corrupt-input and missing-baseline-pin negative controls
must fail. Network construction and external-data reads are explicitly denied
and negatively tested. No delivered file is modified and no logs or caches are
created in the supplied package. The final JSON printed to the terminal is the
fresh replay result. `replay-receipt.json` records the packaging-time run of this
same harness. Runtime duration varies by Python version and computer.

The audit guard enforces the stated restrictions for these standard-library
scripts; it is not a security sandbox for malicious Python/native code. Python's
runtime installation is available, while external research data is not.

To rerun an individual checker, use `python -B checker_name.py`, for example:

```sh
python -B independent_relabel_check.py
python -B verify_exact_delta.py
python -B verify_rebuild.py
```

Individual checkers regenerate their named JSON receipts/traces **in the current
package directory**. These deterministic outputs should remain byte-identical.
For a completely non-mutating invocation, use the aggregate harness above.
`python -B build_source.py` regenerates the seven optimized table/build files.
`python -B loader.py --left 101 --right 01 --particles` prints a clean input and
five-particle coordinates without allocating CA factors.

The aggregate's `--record` flag is for release authors only: after both modes
pass and agree, it replaces the canonical generated artifacts and saved replay
receipt. A release author must run `python -B write_manifest.py` to regenerate the
exact manifest afterward. This
flag is unnecessary for verification and is never used by the default command.

## Contents and scope

- `source.json`, the layer tables, certificates, and pinned source dependency:
  complete literal construction and all finite verification inputs
- `OPTIMIZATION.md`, `PROOF.md`, `independent-macro-audit.md`, and
  `independent-relabel-audit.md`: unbounded invariants and the clean-input
  paired-boundary time comparison, with explicit inherited provenance
- `baseline/`: original generator, original loader, and mandatory seven-output
  hashes; the old 54 MB table pair is regenerated temporarily, never duplicated
- `exact-delta-receipt.json`: four pair swaps, eight changed five-counter rows,
  expanded-name differences, unchanged dimensions, and old/new clock comparison
- `initialization-receipt.json` and `empty-*-trace.json`: actually traversed
  startup and exactly one first TM transition, with every literal row recorded
- `baseline-rebuild-receipt.json` and `byte-exact-rebuild-receipt.json`: exact
  generated-table comparisons, distinguished from external-release preservation
- `PORTABILITY.md`, `PROVENANCE.json`, and `historical/`: readable adaptation
  ledger and bounded historical provenance
- `manifest.json`: exact file inventory, sizes, and SHA-256 digests, excluding
  only the manifest itself; extra files, missing files, and symlinks are errors

Empty input executes 138 literal steps through initialization, then 210 more
through the first TM transition, for 348 executed steps. The corresponding CA
clocks are **predicted**, not CA executions. The old 79,936,151,060,302-step
literal startup is a theorem-derived clock, not an executed two-counter trace.
The nonzero-scratch `T=1` literal prologue is likewise predicted, not traversed.
Finite tests corroborate the separately supplied all-input proofs; they do not
prove universality by experiment or constitute a proof-assistant formalization.
Primary-paper visual evidence is historical, and the four-mass lower-bound
report is an external mathematical dependency, not part of this offline replay.

## Orientation-optimality addendum

`orientation-addendum/` contains the independently audited finite-trace
first-encounter theorem, including simultaneous clean-startup optimality among
static orientations of these fixed templates. Exactly `2^227` of the `2^233`
assignments attain that startup optimum. These are proof notes, not another
source or a global optimality claim. The aggregate verifies their sealed
identity in both modes with `verify_orientation_pins.py`; it does not claim
new execution coverage for the theorem's inherited arithmetic corroboration.
