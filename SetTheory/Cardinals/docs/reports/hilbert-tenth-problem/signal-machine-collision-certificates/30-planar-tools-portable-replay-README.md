# Portable independent-audit replay for Report60

This tool executes only the three frozen, independently owned audit checkers.
All scientific programs remain inert. It reproduces finite supporting evidence;
it does not re-prove the universal mathematical theorems or build Lean.

## Requirements and invocation

Python 3.11 or later, with SymPy 1.14.0 already installed. The wrapper forces
`optimize=0` when compiling every independent checker, retaining arithmetic
assertions even if the wrapper is launched with `python -O`.

All arguments must be canonical absolute paths. The nine selected science,
audit, and dependency roots must be disjoint strict descendants of the explicit
release root. The adapter directory must not overlap those nine roots.

For the distributed release layout, replace `/ABS/RELEASE` and
`/ABS/NEW-EXTERNAL-OUTPUT` below:

```sh
python -B /ABS/RELEASE/tools/portable-replay/replay.py \
  --release-root /ABS/RELEASE \
  --physical-science-root /ABS/RELEASE/science/physical \
  --geometry-science-root /ABS/RELEASE/science/geometry \
  --arithmetic-science-root /ABS/RELEASE/science/arithmetic \
  --quadratic-science-root /ABS/RELEASE/science/quadratic \
  --physical-audit-root /ABS/RELEASE/audits/physical \
  --geometry-audit-root /ABS/RELEASE/audits/geometry \
  --arithmetic-audit-root /ABS/RELEASE/audits/arithmetic \
  --quadratic-audit-root /ABS/RELEASE/audits/quadratic \
  --dependencies-root /ABS/RELEASE/dependencies \
  --output /ABS/NEW-EXTERNAL-OUTPUT
```

The output directory must not exist, even if empty. Its parent must exist.
Output is forbidden anywhere inside the release or adapter, inside any selected
input root, or above an input root. Symlink roots, noncanonical aliases,
symlink entries, hardlinked files, and unexpected/missing input-tree entries
are rejected. No scientific or independent-checker bytes are edited.

`INPUT_PINS.json` authenticates the exact content inventories of all nine
selected trees, including the independent source files and expected outputs.
Its own SHA256 is fixed in the adapter source. Metadata may legitimately differ
in a relocated or read-only copy; the complete actual inventory, bytes, modes,
link counts, and nanosecond mtimes must remain unchanged during each replay.
The complete release and adapter are included in this preservation check.

## What runs

- Physical: unchanged `independent_static_audit.py`, with only its runtime
  `SRC` and `OUT` bindings set to the explicit roots. A new run-local inventory
  baseline is supplied; its frozen provenance inventories are never rewritten
- Geometry: unchanged path-free `independent_exact_checks.py`, with stdout
  captured exactly, including its trailing newline
- Arithmetic: unchanged `audit_exact.py` with all six of its required explicit
  arguments. Two authenticated Report59 dependencies are copied into a read-only
  output-local logical view. The copies are ordinary files, never links

The quadratic scientific and audit trees are authenticated and preserved as
inert inputs only. They have no owned independent executable checker, so no
independent executable replay is claimed for that companion. Its author
`verify_exact.py` is never executed.

Every owned source is hash-checked immediately before its verbatim compilation.
No author compiler, scientific checker, schedule, physical simulator, or
upstream executable is imported or run. Historical paths inside provenance are
logical records only. A runtime I/O guard rejects checker reads outside the
explicit source/audit/adapter roots, installed Python libraries, and fresh
output; it rejects writes to inputs and outside output. This guard supplements
pinned-code review; it is not advertised as a sandbox for hostile Python.

## Exact expected-output checks

Seven byte comparisons are mandatory:

1. Physical `independent_results.json`
2. Physical `run_stdout.json`
3. Geometry `independent_results.json` against its normal baseline
4. The same geometry bytes against its optimized baseline
5. Arithmetic `EXACT_RECEIPT.json`
6. Arithmetic `RECONSTRUCTED_SCHEMAS.json`
7. Arithmetic `AUDIT_RUN.txt`

Run-local inventory snapshots compare with each other, not with historical
metadata from another copy. `REPLAY_RECEIPT.json` records every expected-output
hash and comparison, all selected roots, and source preservation. Before/after
inventories include the complete release. `OUTPUT_INVENTORY.json` inventories
outputs present before that inventory itself is written; it does not hash itself.

## Relocation and guard regression tests

For the standard distributed layout:

```sh
python -B /ABS/RELEASE/tools/portable-replay/selftest.py \
  --release-root /ABS/RELEASE \
  --output /ABS/ANOTHER-NEW-EXTERNAL-DIRECTORY
```

The selftest copies the release into disposable new directories, runs complete
normal and read-only relocated/optimized replays, exercises guard-negative
cases, and verifies the original release inventory is unchanged. It never
modifies the supplied original release. The output records commands, exit
statuses, exact diagnostics, and full-run receipts. Only the pinned independent
checkers execute through `replay.py`.

Scientific caveat: the arithmetic audit records a minor step-count wording
erratum in `audits/arithmetic/ERRATA.json`; replay preserves the scientific
packet and its explicit audit qualification rather than editing either.
