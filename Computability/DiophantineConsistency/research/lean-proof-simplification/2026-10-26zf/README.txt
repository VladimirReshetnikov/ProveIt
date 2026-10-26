FOUR REMAINING LEAN PROOF SIMPLIFICATIONS FOR PROVEIT
26 October 2026

Start with report.pdf (reading copy) or report.tex (complete LaTeX source).
The four recommendations are:
  1. Specialize multiplication's existing left-successor law at zero.
  2. Derive discrete internal-natural order from set-successor membership.
  3. Apply the existing linear coefficient bound twice to bound the square.
  4. Normalize powers to 4^r and prove a fixed quadratic inequality.

STATUS
These are mathematically reviewed, UNCOMPILED Lean source candidates.
No Lean/Lake executable was available during this review. No kernel acceptance,
axiom-set equality, full downstream integration, or performance result is claimed.
Static checks and finite arithmetic diagnostics are separately identified.

BASELINE AND NOVELTY
Source commit: 89226e3921bce3e8949fadd12d3efb6914c7630c
Final exclusion cutoff: 7df43cdfacb490cd3ca3acd23e39027efebf8801
All eight target files are unchanged between the two commits.
Prior proposals were treated as already available, including optional sketches.
The audit covers 23 placed research packets (a--w) and five incoming archives.
See audit/prior-proposals.txt for the scoped exclusion ledger and caveats.

The patches apply to the pinned maintained source. They are not evidence of a
compiled branch containing every prior proposal. On a later branch, transplant
the new argument into the current file and resolve nearby prior changes. Do not
overwrite newer source with the complete candidate files included for review.

SOURCE DELTAS
Four patches compose to eight files: 1,089 -> 1,045 physical lines, a prospective
44-line reduction and 1,636 fewer UTF-8 bytes, including helpers and wrappers.
The optional SuccAddOrder and arbitrary-power examples are excluded from these
counts. The source measure is not a claim about the virtual post-adoption tree.

CONTENTS
  report.tex / report.pdf       Full article, theorem links and rationale
  patches/01-...04-...          Individual narrow changes
  patches/combined.patch       Sequential composition of the four patches
  source-snapshot/             Original eight files with their repository paths
  candidate-source/            Complete eight-file result for review
  lean/                       Five fresh-namespace examples, all uncompiled
  audit/                      Prior-proposal ledger, hashes, freshness comparison
  evidence/                   Metrics, math review, diagnostics, QA, tool status
  notes/                      Detailed source and dependency notes
  scripts/                    Portable validation and replay commands
  MANIFEST.sha256              Final member integrity hashes (excluding itself)

VERIFY WITHOUT LEAN
From this directory, using Python 3.9+ and git:
  python3 scripts/verify_bundle.py
  python3 scripts/validate_sources.py
  python3 scripts/check_mathematics.py

The integrity check reports added local files separately. The source validator
checks hashes, original theorem headers, imports, line/byte counts, and both
patch-composition routes in temporary directories. It does not edit a checkout
and does not compile or type-check Lean. The math diagnostics check finite
examples and an exact polynomial certificate; they are not universal proofs.

REPLAY WITH LEAN
Use a complete disposable ProveIt checkout with the recorded source and
dependencies. This archive intentionally omits the full repository and Mathlib.
The required environment is leanprover/lean4:v4.32.0 and the Mathlib revision
81a5d257c8e410db227a6665ed08f64fea08e997 from lake-manifest.json.

First build the original imported project modules, if the checkout has no build
outputs, then compile the standalone candidates:
  python3 scripts/replay.py --repo /absolute/path/ProveIt --mode prototypes \
    --output /absolute/path/prototype-results

To check the actual integration, apply the narrow patches only in a disposable
checkout after reviewing them. For the exact pinned source, from its root:
  git apply --check /absolute/path/to/this-bundle/patches/combined.patch
  git apply /absolute/path/to/this-bundle/patches/combined.patch

Then from this bundle run:
  python3 scripts/replay.py --repo /absolute/path/ProveIt --mode integration \
    --output /absolute/path/integration-results

The replay tool itself never applies patches. Integration mode requires all
eight source files to match the recorded candidate hashes, builds their modules
in dependency order, then runs selected existing project checks when present.
Both modes check the pinned toolchain/dependency manifest, stop at the first
failure, and write result.json plus per-command logs. A rebased integration must
record its own source hashes and run the appropriate project checks; it cannot
be reported as this exact candidate without updating the evidence.

BUILD THE ARTICLE
Requires XeLaTeX, standard TeX Live packages, Latin Modern and DejaVu Sans Mono.
  bash scripts/build_report.sh
The script makes three passes in a temporary directory, then replaces report.pdf.
Rebuilding may change PDF metadata and therefore the bundled SHA-256 checksum.

READING ORDER
The unit specialization is the smallest first replay. The coefficient change
has a clear two-file dependency adjustment. The power inequality is independent.
Adopt the value/discrete-order bridges as one coherent five-file change. Keep
the optional typeclass registration and higher-power generalization separate
until an actual client justifies their extra API surface.

ProveIt repository: https://github.com/VladimirReshetnikov/ProveIt
