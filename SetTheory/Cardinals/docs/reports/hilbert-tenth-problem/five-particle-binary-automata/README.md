# Report 15: globally reversible binary computation with five particles

Read `report15.pdf` for the full mathematical construction, domain qualifications, exact gate/radius/time ledger, clean exact targets, and counted finite-horizon natural and nonnegative-real polynomial certificates. `report15.tex` and its three included section files are editable LaTeX sources.

## What is proved and what is materialized

- A finite all-input isolated-swap compiler builds one globally reversible, number-conserving binary CA from a finite partial-injective two-counter source. Every valid simulation configuration has exactly five ones
- Classical reversible two-counter universality supplies the universal existence corollary. A literal universal transition table is not materialized here
- A complete one-increment accepting example and its 1,394-frame reflected raw orbit are provided, along with a clean-target wrapper and its 5,670-frame orbit
- Fixed source horizon H gives an explicit degree-at-most-four integer SOS polynomial with an empty-or-singleton complete natural witness fiber. A paid selector-norm extension has the same fiber over the nonnegative real orthant. H is syntax, not an unbounded polynomial input
- The clean target restores input counters and is input-dependent. Periodicity universality would need an additional infinite-continuation premise and is not an unconditional claim
- The separate byte-preserved Report 12 supplies the matching four-mass lower bound for finite-pattern and exact-target reachability. Its proof and assumptions remain a separate dependency

No novelty/priority claim or proof-assistant formalization is asserted.

## Quick start

Requirements for exact replay: Python 3.10 or newer, standard library only.

    python replay.py

The runner verifies SHA256SUMS, creates a temporary copy, runs producer tests, independent normal and optimized API and certificate audits, independent geometric/fixture checks, full raw orbit regeneration, four exact certificate CLI regenerations, and deterministic vector-figure regeneration. It does not alter this extracted release. Temporary test logs are not release artifacts. It prints a concise final receipt and fails immediately on any discrepancy.

Requirements for PDF rebuild: a normal TeX Live installation with the packages listed in `report15.tex`.

    sh build.sh

The build uses a private `.build` directory for caches and intermediate output. The checked PDF is already included. The vector renderer has no dependencies beyond Python and can be rerun directly:

    python tools/render_trace.py

## Files

- `compiler/`: one audited compiler, source schema, fully materialized source tables, raw traces, fixture receipts and replay tests
- `compiler/checks/`: independent ring, geometric stress and full raw-trace reconstruction checks
- `certificates/`: one audited polynomial emitter, exact producer tests, four polynomial examples and their full witnesses
- `audits/`: independent audit scripts and scope/provenance summary
- `figures/`: raw-trace vector PDF and SVG
- `companion-report12/`: unchanged authored lower-bound PDF, LaTeX and vector figure, with its original hash manifest
- `SHA256SUMS`: SHA256 of every bundled file except the manifest itself

The archive contains no third-party primary-source PDFs, screenshots, raw private working notes, execution logs, caches or hidden repositories. Primary literature is attributed and linked in the article. The lower-bound companion's earlier discussion of an unavailable binary upper bound should be read chronologically; this report supplies that separate upper bound.

## Practical conventions

One full edge-plus-phase composition is one CA step. The radius is the sum of factor radius bounds. Normalized certificate branches do not change the original CA parameters. Only exact natural source IDs are accepted; certificate real testing uses exact rational values, not floating-point approximations. The mathematical real-orthant theorem itself covers every nonnegative real witness.
