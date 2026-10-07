# Report192: weighted-depth towers and the critical Airy window

This self-contained, offline package accompanies Report192. Its mathematical
results and scope are stated in the manuscript. The finite exact checks are
supporting evidence, not proofs of asymptotic convergence or error bounds.

## Quick start

Python 3.10+ is sufficient for every mandatory numerical and package check:

    python3 -I -S -B reproduce.py
    python3 -I -S -B test_build.py
    python3 -I -S -B -O test_build.py

In an extracted release, also run:

    python3 -I -S -B verify_manifest.py

To create a new complete release (installed pdfLaTeX also required):

    python3 -I -S -B build.py --output "$(dirname "$PWD")/report192-release"

The parent directory must exist; the output directory must be fresh and
outside this package. Existing paths are never replaced. Use a fresh sibling
name for every replay or build. See README_REPRODUCIBILITY.md for details.

## Exact scope

- Integer recurrence and exact-height decomposition through n=48
- The 15 displayed official A096537 terms, n=0..14
- Nine complete official A096542 polynomial rows, n=0..8, at four rational shifts
- Independent exhaustive rooted Pruefer enumeration through n=7: 280392
  nonempty labelled trees, all exact-height cells and shift-two totals
- Independent positive level-composition sums through n=12
- Nonnegative height weights, path diagonal, and marked monotonicity checks
- Strict fixture, input, path, manifest, and build guards under normal Python and -O

The official A096537 page links a b-file for n=0..200. That b-file was not
retrieved or used. The n=15..48 regression values shipped here are explicitly
author-generated; they must not be described as 201 official terms checked.
See DATA_SOURCES.md and data/README.md.

## Optional diagnostics

    python3 -I -B code/diagnose_mpmath.py --heights 100 1000 --digits 50

This separate script requires mpmath. It produces uncertified numerical
illustrations only and never runs as part of a mandatory replay or build.

The public ZIP contains the manuscript, PDF, authored code and documentation,
bounded attributed integer fixtures, and generated verification receipts.
No downloaded article bodies, working notes, temporary logs, or caches are
included. No network access or third-party Python package is needed for the
core checks. No code publishes, uploads, installs software, or modifies OEIS.
