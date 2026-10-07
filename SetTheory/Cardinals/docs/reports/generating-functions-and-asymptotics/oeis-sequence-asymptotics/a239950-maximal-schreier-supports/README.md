# Report195: partitions with maximal Schreier support

This self-contained research package studies A239950: the number a(n) of partitions of n whose least part equals the number of distinct part sizes. The empty partition is excluded, so a(0)=0. See Report195.tex/PDF for the exact generating function, analytic coefficient asymptotics and correction terms, related distributional statements, and carefully bounded discussion of prior work.

The authoritative computation uses a positive integer dynamic program through n=1500, independently checked by enumerating all partitions through n=35 and comparing precisely the 58 displayed OEIS terms observed on 2026-10-04. Exact rational certificates establish the sign of the first correction and a negative real zero of F(q)/q. Finite computation supports these checks; it does not replace the asymptotic proof.

## Quick start

Python 3.10 or newer is required. The standard-library replay needs neither TeX nor network access:

    python -B reproduce.py --output-dir /absolute/path/to/new-replay

Build with an already installed pdfLaTeX stack:

    python -B build.py --output /absolute/path/to/new-build

The output directory must be an absolute, nonexistent path outside this package, with an existing nonsymlink parent. Relative paths such as `../build`, traversal components, symlinks, existing outputs, and unlisted source files are deliberately rejected.

The build emits Report195.tex, Report195.pdf, Report195_code.zip, and ARTIFACTS.json. The ZIP includes a verified closed inventory of sources, source data, generated exact counts and receipts, the PDF, and SHA256SUMS.json. No downloaded papers or private research files are included.

## Verification commands

    python -B test_build.py
    python -O -B test_build.py
    python -B test_build.py --integration

The integration test performs actual ordinary/optimized builds, byte-compares their artifacts, safely extracts the closed release, reruns its exact checks, and rebuilds it byte-identically on the same installed software stack.

Inside an extracted release:

    python -B verify_manifest.py

Optional symbolic verification of the first two corrections requires an installed SymPy and explicit opt-in; it is not an unrestricted all-orders coefficient engine:

    python -B reproduce.py --symbolic --output-dir /absolute/path/to/new-symbolic-replay
    python -B build.py --symbolic --output /absolute/path/to/new-symbolic-build
    python -B test_build.py --integration --symbolic

See README_REPRODUCIBILITY.md for algorithms, arithmetic, determinism, checks, and limits. DATA_SOURCES.md records provenance and source-screen scope.
