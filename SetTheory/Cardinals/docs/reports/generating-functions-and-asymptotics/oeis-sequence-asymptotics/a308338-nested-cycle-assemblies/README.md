# Report 167: Asymptotics of assemblies of nested cycles

This package accompanies the 15-page report on A308338 and the
component-marked triangle A392471. It contains the LaTeX source, the
rendered PDF, bounded exact code, frozen published numeric fixtures,
and reproducible verification outputs.

The main result is an explicit count equivalent and a complex-uniform,
all-fixed-orders expansion in half powers of n with log-polynomial
coefficients. The report gives R1/R2, refined mean/variance, a credited
Gaussian limit, and a two-ceiling inverse that remains valid near integer
thresholds. The component asymptotics and generic expansive-assembly
CLT have prior sources, identified in the report and SOURCE_PROVENANCE.json.
No worldwide priority claim or complete beyond-all-orders transseries is made.

## Quick exact checks

Use Python 3.10 or later. The core companion needs only the standard library.
From the extracted package root:

    python companion/verify.py
    python -O companion/verify.py
    python companion/test_exact_nested.py
    python -O companion/test_exact_nested.py
    python -m unittest test_release
    python -O -m unittest test_release

Optional finite symbolic checks require SymPy (tested with 1.14.0):

    python companion/symbolic_checks.py
    python -O companion/symbolic_checks.py

The default exact comparison bounds are n=100 for counts and the integer
triangle, n=30 for independent rational power-series triangle extraction,
and n=7 for literal permutation/cycle-group enumeration. CLI inputs are
bounded and validated under both ordinary Python and -O. Exact finite
checks do not certify an asymptotic remainder, error constant, onset
threshold, decimal transcendental constant, or distributional error.
All numerical asymptotic diagnostics are uncertified; the shipped
companion uses no floating arithmetic in its core verification.

## Reproduce the exact arrays

The CLI writes JSON to standard output. Shell redirection is controlled
by your shell, so choose a new filename if preserving existing files matters:

    python companion/verify.py --include-data > regenerated_exact_data_100.json

The result must be byte-identical to data/exact_data_100.json. Without
--include-data it must match data/full_verification.json. See
companion/README.md for the independent recurrences, exact inverse,
fixtures, and optional symbolic checks.

## Build the PDF

The Linux/POSIX builder requires pdfTeX/LaTeX and the standard packages
named in Report167.tex, including Latin Modern and microtype. The tested
environment is TeX Live 2025 with pdfTeX 1.40.26. It uses a private fresh
format and fixed metadata, no shell escape, and up to six passes until
references stabilize. It rejects settled warnings, missing glyphs, and
overfull/underfull boxes.

    python build_pdf.py --output-dir reproduced_pdf

The destination must not already exist and its parent must exist.
The output is reproduced_pdf/Report167.pdf. With the same TeX installation,
two clean builds reproduce the supplied PDF byte for byte. Different
TeX/font/package versions may change bytes or layout. The builder copies
the source to the fresh destination and does not alter the packaged source
or PDF. No installed package is downloaded or modified.

## Verify and rebuild the archive

SHA256SUMS records the exact sorted allowlist in make_zip.py. That manifest
is included in the ZIP but does not hash itself. The ZIP file and any
unlisted review/render/build files are excluded. Check every listed hash:

    sha256sum -c SHA256SUMS

Create a deterministic stored ZIP with fixed member dates and modes:

    python make_zip.py --output Report167_Source_reproduced.zip

The output must be a new filename with an existing parent. Inputs must
be regular files; symlinks are rejected. Outputs are exclusively created
using descriptor-pinned parent directories; existing paths, symlinked
parents, traversal, and special files are rejected. The ZIP builder
verifies every listed checksum before writing and verifies its in-memory
archive. Failures can leave an incomplete newly created build directory
or file; no automatic cleanup or overwrite occurs. Choose another new
output path after a failed run. release_tools.py is Linux/POSIX-specific.

The package was checked in ordinary and optimized Python, built twice
from clean destinations, and replayed from an extracted archive. Exact
scope and final file hashes are recorded in verification_receipt.json
and SHA256SUMS. The receipt does not claim a formal proof certificate or
certified asymptotic numerics.

## Sources and limits

Public source URLs, exact contribution boundaries, and inspected/unread
coverage are listed in SOURCE_PROVENANCE.json and the bibliography.
Only frozen published numeric terms are distributed; third-party papers
and OEIS source snapshots are not bundled. The 2004 Erlihson--Granovsky
paper was not inspected; its CLT attribution is explicitly indirect via
the inspected later paper. No external publication, author contact,
repository change, or OEIS edit accompanies this package.
