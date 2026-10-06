# Report239: symmetric sign matrices and free degree coordinates

This package accompanies `Report239.pdf`. The model is an ordered symmetric
matrix with entries in {-1,+1}, including its diagonal, and with every row sum
nonnegative. By symmetry this also imposes nonnegative column sums. The exact
bridge replaces its diagonal by edges to one extra, unrestricted graph vertex.
The resulting counts are OEIS A027832, with OEIS offset 1. The empty matrix has
count 1 and is recorded separately.

The article proves leading relative asymptotics and the critical window for
specified free graph coordinates, conditional on its cited dense-enumeration
input. The programs check finite identities and constants. They do not establish
an effective asymptotic remainder, a numerical onset, or all-order expansions.
Attribution and the limits of the historical search are in `SOURCES.md`.

## Contents

- `article.tex`, `sections/`: the article sources
- `Report239.pdf`: the frozen reproducible PDF
- `code/exact_counts.py`: exact capped-graph recursion, all 17 OEIS terms,
  literal small symmetric sign matrices, exhaustive small mixed graphs,
  exact Harris--FKG inequalities, and finite capped-binomial variance checks
- `code/oeis_prefix.json`: source-linked transcription of the 17 displayed terms
- `code/constant_certificate.py`: exact rational enclosures of ell and constants
- `code/diagnostics.py`: explicitly NONCERTIFIED finite-order illustrations
- `code/guard_tests.py`: bounded API, CLI, filesystem, manifest and ZIP checks
- `code/reproduce_zip.py`: actual archive replay under normal and optimized Python
- `code/*_receipt.json`: four frozen receipts produced by the default commands
- `build.py`: immutable-source build and deterministic ZIP assembly
- `MANIFEST.sha256`: complete integrity inventory except for the manifest itself
- `COMPUTATION.md`: algorithms, bounds, certificate derivation and limitations

No third-party papers, research notes, credentials, network dependencies or
private audit files are included. The recorded OEIS numbers are a finite test
fixture, not a copied article or paper.

## Reproduce

Python 3.11 or later and the matching pdfTeX/LaTeX toolchain are required. Python
uses its standard library only. The build records actual interpreter and
pdfTeX versions; arbitrary toolchain versions need not reproduce identical bytes.

From the extracted `Report239/` directory, run:

```sh
python -B build.py --verify-only
python -B build.py --output-dir /absolute/existing-parent/new-build
python -B code/reproduce_zip.py \
  --archive /absolute/existing-parent/new-build/Report239.zip \
  --output-dir /absolute/existing-parent/new-replay
```

The output directories must be new, outside the source package, with existing
parents. Existing outputs are never merged or replaced. `--output` is an alias
for the build's `--output-dir`. `--report-number 239` is optional; other report
numbers are rejected.

The build verifies every source hash and the complete file/directory inventory,
regenerates all four receipts, compiles TeX in a disposable directory with a
private format and shell escape disabled, and requires the PDF and receipts to
match the frozen versions byte for byte. There are seven top-level output files:
`Report239.pdf`, `Report239.zip`, `count_receipt.json`,
`diagnostic_receipt.json`, `certificate_receipt.json`, `guard_receipt.json`, and
`build_checks.json`. A separate `logs/` directory contains process logs.

The ZIP contains every frozen package file under one `Report239/` prefix,
including the PDF, receipts and manifest. It contains no copy of itself. The
replay program accepts only an archive whose file bytes match the trusted
package running it. It extracts two actual source copies and rebuilds them with
normal Python and with `-O`. Every member's bytes and ZIP metadata, complete
ZIP bytes, PDFs, four receipts, and build-check bytes must match. Both extracted
source trees, the original trusted tree, and the supplied ZIP remain unchanged.

## Run individual checks

```sh
python -B code/exact_counts.py
python -B code/constant_certificate.py
python -B code/diagnostics.py
python -B code/guard_tests.py
python -B -O code/guard_tests.py
```

Each script can write to a new external file with `--output /new/path.json`;
without it, the receipt is printed to standard output. Validation precedes the
expensive computation. Explicit exceptions preserve checks under `python -O`.
Every Python child has explicit `-B` and `-X int_max_str_digits=640` options, and
every process sets the decimal conversion cap independently of its environment.
No cache or generated file is written into the frozen sources.

The exact-count default regenerates all 17 published terms, n=1 through 17.
Literal sign enumeration stops at n=5 and direct graph enumeration at M=6.
General capped vectors have at most 12 vertices; mixed counts have M<=18 and
k<=8, or a trivial full cap. A per-computation state/transition budget adds a
second stop. Diagnostics are bounded to M<=2001. Certificate output is restricted
to 20--40 decimal digits. See `COMPUTATION.md` for exact API domains.

## What is certified

Count and inequality receipts use exact integers. The constant certificate uses
rational interval arithmetic, alternating Taylor remainders, Machin's identity
and integer square roots. It rigorously encloses its named constants. Its
30-digit intervals do not certify a finite-n counting approximation.

Diagnostics use ordinary floating-point arithmetic, including their saddle
searches and critical-window ratios. They are NONCERTIFIED illustrations.
The SHA256 manifest establishes integrity, not authorship or independent
provenance. Filesystem guards cover the documented finite cases; this package
is not a sandbox against hostile concurrent filesystem changes.
