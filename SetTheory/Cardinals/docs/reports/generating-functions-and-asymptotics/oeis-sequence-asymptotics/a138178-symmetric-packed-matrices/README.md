# Report238: symmetric packed nonnegative matrices

This package accompanies the article in `Report238.pdf`. It concerns ordered
symmetric matrices with nonnegative integer entries and no zero line, counted
by total entry sum (OEIS A138178), with dimension, trace and repeated-cell
markers. The article supplies the mathematical proofs. The programs are bounded
finite verifiers and reproducibility tools, not proofs of asymptotic remainders.

The binary leading equivalent is established prior work of Cameron, Prellberg
and Stark (2006), Proposition 4.2. The unmarked exact identity is recorded in
OEIS A138178 and credited there to Jovovic (2009). See `SOURCES.md` for the
article's sources and the precise attribution and scope boundaries.

## Contents

- `article.tex`, `sections/`: article sources
- `Report238.pdf`: frozen, reproducible PDF
- `code/exact_counts.py`: integer polynomial recurrence, independent deletion,
  direct small matrix enumeration, involutions, and exact collision moments
- `code/symbolic_coefficients.py`: independent exact checks of the first two
  marked corrections; collision/binary first corrections; involution checks
- `code/diagnostics.py`: explicitly noncertified decimal diagnostics from exact
  integer counts and rational moments
- `code/guard_tests.py`: finite input, filesystem, manifest and ZIP guards
- `code/reproduce_zip.py`: actual archive replay under normal and optimized Python
- `code/*_receipt.json`: frozen receipts produced by the default script commands
- `build.py`: immutable-source build and deterministic ZIP assembly
- `MANIFEST.sha256`: complete integrity inventory, excluding the manifest itself
- `COMPUTATION.md`: algorithms, derivations, bounds and limitations

## Reproduction

The tested dependencies are Python 3.11 or newer, the versions in
`requirements.txt`, and a pdfTeX/LaTeX installation containing the packages used
by `article.tex`. The frozen PDF additionally requires the same TeX toolchain
and fonts. `build.py` records the actual Python and pdfTeX versions.

From the extracted package, run:

```sh
python -B build.py --verify-only
python -B build.py --output-dir /absolute/existing-parent/new-build
python -B code/reproduce_zip.py \
  --archive /absolute/existing-parent/new-build/Report238.zip \
  --output-dir /absolute/existing-parent/new-replay
```

Both output directories must be new, outside the source package, and have
existing parents. The commands never merge into an existing output directory.
The optional `--report-number 238` is checked; a different report number is
rejected. `--output` is an alias for the build's `--output-dir`.

A build verifies the manifest, regenerates and compares all four receipts,
compiles in a disposable directory with shell escape disabled, requires the
PDF to match the frozen PDF byte for byte, and writes an external `Report238.zip`.
The ZIP contains a single `Report238/` prefix and every frozen package file,
including PDF, receipts and manifest. The package never contains its own ZIP.
The external `build_checks.json` records hashes, checks and toolchain details.

The replay script first requires the supplied archive's members to equal this
trusted package's files. It does not run code merely because an arbitrary ZIP
contains it. It extracts two separate copies and builds one with normal Python
and one with `-O`. Both copies must remain unchanged. All member bytes, ZIP
metadata, complete ZIP bytes, PDF bytes, receipt bytes and build-check bytes
must match. The detailed replay result is external to the frozen package.

## Finite checks

```sh
python -B code/exact_counts.py
python -B code/symbolic_coefficients.py
python -B code/diagnostics.py
python -B code/guard_tests.py
python -B -O code/guard_tests.py
```

Each script accepts an optional `--output /new/external/file.json`. A preexisting
file, source-tree destination, symlink ancestor, missing parent or dot component
is rejected. Without `--output`, JSON is written to standard output.

The exact-count default reaches `n=640`. Its public large-recurrence limit is
640, independent inclusion–exclusion is capped at 32, collision-marked deletion
at 12, and direct matrix enumeration at 6. Small-marker numerators and
denominators have explicit bounds. Diagnostics default to `n=640` and 60 decimal
working digits. The documented maxima are safeguards for these routines, not
claims that every mathematically finite all-order workload is practical.

## Integrity and numerical scope

All checks use explicit exceptions and survive `python -O`. Every Python child
is invoked with `-B` explicitly, even if the caller ignores environment variables.
Every process sets the integer decimal-conversion limit to 640 digits; large
integer fingerprints use a documented binary encoding. No source-tree caches,
logs or build products are created. TeX uses private temporary format/cache
locations and `-no-shell-escape` for every executable invocation.

The count and symbolic receipts use exact arithmetic. Decimal diagnostics use
mpmath floating-point arithmetic and are **not interval certificates**. They do
not certify an error bound, numerical onset, all-order result, or total variation
estimate. Reproduction is byte-for-byte on the tested toolchain, not a claim of
identical output across arbitrary Python/SymPy/TeX versions. The SHA256 manifest
is an integrity record, not a digital signature or independent provenance proof.
