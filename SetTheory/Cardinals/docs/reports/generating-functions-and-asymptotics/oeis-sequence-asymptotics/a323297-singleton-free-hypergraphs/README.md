# Report240: hypergraphs with no one-vertex edge intersections

This package accompanies `Report240.pdf`. It treats labelled 3-uniform
hypergraphs in which two edges never have exactly one common vertex. Isolated
vertices are allowed in OEIS A323297 and forbidden in A323296. The exact
component classification and exponential generating functions are prior work
recorded by Andrew Howroyd in 2019. The article gives explicit saddle
coefficients, controlled inversion, exceptional-component laws, and the two
fluctuation scales. See `SOURCES.md` for attribution and scope.

The article contains the proofs. The programs supply bounded independent finite
checks and reproducibility machinery. They do not certify asymptotic error
constants, an effective onset, or an exact inverse integer threshold.

## Contents

- `article.tex`, `sections/`: article sources
- `Report240.pdf`: frozen article PDF
- `code/exact_counts.py`: component recurrence, independent exponential-sum
  convolution, actual-edge-set enumeration, and exact marked identities
- `code/symbolic_coefficients.py`: weighted Gaussian algorithm, independent
  checks of E1/E2, cumulant derivatives, and inverse logarithmic coefficients
- `code/diagnostics.py`: explicitly NONCERTIFIED floating diagnostics
- `code/guard_tests.py`: finite input, filesystem, manifest, and archive guards
- `code/reproduce_zip.py`: replay of an actual archive in normal and optimized modes
- `code/*_receipt.json`: frozen default-command receipts
- `build.py`: immutable-source build and deterministic archive assembly
- `MANIFEST.sha256`: complete integrity inventory, excluding itself
- `COMPUTATION.md`: algorithms, bounds, numerical scope, and freeze procedure

## Reproduction

The tested environment uses Python 3.12, SymPy 1.14.0, mpmath 1.3.0, and
pdfTeX/LaTeX with the packages and fonts used by `article.tex`. Python 3.11 or
newer is required. PDF byte reproduction requires the same TeX toolchain and
fonts. Actual Python and pdfTeX versions are recorded in `build_checks.json`.
No network access or package installation is performed by a build.

From the extracted frozen package:

```sh
python -B build.py --verify-only
python -B build.py --output-dir /absolute/existing-parent/new-build
python -B code/reproduce_zip.py \
  --archive /absolute/existing-parent/new-build/Report240.zip \
  --output-dir /absolute/existing-parent/new-replay
```

Both output directories must be new, outside the package, with existing parents.
The tools refuse to reuse or merge into an existing destination. The optional
`--report-number 240` is checked; another number is rejected. `--output` is an
alias for the build's `--output-dir`.

The builder verifies every manifest entry and the exact source-tree inventory,
regenerates all four receipts, compiles a disposable source copy, requires the
PDF to match the frozen PDF byte for byte, and produces an external Report240.zip.
The ZIP has one `Report240/` prefix and contains every frozen package file.
The package never contains its own ZIP.

The archive replay tool requires the input ZIP's member contents to equal the
trusted package already running it. It never executes arbitrary ZIP-supplied
code. It extracts two independent copies, builds normally and with `-O`, and
compares all archive members and metadata, entire ZIP bytes, PDF, receipts, and
build checks. Both extracted sources and the trusted package must remain
unchanged. Replay evidence is written outside the package.

## Finite checks

```sh
python -B code/exact_counts.py
python -B code/symbolic_coefficients.py
python -B code/diagnostics.py
python -B code/guard_tests.py
python -B -O code/guard_tests.py
```

Each script accepts `--output /new/external/file.json`. Otherwise it prints JSON
to standard output. Existing files, source-tree destinations, live or dangling
symlink ancestors, missing parents, and dot path components are rejected.

The count checker defaults to n=640 for each counting method and both raw-moment
methods. It also checks both published prefixes, the isolate binomial transform,
tetrahedron deletion, mixed exceptional factorial moments of total order at
most three through n=32, and literal edge-set enumeration through n=8.

The symbolic checker implements the finite E-order prescription through order
four and verifies the displayed E1/E2 by a separate polynomial-exponential
calculation. It checks P0 through P8 and the reversed logarithmic expansion
through relative order L^-3. It does not claim a practical unbounded-order
implementation.

Diagnostics default to n=640 and 60 decimal working digits, with displayed
orders 32, 80, 160, 320, 640. They compare first saddle corrections, marked
moments, exceptional likelihoods, and deletion probabilities. All displayed
decimals and truncated Poisson sums are NONCERTIFIED; they are not interval
enclosures or effective asymptotic guarantees.

## Integrity and safety scope

Validation uses explicit exceptions and survives `python -O`. All child Python
commands include `-B`; each public process fixes the decimal integer-conversion
limit at 640 digits independently of ambient environment settings. Large exact
counts are recorded using bit lengths and signed binary SHA256 encodings.
No large count is converted to an unrestricted decimal string.

The builder writes no cache, log, temporary TeX artifact, or output into the
sources. TeX uses a private format/cache, restricted file access, and explicit
`-no-shell-escape`. The archive has fixed timestamps, modes, ordering, and stored
compression. These are bounded integrity and reproducibility checks, not a
sandbox against malicious code or hostile concurrent filesystem changes.
Hashes are integrity records, not digital signatures or authorship certificates.
No cross-platform or arbitrary-toolchain PDF-byte identity is promised.
