# Report200: Beyond the leading count of commutative magmas

A self-contained article and reproducibility package for OEIS A001425.
Prepared 4 October 2026.

## What is proved

The objects are arbitrary commutative binary operations, with diagonal entries;
there is no associativity, identity, or idempotence requirement. The exact
Burnside count and leading equivalent are established background already in
OEIS. The article derives exact nonidentity symmetry sectors, convergent
rational-coefficient amplitudes, and a global finite-n remainder after any
fixed defect. It also proves leading labeled/unlabeled nonrigidity probabilities,
the typical transposition-generated automorphism group conditional on
nonrigidity, and an eventual two-ceiling inverse enclosure.

The inverse uses the exact Gamma identity background and exact finite-defect
sectors. Only the unrounded real interval has superexponentially shrinking
width in the root variable. Its two ceilings can differ by one arbitrarily
far out. No effective inverse onset or absolute originality claim is made.

Read Report200.pdf, or edit/rebuild the complete Report200.tex source.
The public ZIP contains no third-party PDFs or external research notes.

## Dependencies

- Python 3.9 or later for exact-only code; Python 3.9+ with pathlib.is_relative_to
  for the package builder
- SymPy 1.14.0 and mpmath 1.3.0 for a complete data replay, pinned in
  code/requirements.txt
- pdfLaTeX/pdfTeX, kpsewhich, and a TeX installation with the packages used by
  Report200.tex (amsmath, amssymb, amsthm, mathtools, lmodern, microtype, geometry,
  booktabs, array, longtable, xcolor, enumitem, fancyhdr, hyperref)
- Poppler's pdfinfo/pdftoppm is useful for independent visual inspection but is
  not a build dependency

The reference build uses pdfTeX 3.141592653-2.6-1.40.26 (TeX Live 2025/dev/Debian), with
SymPy 1.14.0 and mpmath 1.3.0. The source manifest records the actual PDF-engine
banner. Byte identity additionally depends on matching fonts, TeX packages,
and numerical dependency versions; a matching banner alone does not guarantee
an identical installation. The builder reports a mismatch rather than silently
accepting a different PDF or data set.

No network is required once these dependencies are installed. Install optional
Python dependencies, if needed, in a virtual environment:

    python3 -m pip install -r code/requirements.txt

## Validate an extracted release

Extract the actual supplied ZIP into a fresh directory. It contains one
Report200/ directory. From there:

    python3 build.py --validate-only

This checks the allowlisted files, canonical manifests, byte counts and hashes.
It neither runs the mathematics nor recompiles the PDF. Hashes are integrity
checks against the included records, not signatures from a trusted publisher.

## Complete byte-for-byte reproduction

From a freshly extracted Report200/ directory, choose output paths that do not
already exist and are outside the source package:

    python3 build.py --output ../replay-normal --archive ../Report200-normal.zip

The builder first validates the source package and recorded PDF engine, then:

1. Stages exactly the allowlisted public source files
2. Recomputes all integer/rational data, symbolic checks and diagnostics
3. Runs the malformed-package tests
4. Recompiles the PDF until cross-references and bytes stabilize
5. Regenerates source/package manifests
6. Requires every regenerated public member to match its original bytes
7. Emits the rebuilt package and deterministic ZIP

The ZIP uses sorted paths, stored (uncompressed) members, fixed timestamps,
fixed permissions, and no archive comment. It should match the delivered ZIP
byte for byte with the same toolchain. Compare the archives directly:

    cmp /path/to/Report200.zip ../Report200-normal.zip

Extract the original ZIP again to a second fresh directory for an independent
optimized-Python run:

    python3 -O build.py --output ../replay-optimized --archive ../Report200-optimized.zip
    cmp /path/to/Report200.zip ../Report200-optimized.zip

The optimized build passes -O to both check subprocesses. No correctness check
uses a Python assert statement. All relevant validation remains active.
The builder requires a fresh output directory and archive and will not overwrite
an existing destination, including a dangling destination symlink. It does not
modify the source package.

For maintained source changes, --initialize creates new manifests and a new
release without comparing to the old release. This is intentionally a maintainer
operation, not a way to validate a delivered archive:

    python3 build.py --initialize --output ../new-release --archive ../new-release.zip

## Data-only and independent checks

Use a fresh output directory outside the extracted package, so validation does
not see new undeclared members:

    python3 code/check.py --output-dir ../data-replay
    python3 -O code/check.py --output-dir ../data-optimized
    diff -r data ../data-replay
    diff -r ../data-replay ../data-optimized

The exact core has no third-party Python dependencies:

    python3 -S code/check.py --exact-only --output-dir ../data-exact

Exact-only mode omits symbolic_checks.json and diagnostics.json and records
that omission in summary/manifest output. All exact mathematical
result files are the same as in full mode. Do not run exact-only into a full
mode output directory: it does not remove old optional files.

Package guard tests can be run separately:

    python3 code/test_guards.py
    python3 -O code/test_guards.py

These tests reject malformed JSON, duplicate/extra/missing manifest records,
noncanonical paths, tampered members, undeclared files/directories, symlinks,
special objects, oversized members, invalid output locations, and overwrite
attempts within the documented test cases. Domain-input tests additionally
reject 29 malformed arguments. A separate clean-extraction regression verifies that
the documented direct data-only command leaves its source files untouched,
even when PYTHONDONTWRITEBYTECODE is unset. These are targeted integrity/interface checks,
not a security guarantee. The builder executes the shipped Python and TeX;
inspect untrusted packages before executing them.

## Exact coverage

- U_n for n=0..24, independently from three exact Burnside summations
- All 12 displayed OEIS terms n=0..11 compared exactly
- 7,337 positive-order partition types through n=24
- Four agreeing fixed-count routes: literal pair-orbit walking; fixed-point
  traces with Moebius inversion; grouped cycle-length product; support product
- 1,574 fixed-point-free types and 1,393 zero-fixed-count types in that range
- Orbit-loss bounds and the defect-word counting bound
- All 11 sectors through defect 4, with p_0 through p_5 exactly rational
- Independent rational Laurent expansion and exponential-by-partitions check
- Separate SymPy amplitude, pole/constant, power and inverse cancellations
- 62 exact finite-tail inequalities for 8<=n<=24 and 0<=D<floor(n/4),
  including 28 odd-n cases
- All 739 labeled operations n=0..3, including the empty law; 738 have n>=1
- Direct automorphism and isomorphism-class checks for the exhaustive range
- Separate high-precision sector and inverse diagnostics, explicitly not proofs

For fractional exponents in the tail bound, the code compares the exact
remainder against a rational LOWER bound obtained by flooring the exponents.
Passing this stronger inequality at a test point implies the displayed bound
there. The lower bound is not claimed as a theorem for all n.

## File map

- Report200.tex / Report200.pdf: manuscript and compiled article
- build.py: isolated deterministic compilation, replay and ZIP builder
- code/magma.py: standard-library exact arithmetic and domain checks
- code/check.py: reproduction runner, comparisons and data generation
- code/symbolic.py: independent symbolic cancellations
- code/diagnostics.py: mpmath diagnostics, separate from exact proofs
- code/test_guards.py: malformed-package/integrity test cases
- code/requirements.txt / code/USAGE.txt: dependency pins and detailed code use
- data/counts.json / counts.txt: locally computed U_0 through U_24
- data/fixed_counts.json: all cycle-type counts, pair orbits and fixed counts
- data/sectors.json / sector_coefficients.tsv: exact sector parameters and p_j
- data/finite_tails.json: exact rational tail test records
- data/exhaustive_tables.json: complete small-law statistics and class checks
- data/validation.json: coverage and domain-input tests
- data/symbolic_checks.json: independent CAS verification records
- data/diagnostics.json: numerical diagnostics and stated limitations
- data/summary.txt / manifest.json: data summary and data hashes
- manifests/source_manifest.json: source hashes and toolchain metadata
- manifests/package_manifest.json: hashes of every other public member

The package manifest excludes itself to avoid a circular hash. The whole ZIP
hash is recorded outside the archive in delivery/review receipts. Rebuilding
recreates all public hashes deterministically. Data manifest.json covers the
emitted data files other than itself, independently of the package manifest.

## Sources and priority scope

The official A001425 display was inspected on 4 October 2026:
https://oeis.org/A001425
The comparison seed is only the 12 displayed terms. The official b-file was
not retrieved. All supplied counts are locally computed and are not represented
as official b-file data.

Freese (1990), Turecek (2023) and Burris (2025) were read in full. They provide
classical labeled/unlabeled, unrestricted-rigidity, and exact-enumeration context;
unrestricted operation-space theorems are not automatically applied to
commutative tables. The Harrison (1966) originals and Tamura (1970) chapter
were not obtained in full, so their complete scope is not characterized.
The bibliography contains direct primary-source links and these qualifications.

The fixed-defect hierarchy was not identified in the sources actually read or
in bounded exact-model searches of the available repository and prior-artifact
records. This is not exhaustive overlap clearance, a worldwide priority claim,
or evidence that no earlier proof exists. Finite computation verifies the
stated test cases, while the manuscript supplies the general proofs.
