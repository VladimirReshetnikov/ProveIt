# Reproduction and packaging

## Scope and requirements

The mandatory mathematical computation uses Python integers and
`fractions.Fraction` only. Python 3.10 or later is required. Neither third-party
Python packages, TeX, nor network access is needed to run the exact checker.
The optional mpmath script is separate and is never executed by
the checker, replay command, test suite, or release builder.

The exact checks establish the reported finite geometry, integer recurrences,
independent rational inverse-germ identities, input guards, and agreement with
all 64 bounded attributed OEIS terms. Full geometry covers indices 0..250000;
all-earlier-point brute force covers 2..4096. Both independent coefficient
methods check degree 12 and each lower truncation, including the six displayed
nonconstant coefficients. No amplitude interval or numerical amplitude digits
are certified. The all-index and asymptotic conclusions are proved in
`Report191.tex`; a finite computation is not substituted for those proofs.
See `code/README.md`, `data/README.md`, and `DATA_SOURCES.md` for domains and
provenance.

A complete PDF build additionally needs an installed pdfLaTeX distribution,
`kpsewhich`, the packages used by the manuscript, and their fonts. The builder
can initialize a missing local pdfLaTeX format with the installed `pdftex` and
format sources. It does not download or install any dependencies.

## 1. Exact checks

From the source or extracted release directory:

    python3 -I -S -B code/check_exact.py
    python3 -I -S -B -O code/check_exact.py

To write a durable result, supply a new file outside the package:

    python3 -I -S -B code/check_exact.py --output "$(dirname "$PWD")/report191-exact.json"

The canonical JSON is also printed to standard output. The output path must
be fresh; existing data is not silently replaced. `-I` ignores user Python
startup/import settings, and `-B` prevents bytecode cache creation. The `-S` flag excludes installed
site packages as well; the release builder uses these same flags.

For a single command that runs both isolated modes and compares their output
byte for byte:

    python3 -I -S -B reproduce.py --output-dir "$(dirname "$PWD")/report191-replay"

The examples use an absolute sibling path because the package replay and
builder deliberately reject literal `..` path components. The output parent
must already exist. This produces:

- `normal/exact_checks.json`
- `optimized/exact_checks.json`
- `RESULT.json`, which records byte identity, SHA-256, byte count, and scope

Without `--output-dir`, the same checks run in automatically removed temporary
storage and the summary is printed. A replay verifies the complete source
inventory first. For an extracted release it also checks the release manifest.
No reference certificate is silently regenerated: both modes independently
compute their finite checks, validate the fixed attributed fixture, and must
agree. The result is not compared with a mutable stored floating estimate.

The package file set and contents are recorded before replay and checked
again before publication. A changed source causes failure. Existing output
files/directories, symlinks, symlinked parents, missing parents, traversal
components, and output inside the package are rejected.

## 2. Adversarial package checks

    python3 -I -S -B test_build.py
    python3 -I -S -B -O test_build.py

Both commands must print identical successful summaries. These tests use
synthetic files and a simulated compiler; they never invoke TeX, run optional
numerical diagnostics, modify the source, or contact the network. They cover:

- Regular and nested sources; missing, unexpected, and wrong-type entries
- Symlinked files, directories, roots, dangling links, and special files
- Path traversal, absolute/drive paths, control characters, and Python caches
- Exact manifest schemas, duplicate JSON keys, nonfinite values, digest syntax,
  byte-count types, wrong hashes, wrong sizes, and per-file/aggregate size caps
- Complete allowlisted inventory, even when an added file is rehashed
- Refusal to replace files, directories, archives, or racing output writers
- Output/source overlap, including alternate leading-slash path aliases
- Isolated environments, subprocess failures, malformed result objects,
  normal/optimized disagreement, and source changes during a build
- Three compiler passes, stabilization, unresolved or duplicate references,
  every final-log warning, overfull/underfull boxes, missing glyphs, and invalid
  PDF signatures
- Deterministic archive order, timestamp, permissions, and stored compression
- Exact external receipt inventory, byte counts, and hashes
- Exact-checker subprocess isolation and agreement between stdout and file
- All supplied Python source free of removable `assert` statements

The independent mathematical identity and input-domain checks are executed by
`code/check_exact.py`; their counts and tested scope appear in its result.
A test-suite PASS is not a claim that a real compiler ran. The release builder
performs the actual compilation after the synthetic guard suite succeeds.

## 3. Complete offline release

    python3 -I -S -B build.py --output "$(dirname "$PWD")/report191-release"

The output parent must exist and the output directory must not exist.
The builder reads the source, makes an isolated temporary copy, runs the guard
suite normally and with `-O`, and requires identical summaries. It then runs
the exact replay in both modes and requires identical exact JSON bytes.
Only after those checks does it compile the PDF.

TeX runs exactly three passes with shell escape disabled. Auxiliary state from
passes two and three must agree. The final settled log must contain no warning,
undefined/multiply-defined reference, missing character, overfull box, or
underfull box. The metadata line identifying the `infwarerr` support package
is not itself a warning. Initial-pass cross-reference rerun messages are
allowed to settle; a final-pass rerun message fails the build.

The environment uses `SOURCE_DATE_EPOCH=1791072000` (2026-10-04 00:00:00 UTC),
UTC, fixed locale, and private home, temporary, TeX configuration, format,
font, and cache locations. Inherited TeX/Python overrides are removed. The
manuscript suppresses path-dependent PDF trailer information. Temporary TeX
files, auxiliary files, compiler logs, and format caches are not distributed.

The fresh output directory contains exactly:

- `Report191.pdf`
- `Report191.tex`
- `Report191_code.zip`
- `ARTIFACTS.json`

The external receipt has the exact fields `schema`, `report`, `algorithm`,
and `files`. Its `files` map records the byte count and SHA-256 of the three
deliverables. It does not hash itself and is not added to the source archive.
The independently shipped TeX/PDF are byte-identical to their archive entries.

Every archive entry is sorted by path, uses timestamp 2026-10-04 00:00:00,
Unix regular-file mode 0644, and uncompressed ZIP storage. This avoids
compressor-version variation. With identical source and installed Python/TeX
stack, fresh builds produce identical PDF, TeX, ZIP, and receipt bytes.
Different Python/TeX releases, packages, or fonts may change PDF bytes;
cross-version byte identity is not promised.

## 4. Closed source inventory and release manifest

`SOURCES` in `verify_manifest.py` is the sole public source allowlist, imported
by the builder. It lists exactly seventeen authored/fixture files:

- `Report191.tex`, `README.md`, `README_REPRODUCIBILITY.md`, `DATA_SOURCES.md`
- `build.py`, `test_build.py`, `verify_manifest.py`, `reproduce.py`
- `code/spiral.py`, `code/inverse_series.py`, `code/check_exact.py`,
  `code/independent_series.py`, `code/check_geometry.py`,
  `code/diagnose_mpmath.py`, `code/README.md`
- `data/oeis_fixtures.json`, `data/README.md`

An authored tree must contain exactly those files and their necessary parent
directories. An extracted release adds exactly:

- `Report191.pdf`
- `generated/exact_checks.json`
- `generated/verification.json`
- `generated/build_guards.json`
- `generated/BUILD_INFO.json`
- `SHA256SUMS.json`

The manifest uses schema `report191-manifest-v1`, report number 191, algorithm
`sha256`, and a `files` object mapping all twenty-two non-manifest files to
exactly `bytes` and `sha256`. Boolean, negative, noninteger, or oversized byte
counts are rejected. Digests must be 64 lowercase hexadecimal characters.
No entry for the manifest itself is allowed.

Verification requires all of the schema, allowlisted inventory, directory
inventory, sizes, and hashes to agree. The per-file limit is 8 MiB, total
non-manifest payload limit 32 MiB, and manifest limit 64 KiB. Duplicate JSON
keys and NaN/Infinity are rejected. Extra files or empty directories fail even
if the manifest was recomputed to include them. Hashes detect modification,
not an adversary replacing both the code and its manifest; this is not a
cryptographic publisher signature.

The archive contains authored public manuscript/code, bounded attributed
integer fixtures, and the generated release products listed above. Full OEIS
exports, downloaded pages or papers, research/audit notes, transient logs,
private working material, caches, and unrelated files are excluded.

## 5. Verify and rebuild an extracted release

Extract the trusted release ZIP into a new directory, then from that directory:

    python3 -I -S -B verify_manifest.py
    python3 -I -S -B -O verify_manifest.py
    python3 -I -S -B reproduce.py --output-dir "$(dirname "$PWD")/replay-from-extraction"
    python3 -I -S -B build.py --output "$(dirname "$PWD")/rebuilt-release"

Use fresh names for every output. The extracted release is checked intact;
only the seventeen authored/fixture sources enter the new build, and generated files
are computed again. The package is never overwritten or cleaned in place.
Two clean extracted copies can be rebuilt to distinct new sibling output
directories and compared with `cmp` or `sha256sum` for all four output files.

The builder is an offline reproducibility tool for this authored package,
not a security sandbox for arbitrary hostile Python or TeX. Its explicit
paths, isolation settings, bounded inventory, and no-overwrite policy protect
against the tested input/path mistakes; they do not promise immunity to an
actively hostile process changing filesystem components concurrently.
