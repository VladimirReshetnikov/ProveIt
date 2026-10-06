# Reproducibility and verification

## Requirements and dependency boundary

- Python 3.10 or newer, standard library only for every mandatory Python program
- A working `pdflatex`, `pdftex`, and `kpsewhich` installation for PDF creation, with the packages named by the manuscript
- Optional: `g++` with C++17 support for the independent exhaustive audits
- No network or downloaded code is used by the build

The Python subprocesses run with `-I -S -B`, and again with `-O`. Thus the user site, environment import path, and `site` package startup are disabled. All mandatory conditions raise exceptions explicitly; none depend on Python assertions. The original C++ block audit has assertions, so the optional wrapper explicitly passes `-UNDEBUG` and does not use `-DNDEBUG`.

The code was designed as a small, inspectable reference implementation rather than a scalable enumerator for arbitrary k. The finite-kernel enumeration grows quickly; the supplied mandatory computations cover k<=4.

## Mandatory sequence

Run from an unchanged source or an extracted release package:

```sh
python3 -B reproduce.py
```

For each of ordinary and optimized Python, the driver executes:

1. `code/check_fixed_permanent.py`: enumerates finite kernels for k=3,4; verifies their exact rational EGFs; generates exact matrix counts to n=20; exhaustively checks diagonal-one matrices and SCC counts to n=4; checks the embedded available low-column count data to n=6
2. `code/certify_constants.py`: uses exact Fraction interval arithmetic with rigorous derivative-tail bounds to enclose the root and the low-k Laurent coefficients
3. `code/test_certified_guards.py`: checks nine invalid certificate calls and reproduces the valid certificate; the JSON object must match its reference
4. `code/check_effective_error.py`: checks the explicit rational boundary estimates and polynomial envelope inequalities; also checks the error inequality against all supplied exact counts for n=0,...,20 and k=2,3,4
5. `code/decimal_diagnostics.py`: regenerates explicitly non-certified 90-digit-working-precision Decimal diagnostics from 70 Taylor coefficients
6. `code/check_precomputed_audits.py`: validates full and diagonal-one count totals, marked-matching identities, SCC and low-k counts, and the complete multiset-marked SCC transform against the supplied TSVs
7. `code/test_reproduction_guards.py`: rejects altered certificate values, counts, interval shapes, derivative arguments, duplicate or changed TSV rows, and changed/missing frozen-source receipts

The five output JSON files must equal the distributed references byte for byte in each mode. The two modes' additional guard receipts must agree. Outputs are written only into newly created, isolated directories. With no output option, temporary directories are removed on exit. To keep them, pass `--output-dir /absolute/path/to/new-results`, whose parent exists and which is outside the source package. An already existing path is rejected, including a dangling symlink.

The root/certificate and exact scripts are preserved byte for byte. They have their original fixed output filenames. The wrapper therefore runs them in fresh private working directories, never alongside their distributed references. The original certificate guard uses a temporary directory internally and loads its reference from beside its own source. This explains the deliberate location `code/constant_certificate.json`.

## What the arithmetic establishes

The certified routine truncates before degree 45. All finite coefficients, interval endpoints, tail estimates, Horner evaluation, divisions, and Laurent combinations use `fractions.Fraction`. The enclosing interval for a excludes zero. Decimal endpoints are rounded outward to 25 decimal places. The much narrower 40-place rational bracket for rho is hardcoded and checked by rigorous opposite-sign tests, not accepted on numerical faith.

The circle lower bound is eta=119/1000. Exact rational comparisons establish:

    (27/2)/eta^2 + 33 < 1000
    54/eta^2 + 60 < 3900
    864/eta^2 + (27/2)^2/eta^3 + 99 < 170000

The bound `170000*(3/4)^50 < 1/10` and coefficientwise polynomial lower bounds establish the numerical part of positivity and monotonicity of the effective envelopes starting at x=50. The all-n statement additionally uses the manuscript's root isolation, analyticity, and Cauchy argument. The program does not attempt to encode or mechanically verify those analytic theorems.

The Decimal routine replaces a numerical-library diagnostic with an original standard-library implementation. It uses rounded high-precision Newton/Horner evaluation and the explicit low-k Laurent formulas. It computes rho, a, h2/h3/h4, all P1/P2/P3/P4 binomial-basis coefficients, dominant-term ratios at n=5,10,20,30, and permanent-two cycle-size probabilities for sizes 2,...,8. These floating/Decimal calculations provide illustrations and consistency checks only. They are never substituted for rational interval certificates.

## Supplied independent data and optional reruns

The following are unchanged, original authored audit programs and their precomputed results:

- `optional/audit_counts.cpp` and `optional/audit_counts.tsv`
- `optional/audit_blocks.cpp` and `optional/audit_block_counts.tsv`

They were compiled and rerun during preparation of this package, and both output files matched the supplied frozen bytes. By default, the Python pipeline mathematically checks the supplied data, but does not re-enumerate its generating objects. The distinction is recorded in the machine-readable receipt.

```sh
python3 -B reproduce.py --optional-cpp
```

This additionally compiles both programs in private output storage with `g++ -O3 -std=c++17 -UNDEBUG`, executes them, and requires byte-for-byte TSV equality. The command can take substantially longer than ordinary tests on some machines and the count audit needs roughly 128 MiB for its largest integer array. Compiled binaries are never bundled. The C++ files write named TSV files in their current directory; do not run them in the distributed `optional/` directory unless using a disposable copy.

Coverage is exhaustive for all binary and diagonal-one matrices through n=5. The block-signature invariance test checks every marked matching for diagonal-one matrices through n=4 (16,774 comparisons). The stored block distribution is for permanent k<=4 and n<=5. This is finite verification only; it is not a proof of all-n intrinsic block invariance.

## Preserved-source provenance

`data/FROZEN_SOURCE_HASHES.json` records byte lengths and SHA-256 hashes of nine unchanged authored source/reference files from the 2026-10-03T22:10:00Z freeze. `verify_frozen_sources.py` checks exactly that public subset before reproduction. The original full freeze was also checked during package preparation. The public subset receipt does not claim to reproduce unbundled research material.

Hashes detect accidental modification. They do not authenticate a publisher if both the files and their receipt are maliciously replaced. The final ZIP's `SHA256SUMS.json` covers all included files except itself; the external `ARTIFACTS.json` covers the released PDF, TeX, and ZIP, except itself.

## PDF and release build

```sh
python3 -B build.py --output /absolute/path/to/new-release
```

The builder accepts exactly the explicit `SOURCES` inventory in `build.py`, or that inventory plus the exact generated release files and an intact manifest. It rejects symlinks in source paths and directory ancestors, special files, traversal paths, caches, missing files, extra files, and empty unexpected directories. Keep any editor backup or test output outside the package.

The build copies allowlisted sources into a fresh private package directory, runs the build/manifest test suite under ordinary and optimized Python, runs all mandatory mathematical reproduction, and compiles only the standalone TeX file in separate private storage. It does not process a submitted Makefile or invoke arbitrary commands through a shell.

pdfLaTeX runs with `-no-shell-escape`, halt-on-error, and up to six passes until the auxiliary files stabilize. The final log is rejected for unresolved or duplicate labels/citations, compiler/package/class/font warnings, missing characters, or overfull/underfull boxes. A normal first-pass rerun warning is permitted only if absent after stabilization. Private TeX caches and home directories are used. If the installed tree has no usable format, a private format is generated using the installed `pdftex` and map files.

The environment fixes:

- `SOURCE_DATE_EPOCH=1790985600` (2026-10-03 00:00:00 UTC)
- `FORCE_SOURCE_DATE=1`, UTC, and `C.UTF-8`
- Python hash seed 0 and disabled bytecode writes
- private HOME, TMPDIR, TeX cache/config/font directories
- restricted TeX input/output paths and disabled shell escape

The ZIP uses lexicographically sorted entries, fixed timestamps, regular-file mode 0644, and uncompressed storage to avoid compressor-version variation. With the same source and installed Python/TeX stack, repeated clean builds are intended to produce byte-identical PDF, TeX, and ZIP files. Different TeX distributions, package versions, font sets, and engines may change PDF bytes. No cross-version PDF identity is promised.

Publication uses an exclusive `mkdir` only after checks, compilation, manifest verification, and archive creation succeed. Every artifact write is exclusive. Existing output paths, including dangling links or concurrently created directories, are never replaced. A failure while writing to the newly claimed directory can leave a partial new directory; inspect it and choose a fresh output path rather than rerunning against it. Failed checks before publication leave no output directory.

## Build guards

Run the build guard suite independently:

```sh
python3 -B test_build.py
python3 -O -B test_build.py
```

It currently covers 176 acceptance/rejection cases, including path traversal, links, FIFOs, malformed/duplicate-key/nonfinite JSON, bad manifests, changed and extra content, archive order and metadata, exclusive writes, polluted environments, unsafe output paths, normal/optimized disagreement, simulated warnings, unstable auxiliary files, failed compilation, and a racing output-directory creator. Its compiler is simulated; the actual release build invokes the real TeX engine separately. No removable Python assertions occur in mandatory sources.

## Complete archive inventory

Source files:

- `Report184.tex`, `README.md`, `README_REPRODUCIBILITY.md`
- `build.py`, `test_build.py`, `reproduce.py`, `verify_manifest.py`, `verify_frozen_sources.py`
- `code/check_fixed_permanent.py`, `code/certify_constants.py`, `code/test_certified_guards.py`, `code/constant_certificate.json`
- `code/check_effective_error.py`, `code/decimal_diagnostics.py`, `code/check_precomputed_audits.py`, `code/test_reproduction_guards.py`
- `data/FROZEN_SOURCE_HASHES.json`
- `certificates/exact_checks.json`, `certificates/effective_error_checks.json`, `certificates/decimal_diagnostics.json`, `certificates/precomputed_audit_checks.json`
- `optional/audit_counts.cpp`, `optional/audit_counts.tsv`, `optional/audit_blocks.cpp`, `optional/audit_block_counts.tsv`

Generated files inside the release ZIP:

- `Report184.pdf`
- `generated/verification.json`
- `generated/build_guards.json`
- `generated/BUILD_INFO.json`
- `SHA256SUMS.json`

The ZIP deliberately excludes compiled audit binaries, runtime logs, TeX intermediates, caches, third-party papers, private reviews, and unrelated source material.
