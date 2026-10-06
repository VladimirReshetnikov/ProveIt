# Report171 reproducible companion

This archive accompanies **Report171**, on fixed-order logarithmic and exact-Lambert-sector asymptotics for planar Eulerian orientations. Read `Report171.pdf` for the mathematical statements, proofs, references, and limitations. The programs do not independently prove the published global continuation theorem or turn asymptotic big-O constants into finite-index bounds.

## Contents and conventions

- `Report171.tex`, `Report171.pdf`: report source and compiled report
- `code/companion.py`: bounded exact computations and optional numerical diagnostics
- `code/test_companion.py`, `code/test_build.py`: positive and deliberate-failure tests
- `fixtures/`: frozen OEIS prefixes, symbolic formulas, provenance, and fixture hashes
- `outputs/exact.json`: 1000 exact positive-index terms for each family, inverse coefficients through `r_1002`, Lagrange checks through `r_81`, and full ODE residual checks through `t^1001`
- `outputs/symbolic.json`: exact Q0–Q5, reciprocal-Gamma coefficients, U0–U3 substitution checks, and inverse-log E1/E2
- `outputs/diagnostics_110d.json`: non-certified 110-digit Lambert/leading/logarithmic comparison diagnostics
- `outputs/inverse_*_logy1000.json`: non-certified inverse charts at log(y)=1000 for each normalization
- `outputs/tests*.json`, `outputs/build_tests*.json`: normal and optimized-Python test receipts
- `BUILD-INFO.json`: fixed epoch and build tool versions
- `SHA256SUMS.json`: SHA-256 for every archive member except the manifest itself

All integer sequences are represented as decimal strings in JSON. A324312 and A324314 start at index 1. A277493 starts at index 0 with 1 and is twice A324312 at positive indices. General orientations are counted by edges, quartic orientations by vertices. The published paper fixes the Eulerian root-edge direction to agree with the rooting direction; A277493 has the other root-orientation normalization. Every refined formula uses `m=n+2`.

The OEIS fixture is a dated transcription of the retrieved pages, not a live query or a guarantee about the latest uncached revision. It contains 22 A324312 terms, 20 A324314 terms, and the five A277493 terms explicitly transcribed in the reviewed source. See `fixtures/provenance.json` for primary-source URLs and computational provenance. No original source PDFs or internal working notes are redistributed.

## Requirements

Tested with Python 3.12.14, SymPy 1.14.0, mpmath 1.3.0, and pdfTeX from TeX Live. The exact integer engine uses only the Python standard library. Symbolic commands require SymPy; numerical commands require mpmath. `requirements.txt` pins the tested Python packages. Use already installed packages when available; no command performs downloads or network access.

Building the PDF requires `pdflatex` and the packages named in `Report171.tex`. The build does not install TeX or fetch missing packages. The source is expected to be self-contained; no external bibliography processor is invoked.

If the installed TeX files exist but their generated lookup database or format is missing, the builder enables recursive lookup of the installed distribution, runs `pdftex -ini` to create a temporary format, and assembles the report's installed Computer Modern/AMS/Latin Modern font maps locally. This fallback needs `pdftex` and `kpsewhich`; it does not modify the system installation. Both commands are normally part of TeX Live. A genuinely missing package remains an explicit build failure.

## Reproduce the report archive

From the extracted archive directory:

```sh
python build.py --output /path/to/new/Report171-rebuilt.zip
```

To also retain the compiled PDF outside the ZIP:

```sh
python build.py --output /path/to/new/Report171-rebuilt.zip --pdf-output /path/to/new/Report171-rebuilt.pdf
```

Both parent directories must already exist. Every destination must be new: the build refuses to overwrite a regular file, directory, or symlink. If both destinations are requested, the PDF is created first; an intervening ZIP-write failure can leave the completed PDF in place. Choose new paths when retrying.

The build copies a fixed source whitelist into a fresh temporary directory, runs all tests under normal Python and `python -O`, regenerates the exact, symbolic, numerical diagnostic and inverse-example outputs, and runs `pdflatex` with shell escape disabled. Compilation takes at least two passes and continues until `.aux`, `.toc`, and `.out` are byte-stable, with a strict six-pass limit. Unresolved-reference, missing-glyph and overfull-box defects in the final log stop the build. TeX's writable format/font cache locations are also redirected into this temporary tree, so a writable home directory is unnecessary. Temporary files are removed on success and failure. It never reuses local `.aux`, `.log`, `.pdf`, or `outputs/` files.

`SOURCE_DATE_EPOCH` is fixed at 1790985600 (2026-10-03 00:00:00 UTC); the invoking environment cannot change it. PDF date/trailer metadata are suppressed. Archive entries are sorted and have fixed timestamp, Unix regular-file permissions 0644, and uncompressed `ZIP_STORED` data, avoiding compressor-version variation. The archive hash is printed at completion. Byte-identical rebuilding is claimed for identical source files and toolchain, not across different Python/SymPy/TeX installations. TeX package and font versions can alter PDF bytes. `BUILD-INFO.json` records core versions; it is not a complete TeX dependency lockfile.

To verify a received package after extraction:

```sh
python - <<'PY'
from pathlib import Path
import hashlib, json
manifest = json.loads(Path('SHA256SUMS.json').read_text())
for name, expected in manifest.items():
    actual = hashlib.sha256(Path(name).read_bytes()).hexdigest()
    if actual != expected:
        raise SystemExit('SHA-256 mismatch: ' + name)
print('All listed hashes match')
PY
```

The manifest checks integrity, not an authenticated signature or independent mathematical validity.

## Individual commands

All commands default to JSON on stdout. Add `--output NEW.json` for exclusive file creation; existing output is refused before expensive work and again at creation. Run from any working directory; fixture paths are anchored to the script location.

```sh
python code/companion.py exact --n 1000 --lagrange-m 81
python code/companion.py symbolic
python code/companion.py verify --n 1000 --lagrange-m 81
python code/test_companion.py
python -O code/test_companion.py
python code/test_build.py
python -O code/test_build.py
```

`exact` generates the inverse using the integer ODE `R(cR-1)R''=d*t*(R')^3`, with `(c,d)=(16,4)` or `(27,6)`. Every division is checked for zero remainder. It separately constructs the full polynomial ODE residual, compares the requested independent Lagrange prefix, checks positivity and OEIS fixtures, and applies the exact normalization factors. The Lagrange implementation uses generalized-binomial powers of `Omega(r)/r-1`; it does not reuse the ODE recurrence. `--n` is 1–1000; `--lagrange-m` is 1–81 and is capped to the generated inverse prefix. Smaller runs honestly report reduced fixture and prefix coverage. The 1000-term default is a bounded check, not a claim that the ODE engine is validated for arbitrary resource sizes.

`symbolic` independently solves `1/F + x*log(F) = 1+x*t`, with `f=x*F`, constructs reciprocal-Gamma coefficients, and applies the transfer derivative operator. It compares all Q0–Q5 with the frozen formulas. U0–U3 are checked by direct substitution into the integrated hypergeometric equation through degree four in `xi`; their possible finite poles and local constants are checked too. Exact symbolic checking does not certify the analytic remainders: those arguments belong to the report.

`verify` runs both the exact and symbolic checks and emits a compact summary. Tests intentionally corrupt inverse/fixture data, violate argument bounds and integer divisibility, and attempt to clobber existing files and symlinks. Checks use explicit exceptions throughout; optimization cannot remove them.

### Optional floating-point diagnostics

```sh
python code/companion.py diagnostics --n 1000 --digits 110 --prefix 60 --output NEW-diagnostics.json
python code/companion.py inverse --sequence A324312 --log-y 1000 --digits 110
python code/companion.py inverse --sequence A277493 --log-y 1000 --digits 110
```

The first command computes Taylor coefficients of the exact analytic Lambert models by `h*h''=-(h')^3` and `F1=h^2-(delta+1)*h^2*h'`. The real initial germ is selected by `v0-log(v0)=C`, `v0>1`. An independent generalized-binomial Lagrange expansion about zero checks a small prefix. It reports relative errors against exact counts at selected indices, including the requested last index. `--digits` is 50–200 and `--prefix` is 1–60; `--n` remains 1–1000. The prefix acceptance threshold is a declared floating-point tolerance, not an interval certificate.

`inverse` accepts the **natural logarithm** of a target y, avoiding huge input numbers, and prints x0, x1, x2 smooth asymptotic charts. The argument must be a finite decimal string at most 100 characters long with `10 <= log(y) <= 10^9`. The lower bound is a numerical domain safeguard, not a certified asymptotic-validity threshold. No integer ceiling is returned. The theorem's constants and starting indices are not explicitly evaluated or certified here. Together with the possible adjacent-integer ambiguity, this prevents reading a chart as a certified exact threshold.

Neither numerical command uses interval arithmetic. High precision and independent-prefix agreement are diagnostics only. Low-order logarithmic corrections need not improve monotonically at available indices. Retaining the exact Lambert model is essential for resolving the next algebraic sector; a finite inverse-log truncation does not do so.

## Failure behavior

Invalid bounds, nonintegral divisions, altered fixture hashes, disagreement with exact checks, wrong Lambert branch, and existing destinations produce nonzero exit status. CLI validation uses exceptions rather than Python `assert`; tests run in both optimization modes. An interrupted write can leave a partial new file, which is intentionally never overwritten on retry. Select another output path or inspect/remove the partial file yourself. No output contains elapsed time or machine-specific absolute source paths.
