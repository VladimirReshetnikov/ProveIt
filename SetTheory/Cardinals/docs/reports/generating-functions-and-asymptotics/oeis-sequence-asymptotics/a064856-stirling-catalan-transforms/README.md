# Report205: Catalan-weighted Stirling transforms

## Corrected revision 2, 4 October 2026

The historical discussion now attributes the spectral-moment inequality to Bauer and Golinelli (2001), whose coefficientwise theorem already implies Spiridonov’s Conjecture 3.3. A normalization corollary and root-scale consequences have been added. The Stirling–Catalan asymptotic and inverse results, coefficient data, and numerical tables are unchanged. This revision does not claim a new proof of the prior inequality or a relative asymptotic formula for the spectral moments.

This package contains the manuscript, its reproducibility source, generated exact and numerical data, and the PDF. It does not contain third-party papers or private research material.

## Complete build

Requirements: Python 3.12, SymPy 1.14.0, mpmath 1.3.0, and `pdflatex` with standard LaTeX packages used by `Report205.tex`. The reference build uses pdfTeX from TeX Live 2025. No network access is needed after dependencies are installed.

From this directory:

```sh
python build.py
python -O build.py
```

Each command performs the same complete build:

1. Derive the endpoint coefficients, saddle corrections and rational functions Q0–Q3 with exact SymPy arithmetic.
2. Compare them with independent integer coefficient literals. Run `verify_exact.py`, which uses only the standard library and an independent sparse-polynomial implementation to verify 28 rational evaluation points certifying the four identities Q0–Q3. The documented numerator degree bound makes these evaluations exact polynomial identity checks, not numerical evidence.
3. Compare exact Stirling–Catalan enumeration with the independently derived differential-equation recurrence through n=200, and compare the first 23 terms with the cited OEIS prefix.
4. Compute exact Stirling rows and Catalan numbers through n=2000, retaining eight checkpoint values. At these checkpoints, evaluate asymptotic and inverse diagnostics independently at 80 and 110 decimal digits and require relative agreement to 62 digits. The public JSON keeps 72 significant digits from the higher-precision run.
5. Regenerate all TeX constants and the two manuscript tables from the checked values. Check the committed manuscript's complete SHA-256 and its reviewed literal blocks; a manuscript edit requires an explicit review and update of `manuscript_guards.json`.
6. Run `pdflatex` at least twice, continuing until references and contents stabilize (at most six passes), with shell escape disabled and reproducible metadata settings. Reject unresolved references and overfull boxes.
7. Write the manifests and a deterministic `Report205.zip`, then read back and verify every archive member.

All tests use explicit exceptions. Python optimization cannot remove them. The independent checker can also be run by itself after a build:

```sh
python verify_exact.py
python -O verify_exact.py
```

For data development only, `python build.py --data-only` stops before manuscript checks, typesetting, and packaging. It is not a complete reproducibility build.

## Byte-for-byte extracted rebuild test

```sh
python build.py --verify-replay
```

This first makes a complete reference build. It extracts the resulting archive into two separate fresh temporary directories, runs a complete normal build in one and a complete `python -O` build in the other, and compares every public source/data/PDF/manifest member, both external archive identity manifests, and the complete ZIP bytes. It fails at the first mismatch. Its success is printed to stdout; no variable run-time or filesystem path is added to the package.

Byte identity is promised for replay in the same dependency and TeX/font environment. Different software releases can change symbolic formatting, floating last digits, PDF fonts, or compression. The generated `data/validation.json` records the relevant versions.

## Data and manuscript interface

- `data/coefficients.json`: exact endpoint beta and c coefficients, Touchard-derived P polynomials, saddle corrections A, Q0–Q3, logarithmic corrections R1–R3, the Bell correction, and the first two inverse shifts
- `data/polynomial_coefficients.json`: ascending integer numerators of Qj and denominator constants for (1+r)^(3j)
- `data/exact_values.json`: exact a_n and ordinary Bell numbers at n=10,20,50,100,200,500,1000,2000
- `data/exact_checks.json`: independent exact-check result
- `data/numerical_checks.json`: r=W(n/4), a_n/L_n, scaled remainders, relative residuals, and the nth-root Bell ratio
- `data/inverse_checks.json`: rho, n0, d0, d1, the first two inverse errors, and a scaled inverse error
- `data/validation.json`: reproducible validation summary and dependency versions
- `tex/constants.tex`: generated exact coefficient macros
- `tex/asymptotic_table.tex`: tabular data for E_j=(a_n/L_n−sum_{k=0}^j Q_k(r)/n^k)(n/r)^(j+1)
- `tex/inverse_table.tex`: tabular d0,d1,I0(a_n)−n,I1(a_n)−n values
- `tex/pdf_settings.tex`: deterministic pdfTeX metadata controls

The numerical tests concern the finite checkpoint grid only. They are floating-point diagnostics, not interval-certified error bounds. They neither certify a global remainder constant or onset nor turn a two-ceiling inverse envelope into a guaranteed single-ceiling rule.

## Manifest design and deterministic settings

`MANIFEST.json` hashes all distributable sources, generated data, TeX inputs, and the PDF. It excludes itself to avoid a self-hash cycle. The external `archive_manifest.json` hashes the ZIP and **every** member in it, including `MANIFEST.json`. This external manifest is reproducible but is not itself inside the ZIP, which would create a self-reference. The ZIP excludes itself, the external manifest, logs, TeX intermediates, caches and temporary files.

ZIP paths are sorted; timestamps are fixed to 2026-10-04 00:00:00 UTC; permissions are fixed to ordinary read/write owner and read-only others. `SOURCE_DATE_EPOCH=1791072000`, `FORCE_SOURCE_DATE=1`, UTC, PDF date suppression, suppressed pdfTeX path/version metadata and an empty PDF trailer identifier remove variable metadata. No absolute local path, current clock time, or optimization flag is recorded in a distributable output.

The TeX inputs and numerical tables are generated, not copied from the manuscript. The exact checker contains its own coefficient literals, and the whole-source guard plus reviewed literal blocks detects unreviewed transcription changes elsewhere in the manuscript. The analytic asymptotic proof is a mathematical argument, not replaced by the finite tests.
