# Report185: Decorated logarithmic eta products

This package accompanies the self-contained mathematical report on OEIS
A330499 and analytic, nonnegative, positive-variance, span-one decorations.
The PDF gives the theorem, proof, exact model, first three oscillatory terms,
and smooth inverse charts with pointwise integer envelopes.

## Run the exact checks

Python 3.10 or newer is recommended. No third-party Python package is needed:

```sh
python -I -S -B reproduce.py
python -I -S -B -O reproduce.py
```

The reproducer itself runs the mandatory tests in both normal and optimized
Python, compares their structured results and the exact receipt, and rejects
corrupted fixtures. The `-S` flag deliberately excludes third-party packages.
Every consequential check uses an explicit exception, not a removable assert.

The exact kernel independently checks:

- all 21 listed sequence values, beginning with a(0)=0
- the alternating logarithm/divisor identity through degree 100
- unsigned-Stirling integer values, row sums, and strict monotonicity through 600
- direct rational polynomial composition for the logarithmic decoration through 60
- polynomial composition against the finite binomial coefficient formula for
  B(z)=(z+z^2)/2 through 60
- rational arithmetic supporting the first-harmonic tail bound, with Archimedes'
  classical pi bound explicitly identified as a mathematical input

## Build the report

A TeX installation with pdfLaTeX and the report's standard packages is required:

```sh
python -I -S -B build.py --output /tmp/fresh-report185-build
```

The output directory must not exist and must be outside the source package.
The builder creates `Report185.pdf`, `Report185.tex`, `Report185_code.zip`, and
`ARTIFACTS.json`. It verifies the exact kernel, tests the build guards in normal
and optimized Python, compiles without shell escape, rejects unresolved
references and layout warnings, and produces a deterministic, explicitly
allowlisted ZIP with checksums. No network access is used.

## Optional floating-point diagnostics

```sh
python -B reproduce.py --optional-numerics --output-dir /tmp/fresh-report185-numerics
```

Install the optional dependencies separately if desired: mpmath, NumPy, and
SciPy. The package does not install anything. Optional programs cover 50/80-digit
precision replication, the independent Laguerre recurrence, a two-point
polynomial decoration, modular-identity FFT coefficient extraction, and smooth
inverse roots. See `optional/README.md` for the independent commands and exact
sample/precision limits. Saved receipts and byte-preserved numerical files in `optional/historical/`
are finite diagnostics.

## What the computation establishes

Integer and Fraction checks are exact within their stated finite ranges.
Floating-point tolerances are finite regression checks, not interval certificates,
proofs of a uniform remainder, effective starting indices, or guarantees at
uncomputed n. The all-fixed-orders analytic theorem is proved in the manuscript;
its existence constants and eventual thresholds are not computed by this code.
A chosen smooth inverse is not a canonical interpolation of an integer staircase.

`data/provenance.json` identifies the finite fixture and public mathematical
sources. It does not assert an exhaustive novelty search or priority.
Third-party papers, complete source records, and research notes are not bundled.
See `README_REPRODUCIBILITY.md` for integrity and reproducibility limits.
