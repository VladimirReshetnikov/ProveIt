# Late growth of Bessel counting coefficients

This package accompanies the article `bessel_late_growth.pdf` and its editable
LaTeX source `bessel_late_growth.tex`.

The main theorem proves the late-coefficient conjecture for the rational
quotient A395976(j)/A395977(j), associated with the half-power expansion of
A336293. It gives every fixed inverse-factorial correction, both asymptotic
inverse constructions with rounding-aware integer enclosures, and a leading
late-coefficient corollary for each fixed positive integer number of colors.

The theorem proves eventual positivity, not positivity at every index above
five. It does not separate reduced numerator and denominator growth. The
fixed-order estimates and inverse enclosures have unspecified constants and
cutoffs; the numerical results are not interval-certified. No estimate is
claimed uniformly for a growing number of colors.

## Replay the checks

Requirements: Python 3.10 or newer and mpmath 1.3.0. The preparation environment
used Python 3.12.14. No SymPy or external data downloads are required.

```sh
python3 -m pip install -r requirements.txt
bash reproduce.sh
```

This verifies the distributed manifest, regenerates all five result files,
and checks that their hashes match the distributed results. A run took about
seven seconds in the preparation environment. All paths are relative.
The shell wrapper uses python3 by default; set PYTHON to select another
compatible interpreter, for example `PYTHON=/path/to/python3 bash reproduce.sh`.

To rebuild the PDF as well:

```sh
bash reproduce.sh --with-pdf
```

The PDF build requires pdfLaTeX and the standard packages listed in the TeX
preamble (including Latin Modern, AMS math, geometry, booktabs, microtype,
and hyperref). TeX Live 2025 / pdfTeX 1.40.26 was used here. The build uses a
fixed SOURCE_DATE_EPOCH and suppresses volatile PDF metadata. A byte-identical
PDF is checked for this toolchain. Other TeX/font versions may produce a
different PDF despite rendering the same mathematics; in that case use
`bash build_pdf.sh` and inspect the output, separately from the default data
replay. Build logs and intermediate files remain in `.build/`.

## Contents

- `bessel_late_growth.pdf`, `bessel_late_growth.tex`: article and source
- `scripts/exact_algebra.py`: exact finite rational-series arithmetic
- `scripts/replay.py`: independent exact checks and high-precision checks
- `scripts/README.md`: computation details and limits
- `results/exact_coefficients.json`: d0 through d12 and c0 through c8
- `results/high_precision.json`: independent 200/300-digit computations to d100
- `results/original_sequence_and_inverse.json`: original-count and inverse checks
- `results/late_inverse_models.json`: late smooth-model inverse checks
- `results/numerical_tables.tex`: optional generated tables, independent of the article build
- `provenance/SOURCES.md`: source links and bounded retrieval account
- `MANIFEST.sha256`: SHA-256 checksums of the distributed files except itself
- `build_pdf.sh`, `reproduce.sh`: PDF build and one-command replay

Exact arithmetic checks prove the finite identities they test. Agreement at
two numerical precisions is a consistency test, not a rigorous floating-point
error certificate. The asymptotic proofs are in the article.

No third-party full texts, repository snapshots, or private working/review
notes are distributed in this package.
