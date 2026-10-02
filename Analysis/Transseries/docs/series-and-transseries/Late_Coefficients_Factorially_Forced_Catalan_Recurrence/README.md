# Late coefficients of the factorially forced Catalan recurrence

This package accompanies the article proving the leading formula conjectured in OEIS A260879 and giving every fixed algebraic correction, an exact Stirling transform, selected smooth inverses, and discrete threshold enclosures for both the late coefficients and the original recurrence. A separate chapter proves the exact positive remainder after factorial-basis half truncation, its parity-dependent exponential scale, all fixed scalar corrections, and explicit lower bounds.

## Main files

- `late_factorial_coefficients.pdf`: the complete article
- `late_factorial_coefficients.tex`: editable source
- `results/numerical_tables.tex`: generated numerical tables used by the article
- `scripts/verify.py`: exact integer and rational-polynomial checks using Python's standard library
- `scripts/inverse_checks.py`: optional high-precision Gamma/Lambert inverse checks
- `scripts/render_tables.py`: deterministic table generation
- `scripts/remainder_coefficients.py`: nine exact even/odd scalar corrections
- `scripts/remainder_checks.py`: exact half-truncation complement/shape checks and high-index remainder illustrations
- `results/`: recorded calculation outputs, including exact coefficients through index 500
- `provenance/SOURCES.md`: literature links, version details, and scope of the prior-work comparison
- `VALIDATION.md`: review and reproducibility status
- `SHA256SUMS`: integrity manifest for package files, excluding itself

## Requirements

- Python 3.11 or newer
- For numerical inverse checks, mpmath 1.3.0 (`python3 -m pip install -r requirements.txt`)
- For rebuilding the PDF, pdfLaTeX/TeX Live with the standard article class and fontenc, lmodern, geometry, amsmath, amssymb, amsthm, mathtools, booktabs, array, microtype, hyperref, and enumitem packages
- Bash for the replay and build wrappers

No network is used by the scripts or replay. Dependency installation, if needed, is a separate optional step. The package does not install software automatically.

## Replay after ordinary Python ZIP extraction

From the directory containing the ZIP:

```sh
python3 -m zipfile -e late-factorial-coefficients-reproducibility.zip extracted
cd extracted/late-factorial-coefficients
bash replay.sh
```

Calling the script with `bash` is intentional: ZIP extraction with Python need not preserve executable permission bits. The full replay verifies the manifest, recomputes all recorded data in a fresh local folder, compares the data byte-for-byte, regenerates tables, and rebuilds the PDF. It reports whether the regenerated PDF is byte-identical to the supplied PDF in the active TeX environment. PDF binary identity across different TeX distributions is not promised.

To perform only the standard-library exact and Decimal checks:

```sh
bash replay.sh --core-only
```

That mode does not require mpmath or TeX. It compares all core outputs but omits the combined table file, because the archived table also contains optional inverse data.

For custom ranges, see `scripts/README.md`. To rebuild only the article:

```sh
bash build_pdf.sh
```

## Mathematical scope

Every asymptotic error is for a fixed finite order. The manuscript proves the conjectured leading late-coefficient law and its explicit correction expansion. The Gamma models are deliberately selected smooth carriers; no canonical continuous interpolation of the integer sequences is asserted. Ceiling enclosures have existential constants and are not numerical interval certificates.

The factorial-basis cutoff j<n/2 has a proved positive remainder of order n! n^(-1/2)2^(-n), with parity-dependent constants and all fixed algebraic corrections. This is a different truncation rule from the inverse-power series.

The least inverse-power term near k=(log 2)n and the scale n^(-1/2)2^(-n) motivate a research question; an optimal inverse-power truncation remainder is not proved here. The report does not assume Borel continuation or identify a Stokes constant.

The exact recurrence, factorial-series composition framework, and Fubini pole mechanism are prior work and are credited. The bounded source comparison is not a claim of universal priority. No third-party full texts or private working notes are included.
