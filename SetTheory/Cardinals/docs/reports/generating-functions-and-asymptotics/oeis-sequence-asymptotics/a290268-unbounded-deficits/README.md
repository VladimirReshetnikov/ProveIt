# An explicit finite-ratio region for A290268

`article.pdf` is the ten-page standalone report. Its complete proof source is `article.tex` plus `spectral_sections.tex`.

The report proves a uniform finite-ratio phase law on an explicitly parametrized regular saddle branch. The endpoint is defined exactly, with the decimal 0.0281461097171 supplied only for orientation. Consequences include:

- Eventual noncancellation whenever k/d tends to an algebraic number in the regular branch, for each fixed central offset b=q−2d, apart from the proved reflection holes
- Eventual noncancellation uniformly for all |b|<=8 and 0<=k<=d/36, again apart from reflection holes
- An explicit finite set of possible leading-phase zeros for each larger fixed offset; these limiting ratios are transcendental and are not asserted to be zeros of integer coefficients

The full A290268 support conjecture remains open. The curvature-zero endpoint and growing offsets are outside the theorem, and no numerical depth threshold is claimed.

## Exact rational certificate

Run with Python 3:

```sh
python3 verify_rational_band.py
```

This uses only the standard library and exact fractions. It verifies the Taylor inequalities proving that the regular branch extends beyond 1/36. The certificate is recorded in `rational_band_certificate.json`. No floating-point calculation is used for this assertion.

## Optional numerical orientation

With NumPy and SciPy installed, run:

```sh
python3 check_spectral_limits.py
```

This compares finite Jacobi spectra, means, curvature, resolvents, and complex shift factors with the proved limiting formulas. `spectral_numeric.json` records the sample values. This numerical calculation does not prove any asymptotic theorem or any finite-depth noncancellation claim. The analytic proof is complete without it.

## Typesetting and review

Compile `article.tex` twice with pdfLaTeX on a standard TeX Live installation. `build_local.sh` is the wrapper used for the included PDF. The final source received independent mathematical review, every PDF page was visually inspected, and the exact rational certificate was rerun. These are ordinary mathematical proofs, not Lean formalizations or externally refereed results. No exhaustive priority claim is made.

The source comparison is pinned to ProveIt commit `ca81647a9f679e96d49ffdbc54b0c0ab13d10a36`. The bibliography credits the coefficient model, classical polynomial family, and varying-recurrence zero-distribution theory. The report gives a self-contained trace-moment proof of the required spectral specialization.
