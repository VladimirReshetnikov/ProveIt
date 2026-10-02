# Late coefficients of three letter abelian squares

This package proves the asymptotic conjecture in OEIS A274600, the late coefficients of A002893. Read `honeycomb_late_coefficients.pdf`; the editable, self-contained source is `honeycomb_late_coefficients.tex`.

## What is proved

- The exact normalized Borel transform and the required complex continuation
- The leading factorial asymptotic and every fixed late correction order, with a rigorous remainder
- The exact physical median, lateral Stokes jump, and every fixed fluctuation order
- Lambert-function inversions for both the late coefficients and the original moment counts
- A convergent Lagrange generator of the inverse exponential sectors, with every fixed-sector remainder

The convergent auxiliary-parameter sector expansion is distinct from its all-fixed-order inverse-power fluctuations. The physical inverse is not the arithmetic mean of the lateral inverses. The note does not classify all farther Borel sheets or prove optimal-truncation/Stokes-smoothing estimates. The source/novelty search is bounded and is documented in the article and `SOURCES.md`.

## Offline replay

Requirements: Python 3.10 or later and mpmath 1.3.0 or compatible. Both replay scripts use no network. The exact arithmetic uses only Python integers and fractions. Numerical checks are consistency tests, not interval-certified proofs.

Run:

    bash replay.sh

The replay verifies the package checksums, checks the 22 displayed OEIS terms, independently matches the first 31 Borel-germ coefficients, generates coefficients through index 500, compares them byte-for-byte with the retained exact baseline, asserts finite sanity bounds for density integrals, the four-term Stokes-integral approximation, and the two Lambert inversions, and writes fresh reports to a temporary directory. It does not overwrite the sealed baseline reports. The temporary directory is removed after a successful replay. The exact inverse-sector family in equations (36c-h) is analytically reviewed; these scripts do not numerically test that family.

## Rebuilding the article

With an installed TeX Live distribution, run:

    bash build.sh

The source requires standard LaTeX packages: amsmath, amssymb, amsthm, lmodern, microtype, geometry, enumitem, xcolor, hyperref, booktabs, longtable, and array. The script has a local-format fallback for containers with installed but unindexed TeX files. No TeX packages are downloaded. SOURCE_DATE_EPOCH is fixed for reproducibility; byte-identical PDFs also depend on the TeX versions and font installations.

## Contents

- PDF and editable TeX source
- Two verification scripts and offline replay/build entry points
- Exact coefficients through index 500 and the retained numerical reports in `expected/`
- Source bibliography and bounded duplicate-search metadata
- Concise mathematical-check and final visual-QA records
- SHA-256 manifest

The principal theorem is an analytic proof, not a machine-formalized theorem. No external OEIS submission or repository modification was performed.
