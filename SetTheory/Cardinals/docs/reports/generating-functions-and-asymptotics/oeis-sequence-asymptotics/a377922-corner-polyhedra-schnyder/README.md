# Polynomial exponents for corner polyhedra and Schnyder labelings

Research note dated 2 October 2026

## Main results

The article proves the two-sided estimates

- p_n = Theta((9/2)^n n^(-1-pi/arccos(9/16))) for A377922
- s_n = Theta((16/3)^n n^(-1-pi/arccos(22/27))) for A377920

It also proves non-D-finiteness for A377922 and A377920, and for A377921 through the exact rational generating-function relation. It gives first-threshold inverse estimates with O(1) error without assuming coefficient monotonicity.

The full positive-amplitude asymptotic equivalents in Fusy–Narmanli–Schaeffer's Conjecture 25 remain unproved here. No coefficientwise Theta estimate for A377921 is claimed, and A377923 is outside the theorem.

This is a mathematical research manuscript with reproducible exact checks. It has not been externally peer reviewed or machine-formalized. No claim of publication priority is made.

## Files

- `article.pdf`: standalone 15-page research article
- `article.tex`: editable LaTeX source
- `build.sh`: portable two-pass PDF build, with TeX Live configuration fallbacks
- `requirements.txt`: Python dependency
- `scripts/verify_symbols.py`: exact kernel, corrector, covariance, cycle, and angle assertions
- `scripts/independent_corner_checks.py`: separate P algebra, cycle-shape, and enumeration checks
- `scripts/independent_schnyder_checks.py`: separate S resolvent, moments, and direct aggregate enumeration
- `scripts/enumerate_schnyder.py`: weighted recurrence through n=30 and exact OEIS comparison
- `scripts/run_all.py`: runs all verification scripts and records their results
- `results/`: machine-readable exact outputs and readable transcripts
- `audit/mathematical-verification.md` and `.json`: source-hash-bound integrated mathematical review and exact-check receipt
- `audit/visual-validation.json`: final PDF rendering and layout checks
- `audit/literature-status.md`: bounded public literature and overlap check
- `sources/`: official OEIS data excerpts and source provenance
- `SHA256SUMS`: checksums for the delivered package files

## Reproduce the exact checks

With Python 3 and SymPy installed, from the package directory run:

    python3 scripts/run_all.py

To install the declared dependency into an environment you control:

    python3 -m pip install -r requirements.txt

The scripts use exact integers and symbolic rational arithmetic. Only the displayed decimal exponent approximations use numerical evaluation. All scripts resolve inputs and outputs relative to their own package root, so the launch working directory does not matter. Verification overwrites the corresponding files in `results/`.

The recorded run used Python and SymPy versions stated in `results/verification-summary.json`. Successful scripts exit with status zero. A failed assertion or subprocess exits nonzero. Finite tests do not replace the general proofs in the article.

## Rebuild the article

A TeX Live installation with pdfLaTeX, Latin Modern, AMS packages, geometry, microtype, enumitem, booktabs, xcolor and hyperref is needed. Run:

    bash build.sh

The build performs two LaTeX passes and writes `article.pdf`. Temporary files stay in `build/`, which is not part of the delivery archive. PDF metadata use the manuscript date through `SOURCE_DATE_EPOCH`. Exact PDF byte reproducibility can depend on the TeX engine and font versions; mathematical source and result checksums are provided independently.

To render pages for visual inspection with Poppler:

    mkdir -p qa
    pdftoppm -r 120 -png article.pdf qa/page

To verify the delivery checksums before rebuilding or regenerating outputs:

    sha256sum -c SHA256SUMS

Reproduction can legitimately change version metadata or engine-dependent PDF bytes; the original checksum file records the delivered artifact state.

## Source credits

The counting bijections and original asymptotic conjectures are due to Éric Fusy, Erkan Narmanli and Gilles Schaeffer. The iid cone input is due to Denis Denisov and Vitali Wachtel. The non-D-finiteness argument uses the arithmetic regular-singularity and rational-exponent theorem in the form stated by Stéphane Fischler and Tanguy Rivoal, with related exposition by Alin Bostan, Kilian Raschel and Bruno Salvy. The article gives precise source links and theorem numbers.

The included `.seq` files are data excerpts from the official OEIS repository, preserving their contributor credits. OEIS data are distributed under the Creative Commons Attribution Share Alike 4.0 license; see https://oeis.org/wiki/The_OEIS_End-User_License_Agreement and the official repository https://github.com/oeis/oeisdata. The export commit and file hashes are in `sources/provenance.json`. The source papers themselves are referenced by verified links and are not redistributed in this package.
