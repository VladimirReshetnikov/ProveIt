FINITE SPECTRAL CERTIFICATES AND ARITHMETIC DETERMINANT BOUNDS
Research note prepared for Vladimir Reshetnikov
26 November 2026

START HERE
  report.pdf                 Complete report with proofs and references.
  report.tex                 Main LaTeX source.
  sections/*.tex             All included sections and bibliography.

RESULTS
1. A finite residual/Hermite certificate for complete cluster counts in a
   positive summable spectrum with integer multiplicities. It uses 2m+1
   consecutive moments, includes explicit error bounds, and eventually
   succeeds under adaptive refinement at a threshold outside the spectrum.
   The zeta application uses x = 1/(1/4 + gamma^2) and RH.
2. For a full-row-rank integer r-by-n matrix, n>=5 and 2<=r<=n-2:
     det(A A^T)/D^2 >= max{N-z, (8/5)N-4z, (12/5)N-12z},
   where N=choose(n,r), z counts zero maximal minors, and D is the gcd of
   the nonzero maximal minors. Equality examples are supplied.
3. A finite-factor surgery theorem preserves an exact finite Taylor jet,
   real zeros, and the eventual zero-counting function while planting a
   prescribed high multiple zero. The modified functions are not asserted
   to be arithmetic L-functions.

The formulations are derived here, with full mathematical proofs. Classical
ingredients and closely related literature are identified. Historical
priority is not established by the targeted search. The report is not an
externally peer-reviewed paper or a complete Lean formalization.

REPRODUCE EXACT ARITHMETIC (Python 3.10 or later; standard library only)
From this directory:
  python3 code/certify.py
  python3 code/determinant_verify.py
  python3 code/surgery_verify.py > artifacts/surgery_results.json

Verify the standalone input example:
  python3 code/certify.py --input artifacts/certificate_input.json --output artifacts/input_verification.json

The certificate example has a genuine infinite geometric tail, summed
exactly. It certifies cluster counts (1,2,1) above 1/8 with moments p25..p31.
Negative controls test a missing cluster and insufficient input precision.
The verifier assumes that supplied moment enclosures are mathematically
valid; it is not a proof that arbitrary data come from the intended spectrum.

OPTIONAL NUMERICAL ILLUSTRATION AND FIGURES
The exact scripts above need no packages. For the additional scripts, the
versions used in this environment are recorded in requirements.txt.
  python3 code/zeta_demo.py
  python3 code/make_figures.py

The zeta script uses high-precision mpmath, not rigorous ball arithmetic.
Its output is a numerical illustration, NOT a certified zeta-zero count.
The report proves the theorem independently of this illustration.
The two figure PDFs needed by LaTeX are already included.

COMPILE THE REPORT (a normally configured TeX Live installation)
  latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex
or run pdflatex report.tex until references stabilize (usually 2-3 runs).

FILES
  code/certify.py                Exact general certificate verifier.
  code/determinant_verify.py     Exact minors, gcds, determinants, examples.
  code/surgery_verify.py         Exact Newton and Taylor identities.
  code/zeta_demo.py              Clearly labeled non-certified illustration.
  code/make_figures.py           Rebuild the two static research figures.
  artifacts/*.json              Complete numerical inputs and outputs.
  artifacts/source_manifest.json
                               Inspected upstream commit and file hashes.
  artifacts/verification.txt    Scope and results of the checks performed.
  figures/*.pdf, figures/*.png  Vector and raster versions of the figures.
  SHA256SUMS.txt                 Integrity hashes of packaged files.

UPSTREAM SOURCE
  https://github.com/lsernau/grh-lean
  commit 72fead102f663d5c7a407964a13dc0cf9d977207
  https://en.wikipedia.org/wiki/Riemann_hypothesis

The repository's exported scope is RH and GRH for Dirichlet L-functions.
The present work inspected selected source files and their statement
dependencies; it did not rebuild the full upstream proof.
