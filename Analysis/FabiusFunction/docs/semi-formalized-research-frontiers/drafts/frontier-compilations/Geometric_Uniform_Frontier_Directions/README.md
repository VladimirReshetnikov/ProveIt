# Frontier Directions for Fabius–Rvachev Analysis

This package contains the current source, the last validated compiled PDF,
deterministic numerical experiments, figures, and machine-readable tables for
the report dated **30 August 2026**. The PDF has not yet been regenerated from
the merge-resolved source described below.

## Intake provenance

The package was filed from `drafts/incoming/fabius_frontier_report_bundle-D.zip` (1,508,514 bytes; SHA-256 `39f3638f52f19955b88b7a865a60b76d9ce31154d98967d1400a6ad97396fa9a`). The archive was safety-checked and its submitted 34-row checksum ledger passed in full. The exact arrival receipt remains recoverable from Git history. A later normalized-package ledger covered the current-at-that-checkpoint source and metadata together with the retained historical PDF, but package-local checksum manifests have since been retired; that historical check did not assert that the PDF rendered the source.

Repository normalization retained the mathematical body while replacing the submitted Letter/Latin-Modern preamble with the shared A4/27 mm/Libertinus preamble, regenerating all vector figures with embedded non-Type-3 fonts, and making generated CSV line endings deterministic. The report now states its current Lean boundary and its overlap with the separately audited digital-spectral and reciprocal-integer reports.

## Main deliverables

- `fabius_frontier_report.tex` — current 1,615-line, 77,411-byte report
  source; SHA-256
  `a0f877d99af685749b562fe0b007fcfd0e78699214bca4a0cb94f19174b59afd`.
- `fabius_frontier_report.pdf` — last validated 30-page A4 render of the
  preceding source checkpoint; it is not synchronized with the current TeX.
- `source/fabius_frontier_experiments.py` — 874-line deterministic experiment suite.
- `figures/` — eight vector PDF figures used by the report and eight PNG previews.
- `data/` — eleven CSV, TXT, and JSON outputs used for numerical checks.
- `requirements.txt` — pinned Python package versions used for the validated replay.
- `REPOSITORY_AUDIT.md` — source-audit, claim-boundary, replay, nonduplication,
  verified intake-ledger, and normalized-package provenance record.
- `PDF_VALIDATION.txt` — last-render build, geometry, font, text, and visual
  checks, plus the current uncompiled-source fingerprint.
- Historical checksum records — the verified 34-row submission receipt and a
  later normalized-package checkpoint are retired from the live tree but
  remain recoverable from Git history.  The separate source/PDF synchronization
  debt remains explicit here and in `PDF_VALIDATION.txt`.

## Claim and formalization boundary

The report distinguishes proved manuscript results, proof programs, numerical evidence, and conjectures. “Novel” means absent from the arrival-time repository snapshot, not worldwide priority.

The current Lean corpus already supplies the geometric-uniform series and
distribution, their positive-parameter CDF/density/support and
convolution/cumulant-tail interfaces, finite sinc products, a general weighted
analytic sinc--zeta expansion, and the fixed dyadic half--quarter multisection.
It now also supplies the recursive rational moment polynomial, its real,
inner-complex, and exterior-germ coefficient bridges, the sharp degree, and the
one-definition/four-theorem rational-function clearing/evaluation package. That
last package makes canonical q-series label `thm:qF-moment-polynomial` Exact;
the broader `thm:geometric-uniform-mgf` remains Partial. The report does **not**
thereby elevate its positive-integral-coefficient conjecture, negative-parameter
duality, closed all-parameter Bernoulli cumulants, Gaussian/LDP limits, exact
subdyadic plateaux and derivative norms, arbitrary-parameter zero divisor and
spectral zeta, Legendre scaling, or arbitrary-parameter periodic Laplace phase
to Lean theorems. In particular, the periodic-phase contour step remains a
paper proof, and no additional coverage-ledger status changes merely because
this package is filed.

## Principal directions developed in the report

1. an affine duality reducing negative geometric-uniform parameters to positive ones;
2. Bernoulli cumulants and Bell-polynomial moments for arbitrary `q`;
3. log-concavity, the central plateau, and signed-copy derivative formulas for `0 < q <= 1/2`;
4. a zero divisor, spectral zeta function, zero density, and reciprocal-integer digit-sum counts for the infinite sinc product;
5. recovery of the Thue–Morse sign from cumulative zero-count parity in the dyadic case;
6. normalized `q`-moment polynomials and a positive-integral-coefficient conjecture checked through order 30;
7. Gaussian/Edgeworth, large-deviation, and Legendre heat-kernel scaling regimes as `q -> 1`;
8. a dilation-periodic Laplace decomposition with Gamma–zeta Fourier coefficients and endpoint/inverse conjectures.

## Reproducing the numerical experiments

Create an isolated Python 3.13 environment and install the pinned packages:

```bash
python -m venv .venv
source .venv/bin/activate        # Windows PowerShell: .venv\Scripts\Activate.ps1
python -m pip install -r requirements.txt
python source/fabius_frontier_experiments.py --output-root .
```

The validated replay used NumPy 2.3.5, SciPy 1.17.0, SymPy 1.14.0, mpmath 1.3.0, and Matplotlib 3.10.8. It reproduced all exact tables. Relative to the submitted archive, only ordinary floating-point/platform drift occurred: four of 42 fields in `edgeworth_errors.csv` changed by at most `2.7755575615628914e-15`; 112 of 396 fields in `large_deviation_rate.csv` changed by at most `5.572764472105973e-13`; and 27 of 63 fields in `periodic_fourier_check.csv` changed by at most `2.2455452587358634e-18`. Seven of eight PNG previews reproduced byte-for-byte; the remaining preview kept the same dimensions with 99.9629% of whole pixels identical and a mean channel difference below `0.001`. Vector PDFs were deliberately regenerated with non-Type-3 fonts.

No random sampling is used. The program reconstructs densities by FFT from the characteristic product, uses exact polynomial recurrences for moment experiments, and switches to arbitrary precision for the cancellation-sensitive Legendre calculation. Aggregate results are recorded in `data/experiment_metadata.json` and `EXPERIMENT_RUN.txt`.

## Compiling the report

From the package root, run three serial strict passes:

```bash
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error fabius_frontier_report.tex
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error fabius_frontier_report.tex
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error fabius_frontier_report.tex
```

## Integrity provenance

Package-local checksum manifests are retired repository-wide and must not be
recreated.  The submitted and normalized-package verification records remain
recoverable from Git history, while `REPOSITORY_AUDIT.md` and
`PDF_VALIDATION.txt` record the surviving purpose-specific checks.  The arrival
receipt applies to the original archive, not to normalized current files, and
the pending source/PDF rebuild remains recorded above.
