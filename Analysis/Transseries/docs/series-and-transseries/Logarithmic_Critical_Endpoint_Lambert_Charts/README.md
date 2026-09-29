# The Logarithmic Critical Endpoint

**Convergent Lambert Charts, All-Order Sector Laws, and Sharp Action-Cutoff Corrections**  
Research draft prepared for Vladimir Reshetnikov, 29 September 2026.

## Main content

This 28-page article studies the positive countable-action equation

    U_beta(q) = beta * sum_{j>=1} a_j q^j exp(j U_beta(q)),

where `a_j = a/j^3` outside a finite set. It develops an exact convergent
Lambert–analytic critical inverse, an arbitrary-order inverse-logarithmic
sector expansion, a quantitative finite-coupling action-cutoff formula, and
convergent all-order functions for finite-action fold drift and curvature.
A further theorem treats leading inversion and cutoff laws for
`a_j ~ a j^(-3) (log j)^r`, including `r = -1`.

The preceding countable-action manuscript asks for endpoint logarithmic
charts and cutoff laws. This article treats the fixed upper endpoint, not
the full joint limit of its exponent with the sector index. The leading
Gaussian/extreme-scale separation has classical precedents, acknowledged
explicitly through Janson's Example 18.29. The specialized chart and
correction formulas are contributions developed here; worldwide publication
novelty has not been established. No Lean formalization is claimed.

## Files

- `article.tex`: complete editable article with bibliography; uses the four
  included generated table fragments under `data/`.
- `article.pdf`: compiled 28-page PDF.
- `code/verify.py`: exact symbolic checks and numerical diagnostics.
- `data/verification.json`: full results, precision and package versions.
- `data/verification_run.txt`: stdout from the supplied full verification run.
- `data/*_table.tex`: the four reproducible table fragments used by the article.
- `requirements.txt`: dependency versions used for the supplied run.
- `Makefile`: verification, PDF build and auxiliary-file cleanup targets.
- `PROVENANCE.md`: repository snapshot, inspected sources and audit boundaries.
- `BUILD_REPORT.json`: build and validation summary.
- `SHA256SUMS`: hashes of package files other than the ledger itself.

## Reproduce

The verified environment used Python 3.13.5 and pdfLaTeX from TeX Live.
From this directory:

```sh
python -m pip install -r requirements.txt
python code/verify.py --max-n 65536
make pdf
```

Without `make`, run the following command three times:

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

The PDF can be rebuilt without running the numerical program: all table
fragments are supplied. No external font files are required or bundled.
For a quicker numerical run, use `--max-n 4096`; this intentionally writes
shorter diagnostic tables. The supplied data and PDF use `--max-n 65536`.

## Verification boundary

Exact checks cover the first two nonconstant Lambert chart coefficients,
the finite-fold Y series through degree 7, the drift H series through degree
6, the composed curvature series through degree 5, and the Lagrange identity
through degree 6 in a rational test model. All these checks passed.

The numerical diagnostics are not interval certificates. Fourier coefficient
extraction has a separate rigorous alias bound in exact arithmetic, but its
floating-point roundoff is not globally enclosed. A comparison at index 128
with an independent 80-digit recurrence had relative discrepancy about
6.76e-15. Root calculations and displayed approximation errors are numerical
diagnostics, not replacements for the article's mathematical proofs.

The large-sector inverse-logarithmic series is asymptotic; convergence is
proved for the local Lambert chart and for the finite-fold generating
functions, not for that large-sector series. Finite-fold approximations may
be exponentiated only under the explicit conditions in Proposition 8.4.

The final PDF has no undefined references, overfull boxes or underfull boxes
in the recorded build. All pages were rendered for visual review; the front
matter was then improved and rechecked. The repository and Library were not
modified.
