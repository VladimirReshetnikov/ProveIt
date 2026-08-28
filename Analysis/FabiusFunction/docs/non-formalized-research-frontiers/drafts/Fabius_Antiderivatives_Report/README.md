# Antiderivatives of Monomially Weighted Fabius-Type Functions

This package accompanies the research report prepared on 27 August 2026.
The source audit is tied to ProveIt commit
`32d6d36c51d803289e6d6a0dc0c37753766eba47` and is documented in Sections 1
and Appendix A of the report.

## Package contents

- `fabius_antiderivatives.pdf` — rendered 29-page report.
- `fabius_antiderivatives.tex` — complete standalone LaTeX source.
- `numerical_experiments.py` — commented exact and high-precision checks.
- `verification_output.txt` — deterministic output from the default run.
- `fractional_power_checks.csv` — machine-readable comparison table.
- `requirements.txt` — pinned Python dependency.
- `PDF_VALIDATION.txt` — structural/rendering validation summary.
- `SHA256SUMS` — checksums for all package files other than itself.

## Main results represented in the report

The report develops the normalized Volterra ladder for the Fabius function,
a terminating dyadic formula for natural monomial powers, an absolutely and
locally uniformly convergent Newton–Volterra series for arbitrary complex
powers, negative-power and Mellin/Newton identities, complete piecewise
formulas for Rvachev's up-function, formulas for reflected/complementary
Fabius transforms, exact higher derivatives, Riemann–Liouville orders, and
first- and higher-order primitives of the inverse Fabius function.  It also
derives inverse-primitive and order-statistic asymptotics from the repository's
now-formalized inverse endpoint equivalent, and clearly labels conjectural
refinements.

## Rebuild the PDF

A TeX Live installation with `latexmk`, `pdflatex`, and the packages imported
by the source is sufficient:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error fabius_antiderivatives.tex
```

## Reproduce the numerical checks

```bash
python -m pip install -r requirements.txt
python numerical_experiments.py
```

The default run uses 85 decimal digits, moments `d_0,...,d_1500`, and centered
moments `c_0,...,c_700`.  It uses exact `fractions.Fraction` arithmetic for the
terminating identities and `mpmath` for nonintegral, negative, and complex
powers.  No Monte Carlo sampling is used.
