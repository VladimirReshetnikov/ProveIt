# Inverse Functions of q-Pochhammer Symbols, Gaussian Coefficients, and Related q-Analogues

This archive accompanies the 59-page report
`inverse_q_analog_functions.pdf` and its LaTeX source.

## Scope

The report develops a branchwise theory of compositional inversion for finite
and infinite q-Pochhammer symbols, Gaussian/q-binomial coefficients,
continuous-order q-products, q-gamma and q-beta functions, q-numbers,
q-exponentials, a normalized q-polylogarithm, and parameter-dependent basic
hypergeometric functions. It treats regular Taylor reversion, Puiseux branches,
root-of-unity collisions, logarithmic endpoint inverses, large-parameter
scales, condition numbers, monodromy, simultaneous inversion, conjectures, and
future research problems.

Special attention is given to expansions near q=0, q=1, q=-1, q approaching
roots of unity, and q tending to positive or negative infinity, as well as
inversion with respect to product arguments, continuous orders, upper and
lower Gaussian parameters, and q-gamma/q-beta arguments.

## Files

- `inverse_q_analog_functions.pdf` — rendered report.
- `inverse_q_analog_functions.tex` — complete LaTeX source.
- `inverse_q_analogs_experiments.py` — commented, self-contained numerical
  experiments at 80-digit precision.
- `numerical_results.tex` — generated table included by the report.
- `numerical_results.txt` — plain-text numerical log.
- `finite_pochhammer_branch_atlas.pdf` — generated branch-atlas figure.
- `log_periodic_correction.pdf` — generated log-periodic correction figure.
- `qgamma_inverse_branches.pdf` — generated q-gamma inverse-branch figure.

The report explicitly labels proved statements, conditional statements,
conjectures, and open problems. Numerical evidence is used only as evidence,
not as a substitute for proof.

## Reproducing the computations and PDF

From this directory, run:

```bash
python inverse_q_analogs_experiments.py
latexmk -pdf -interaction=nonstopmode -halt-on-error inverse_q_analog_functions.tex
```

The Python program has no network dependency and regenerates all three figure
PDFs and both numerical-results files.

## Dependencies

- Python 3
- `mpmath`
- `sympy`
- `matplotlib`
- A reasonably complete TeX Live installation with `latexmk`, Libertinus,
  `amsmath`, `mathtools`, `tcolorbox`, `hyperref`, and the standard graphics
  and table packages used in the source.

The supplied PDF was built with pdfLaTeX and passed an automated PDF preflight
(openable, unencrypted, 59 pages, no XFA) followed by full-page rendering and
visual inspection.
