# Exponential Accuracy and Stokes Transport for Inverse Harmonic Transseries

Research note prepared for Vladimir Reshetnikov, 29 September 2026.

## Read

`inverse_harmonic_transseries.pdf` is the complete article.
`inverse_harmonic_transseries.tex` is its self-contained editable LaTeX source.

The article extends the harmonic-inverse part of the ProveIt companion at
commit `04e06e032dff1966513bfba316966d52db3646b4`. The exact repository path,
inspected source ranges, result boundaries, and literature references are
recorded in the article. No repository files were modified.

## Results and boundaries

- A general factorial endpoint-extraction theorem and an all-orders formula
  for the large-order asymptotics of the inverse-harmonic coefficients.
- Explicit positive-real inverse certificates and a sharp error theorem for
  the inverse of a forward expansion truncated at order M = pi X + O(1).
- Borel summability/resurgence using credited existing closure theorems,
  plus an explicit convergent formula and tail bound for every inverse Stokes
  sector in the specified complex sector.
- Seven further research questions with proposed approaches.

The sharp exponential error theorem is for the root of a truncated FORWARD
expansion, not for a direct partial sum of the INVERSE series. The latter
sharp remainder problem is not claimed solved. General Binet formulas and
nonlinear resurgence closure are existing results. Global priority for the
specialized results has not been established. No new Lean formalization is
included.

## Build the PDF

Run from this directory, using a normal TeX installation:

```sh
pdflatex -interaction=nonstopmode -halt-on-error inverse_harmonic_transseries.tex
pdflatex -interaction=nonstopmode -halt-on-error inverse_harmonic_transseries.tex
```

A third pass is harmless when references change. The preamble lists all
packages; newtxtext/newtxmath, mathtools/amsthm, microtype, xurl, and cleveref
are among them. No external bibliography database or repository notation file
is needed. The pre-generated figure is included.

## Reproduce checks

Python 3.10 or later is required. Install the packages listed in requirements.txt,
then run:

```sh
python verification/verify.py
python verification/certify.py
python verification/make_figure.py
```

The first script carries out exact coefficient and symbolic residual checks,
190-digit numerical tests, and writes `verification/results.json`.

The second uses a 200-digit calculation ONLY to propose candidates. All final
interval assertions, initial truncation-root conditions, and forward endpoint
signs are checked with exact rational arithmetic plus the analytic inequalities
proved in the article. It writes `verification/certificates.json`. The targets
in that file are exactly gamma + log(X), with X a specified integer; the
finite-decimal interval endpoints are directed outwards.

The third script regenerates the figure. Floating-point tests and figure
values are diagnostics, not interval certificates. Assertions for arbitrary
order are established by the article's proofs, not by a finite test suite.

The JSON files and text logs in this archive are actual outputs from the run
used to prepare the article. Re-running may change last printed digits if
library versions differ. Rational assertions should remain unchanged.

## File integrity

`SHA256SUMS.txt` records the hashes of the delivered files (excluding itself).
No font files, downloaded papers, or repository source copies are included.
