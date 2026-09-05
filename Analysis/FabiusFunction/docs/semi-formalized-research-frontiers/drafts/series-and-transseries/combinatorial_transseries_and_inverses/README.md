# Combinatorial Transseries and Their Inverses

Research extension prepared for Vladimir Reshetnikov, 4 September 2026.

## Main files

- `combinatorial_transseries_extension.pdf`: the rendered 29-page article.
- `combinatorial_transseries_extension.tex`: self-contained LaTeX source. The
  Wolfram Language listing is embedded; no other input file is required to compile it.
- `coefficients.wl`: a separately usable copy of the Wolfram Language definitions.
- `verify.py` and `audit.py`: executed coefficient and numerical verification scripts.
- `verification_results.json` and `audit_results.json`: outputs from those runs.
- `requirements.txt`: Python package versions used for the checks.
- `build.sh`: a PDF build helper.

## Scope

The article develops forward and inverse expansions for balanced factorial ratios
(Fuss--Catalan numbers, central multinomial coefficients, and rectangular standard
Young tableaux), fixed Stirling and Eulerian columns, Motzkin and central trinomial
numbers, involutions, Euler zigzag numbers, and central Gaussian binomial
coefficients at fixed real q > 1. It gives finite all-order coefficient formulas,
explicit real or parity-resolved interpolations, convergent sector formulas where
proved, residual error certificates, and discrete threshold recovery rules.

The parent article was consulted on its public GitHub `main` branch on
4 September 2026. This is an access-date reference, not a pinned-commit claim.
The bibliography in the article contains the source references.

## Build the PDF

A standard TeX Live or MiKTeX installation with the packages named in the preamble
is sufficient. Run `sh build.sh`, or run:

    pdflatex -interaction=nonstopmode -halt-on-error combinatorial_transseries_extension.tex
    pdflatex -interaction=nonstopmode -halt-on-error combinatorial_transseries_extension.tex
    pdflatex -interaction=nonstopmode -halt-on-error combinatorial_transseries_extension.tex

The repeated passes resolve the table of contents and cross-references.
There are no required external images, fonts, bibliography databases, or code inputs.
The included PDF was built successfully and its rendered pages inspected.

## Reproduce the computational checks

Python 3.10 or newer is required. The executed environment used
Python 3.13.5, SymPy 1.14.0, and mpmath 1.3.0.
From this directory, run:

    python -m pip install -r requirements.txt
    python verify.py
    python audit.py

The scripts regenerate their corresponding JSON output files. The calculations
need no network access after installing the Python packages. Both scripts must
remain in the same directory because `audit.py` imports shared routines from
`verify.py`.

The symbolic checks use exact rational arithmetic. Numerical tests use 90 decimal
digits; they are not interval-arithmetic certificates. In particular, the reported
inverse errors use targets equal to known exact sequence values, rather than an
unverified root finder as ground truth. The Wolfram Language code was provided but
was not run in a Wolfram kernel in preparing this article.

## Mathematical qualifications

An inverse of a sequence is not canonical until an interpolation or discrete
threshold convention is chosen. The article specifies those conventions.
Asymptotic amplitude series, exact analytic blocks, and convergent sector-marker
expansions are distinguished throughout. No complete complex Stokes classification
or Lean formalization is claimed.

Appendix A records an exact-arithmetic recurrence audit of the involution
coefficients and a discrepancy with one displayed coefficient in the specifically
cited HTML version arXiv:2410.16334v1. It does not make claims about that paper's
separately linked high-order data or software.
