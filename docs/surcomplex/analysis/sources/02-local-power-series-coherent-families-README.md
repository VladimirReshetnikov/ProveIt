# Surcomplex Analysis
## Local Power Series, Coherent Hahn Families, and Infinitesimal Zero Geometry

Research exposition, September 21, 2026.

## Contents

- `surcomplex_analysis.pdf`: the compiled article (35 pages).
- `surcomplex_analysis.tex`: complete, self-contained LaTeX source, with bibliography.
- `verify_examples.py`: optional exact symbolic checks of finite example truncations.
- `verification_results.txt`: output of the included verification script.

The article develops three explicitly separated levels: intrinsic normally
summed power-series germs over No[i], coherent Hahn families with ordinary
holomorphic coefficient functions, and canonical lifts of classical holomorphic
functions. Its main constructive result is a preparation and division theorem
for infinitesimal perturbations of ordinary zero divisors. Consequences include
exact zero-cluster counts, a weighted argument principle, and a finite-pole
residue theorem. Counterexamples explain which global claims require additional
hypotheses.

The surreal foundations and existing work on surreal analyticity and surcomplex
exponentiation are credited in the article. The article is a mathematical
research exposition with proofs, not an externally peer-reviewed or formally
verified publication. It does not assert verified publication priority for the
formulations developed here. Further directions are distinguished from proved
results.

## Rebuilding the PDF

Use a reasonably complete TeX Live or MiKTeX installation. No external figures,
separate bibliography database, or shell escape are required.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error surcomplex_analysis.tex
```

Alternatively, run `pdflatex surcomplex_analysis.tex` three times to resolve the
table of contents, theorem references, and citations.

The source uses standard packages including `amsmath`, `amssymb`, `amsthm`,
`mathtools`, `mathrsfs`, `lmodern`, `microtype`, `geometry`, `booktabs`, `longtable`,
`enumitem`, `xcolor`, `fancyhdr`, `aliascnt`, `hyperref`, and `cleveref`.

## Optional algebra checks

With Python 3.10 or newer and SymPy installed:

```sh
python verify_examples.py
```

The checks verify the cubic preparation product through parameter degree 12,
the two root branches through degree 6 in their auxiliary parameter, and the
Catalan/Lagrange inverse through degree 9. All calculations use exact rational
symbolic arithmetic. These finite checks are not substitutes for the article's
normal-summability and class-theoretic proofs.

## Reading order

For the central construction, read Sections 8–11. Sections 2–7 provide the local
foundations, Section 12 the limits of global principles, Section 13 classical
lifts, Section 14 examples, and Section 15 further directions. The appendix lists
the exact hypotheses accompanying each classical theorem analogue.

The contour integrals are explicitly coefficientwise external functionals on
ordinary contours and their chosen affine rescalings. They are not unqualified
Riemann integrals in the full surreal neighborhood topology.
