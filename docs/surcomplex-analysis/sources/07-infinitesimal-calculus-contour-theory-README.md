# Surcomplex Analysis
## Infinitesimal Calculus, Hahn-Coherent Holomorphy, and Contour Theory

Date: September 21, 2026

## Files

- `surcomplex_analysis.pdf`: complete 37-page article, including references.
- `surcomplex_analysis.tex`: self-contained LaTeX source with an inline bibliography.
- `verify_examples.py`: exact symbolic checks of illustrative formulas.
- `verification_report.txt`: output of the verification script.
- `README.md`: these build and scope notes.

## Main mathematical content

The article develops analysis over SC = No[i] in three explicitly distinguished
settings: fine-local formal analytic germs, Hahn-coherent holomorphic functions
on infinitesimal thickenings of ordinary complex domains, and a global
all-scale Hahn-coherent category.

Results include local inverse and implicit functions; ramification and
Cauchy–Riemann equations; coherent identity and gluing theorems; Cauchy, Morera,
primitive, and order-valued ML theorems; constructive Weierstrass preparation;
exact lifting of leading-coefficient zeros; residues at infinitesimally displaced
poles; the argument principle and Rouché variants; restricted Schwarz–Pick,
harmonic-conjugate and Poisson theorems; and polynomial/rational rigidity at all
surreal scales. Explicit exponentials, a global fine-analytic logarithm, and
counterexamples delimit which hypotheses cannot be dropped.

## Rebuilding the PDF

A normal TeX Live installation with Latin Modern and the packages named in the
preamble is sufficient. No external figures, bibliography files, shell escape,
or font files are required.

    latexmk -pdf -interaction=nonstopmode -halt-on-error surcomplex_analysis.tex

Alternatively, run `pdflatex surcomplex_analysis.tex` three times to resolve the
table of contents and cross-references. The supplied PDF was built with pdfLaTeX
and inspected after rendering. The final build has no undefined references or
citations and no overfull-box warnings.

## Running the exact finite checks

The script requires Python 3.10 or later and SymPy:

    python -m pip install sympy
    python verify_examples.py --output verification_report.txt

The supplied report was produced with Python 3.13.5 and SymPy 1.14.0. The script
checks the root-splitting expansion, the prepared polynomial through t^4, the
moving-pole residue identity through t^6, the second-order simple-root formula,
and a finite instance of the preparation recursion through t^6. All comparisons
use exact symbolic arithmetic, not floating-point tolerances.

## Scope and proof status

This is a theorem-driven research exposition, not a declaration that there is
one canonical foundation for surcomplex analysis. The contour functional is a
coefficientwise Hahn integral, not an ordinary Riemann integral in the full fine
topology. "All-scale Hahn-entire" is a strong condition defined in the article;
it is not a synonym for every possible notion of surcomplex entire function.

The article cites existing surreal/Hahn analysis and gives proofs of its stated
constructions and analogs. No exhaustive claim of novelty, independent referee
validation, or machine-checked verification is made. The symbolic checks verify
finite example expansions only. They do not verify the general theorems or the
set/class and strong-summability arguments.
