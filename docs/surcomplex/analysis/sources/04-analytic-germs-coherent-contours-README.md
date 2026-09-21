# Surcomplex Analysis
## Hahn-Analytic Germs, Coherent Contours, and Infinitesimal Zero Clusters

Research exposition, September 21, 2026.

## Files

- `surcomplex_analysis.pdf`: the 32-page article, including contents, proofs,
  examples, a support-lemma appendix, and references.
- `surcomplex_analysis.tex`: complete, editable LaTeX source. The bibliography
  is embedded; no external images, bibliography databases, or custom fonts
  are required.
- `verify_examples.py`: six exact symbolic consistency checks of the examples.
- `verification.txt`: the output actually produced by the verification script.
- `requirements.txt`: the tested SymPy version for those optional checks.
- `Makefile`: commands for building the PDF, running the checks, and removing
  LaTeX auxiliary files.

## Mathematical framework

The article works over the proper-class field No[i], with set-sized supports
and coefficient data. It distinguishes three operations that must not be
conflated: fine-topological differentiation, Hahn summation, and coherent
coefficientwise contour integration.

The local theory realizes arbitrary formal power series on sufficiently small
surreal disks and develops differentiation, inversion, ramification, harmonic
conjugates, Laurent residues, and Lagrange inversion. A coherent class of Hahn
series with holomorphic complex coefficient functions supports Cauchy and
Morera theorems, identity and coefficientwise Liouville principles, and contour
integration in affine charts at arbitrary surreal scales.

Constructive Weierstrass preparation and division prove exact counts of actual
surcomplex zeros in infinitesimal monads. They also identify coefficientwise
residues with sums of actual local residues, yielding an argument principle
and a Rouché theorem. Rational projective geometry and explicit global
fine-analytic logarithms and nonunique exponentials complete the development.

## Building the article

Use a reasonably complete TeX Live or MiKTeX installation. The article uses
standard LaTeX packages, including AMS packages, mathrsfs, Latin Modern,
microtype, geometry, booktabs, longtable, enumitem, hyperref, bookmark, and
fancyhdr.

Run:

```sh
make pdf
```

Or run the following command three times so that contents, citations, and
cross-references stabilize:

```sh
pdflatex -interaction=nonstopmode -halt-on-error surcomplex_analysis.tex
```

The delivered PDF was built with pdfTeX 1.40.26, has no unresolved references
or overfull boxes, and was rendered and visually inspected.

## Running the optional exact checks

The recorded run used Python 3.13.5 and SymPy 1.14.0. In an environment with
Python and pip, install the optional dependency and run:

```sh
python -m pip install -r requirements.txt
python verify_examples.py
```

Alternatively, run `make check`. Failures raise an exception and return a
nonzero exit status. The six checks concern the factorial-series differential
identity, Lambert inverse coefficients, two split-root expansions, the first
Weierstrass preparation coefficients, a separated-scale quadratic, and a
rational ramification example.

## Proof status and scope

The symbolic checks verify only finite algebraic identities; they are not a
formal verification of the general theorems. No independent peer review,
Lean formalization, or historical priority is claimed.

The article proves its proposed transfers and constructions within explicit
hypotheses. It takes surreal normal forms, real closedness, the stated
properties of Gonshor exponentiation, and named ordinary complex-analytic
theorems as foundational inputs. It does not claim that fine complex
differentiability alone implies Hahn analyticity, that arbitrary local
analytic functions satisfy coherent contour theorems, or that the displayed
full-field exponential extensions are uniquely determined.
