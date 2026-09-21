# Finite Hahn Deformations in Surcomplex Analysis

**Multivariable Division, Conservation of Multiplicity, and Residue Duality**  
Research draft dated September 21, 2026.

## Contents

- `surcomplex_finite_deformations.pdf`: the complete 29-page article.
- `surcomplex_finite_deformations.tex`: self-contained LaTeX source, including bibliography.
- `verify_examples.py`: exact symbolic checks of the worked examples.
- `verification_report.txt`: output of the verification script as actually run.
- `research_scope.md`: research provenance, novelty scope, and proof dependencies.

The article extends the Hahn-coherent framework in the user-supplied
`surcomplex_analysis(3).tex`. It is readable independently: the required
coefficient algebra, summation convention, and ordinary hypotheses are restated.
The supplied original has not been modified.

## Main results

Theorem 5.1 proves division on one fixed ordinary polydisc and finite freeness of
the perturbed complete-intersection quotient, with explicit Hahn support bounds.
Theorems 6.2 and 6.3 identify the quotient's characters and local factors with
actual surcomplex zeros and their formal local algebras, proving exact
conservation of multiplicity. Theorems 8.2, 9.2, and 9.4 prove residue duality,
the trace–Jacobian identity, and the discriminant identity. Theorem 10.1 gives
valuation precision estimates; Corollary 10.2 gives a discriminant threshold for
preserving simple zeros.

The results allow arbitrary well-ordered positive perturbation supports and
higher-rank value groups. They do not assume that the Hahn valuation ring is
Noetherian. They concern isolated ordinary complete intersections, not arbitrary
positive-dimensional analytic spaces.

## Build the PDF

A standard TeX Live or MiKTeX installation with pdfLaTeX and the packages named
in the preamble is sufficient. From this directory, run twice:

```sh
pdflatex -interaction=nonstopmode -halt-on-error surcomplex_finite_deformations.tex
pdflatex -interaction=nonstopmode -halt-on-error surcomplex_finite_deformations.tex
```

No external images, fonts, or BibTeX database are required. The delivered PDF was
compiled without unresolved references or overfull-box warnings and was rendered
and visually inspected.

## Run the finite checks

```sh
python -m pip install sympy
python verify_examples.py
```

The included run used Python 3.13.5 and SymPy 1.14.0. All assertions passed.
These are exact finite symbolic checks, not proof-assistant certification of the
general theorems.

## Research status

The precise combined theorem package was not located in the literature checked
for this draft. This is a qualified novelty assessment, not an exhaustive
priority certification. The article uses established ordinary analytic algebra,
Neumann summability, homological perturbation, and Grothendieck residue duality,
with explicit attribution. It addresses an unfinished direction in the supplied
manuscript rather than claiming to settle a named published conjecture. The
article is not peer reviewed or formally verified.
