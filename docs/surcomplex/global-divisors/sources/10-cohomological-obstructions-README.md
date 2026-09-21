# Global Divisors and Cohomological Obstructions in Hahn-Coherent Surcomplex Analysis

A research continuation of the supplied `surcomplex_analysis(3).tex`, dated September 21, 2026.

## Contents

- `surcomplex_global_theorems.pdf` — the complete article.
- `surcomplex_global_theorems.tex` — editable LaTeX source with an internal bibliography.
- `verify_examples.py` — exact symbolic checks of finite algebraic examples.
- `verification.txt` — the successful output of those checks.
- `literature_audit.md` — source provenance, consulted literature, and novelty boundaries.

## Main results

The article proves an exact support criterion for global realization of infinitely many infinitesimal zero clusters, a deformed Hermite interpolation theorem with a support-restricted Chinese remainder quotient, and a moving-pole Mittag–Leffler theorem. It also identifies the exact additive Cousin obstruction on a puncture-and-disk cover and proves a vanishing/nonvanishing dichotomy for rank-one line bundles: vanishing occurs exactly for the trivial exponent group or an ordered copy of the integers.

The coefficient sheaves live on the ordinary complex plane. Their evaluations live on its finite surcomplex thickening. The nonnegative-exponent sheaf has local stalks; the Laurent Hahn sheaf does not. The article distinguishes the ordinary Picard group of the former from the group of locally free rank-one modules over the latter.

The symmetric coefficients of root clusters, not independently labeled root supports, determine divisor admissibility. An example realizes all roots of `(z-n)^n-t` simultaneously for every positive integer n, despite descending fractional root exponents. Another example shows why bounded 0/1 interpolation values may still force a globally forbidden support.

## Build

A standard TeX Live installation with pdfLaTeX, Latin Modern, AMS packages, microtype, fancyhdr, tocloft, hyperref, and cleveref is sufficient.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error surcomplex_global_theorems.tex
```

Alternatively run `pdflatex surcomplex_global_theorems.tex` twice. No BibTeX step or external bibliography is required.

## Run the finite checks

The script requires Python 3.10 or later and SymPy.

```sh
python verify_examples.py
```

The supplied run used Python 3.13.5 and SymPy 1.14.0 and passed 38 checks. These computations verify finite identities, not arbitrary Hahn summability, transfinite recursions, sheaf cohomology, or novelty. The general results depend on the proofs in the article.

## Research status

The local framework and local preparation/division arguments are inherited from the supplied manuscript and are not claimed as new here. The global theorems are developed and proved in this article. No matching statement was located in the primary sources consulted, but no exhaustive novelty or priority certification is claimed. The proofs are not independently refereed or machine checked. The article does not claim to solve a named published open conjecture, classify all essential singularities, or construct an all-scale transcendental theory.
