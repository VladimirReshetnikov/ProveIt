# Surcomplex Analysis via Hahn-Supported Holomorphic Functions

A proof-based mathematical article prepared September 21, 2026.

## Files

- `surcomplex_analysis.tex`: standalone LaTeX source, including the bibliography.
- `surcomplex_analysis.pdf`: compiled article.
- `verify_examples.py`: exact finite symbolic checks for the worked examples.
- `verification_results.txt`: output of those checks.
- `build.sh`: a three-pass PDF build with pdfLaTeX.

## Mathematical scope

The article constructs an explicitly specified analytic category over
K = No[i]. Its functions are set-supported Hahn series with ordinary
holomorphic coefficient functions, evaluated at surcomplex points by exact
infinitesimal Taylor summation. Affine charts allow arbitrary surcomplex
centers and scales.

The results include strong Taylor calculus; Cauchy–Riemann equations;
identity, maximum-modulus, and open-mapping principles; constructive
Weierstrass preparation and division; exact multiplicity-preserving zero
lifting; perturbative and general local inverse theorems; coefficientwise
Cauchy and Morera formulas; actual-pole residues and the argument principle;
Rouche-type zero conservation; and a removable-singularity theorem within
the meromorphic category.

A separate global construction gives a surjective exponential on the
finite-imaginary strip, explicit extensions to all surcomplex numbers, and
an obstruction to preserving only the classical period group. Counterexamples
explain why unrestricted differentiability or local power-series expansions
do not imply the usual global identity, removability, Liouville, or Schwarz
principles.

Hahn summation is not ordinary sequential convergence. The contours in this
article are coefficientwise integrals over ordinary shadow curves, not
integrals along nonconstant fine-continuous real paths. These distinctions
are part of the definitions and hypotheses, not suppressed qualifications.

## Build the PDF

Use a TeX distribution with pdfLaTeX and the packages named in the preamble
(AMS packages, Latin Modern, geometry, microtype, hyperref, cleveref,
fancyhdr, booktabs, enumitem, and the other standard packages).

On a POSIX shell:

```sh
sh build.sh
```

Alternatively, on any platform run this command three times in the folder:

```text
pdflatex -interaction=nonstopmode -halt-on-error surcomplex_analysis.tex
```

No bibliography processor or external illustrations are required. Font files
are not distributed with this archive.

## Run the example checks

Use Python 3.10 or later and SymPy. The included results were generated with
SymPy 1.14.0.

```sh
python -m pip install sympy
python verify_examples.py
```

The checks verify the simple-root expansion for z + t exp(z) through degree
12; the analytic preparation of z^2 + t exp(z) through degree 3 in t; and
three exact pairs of rational residues. They use rational/symbolic arithmetic,
not numerical approximations.

These checks do not implement the surreal number field and do not constitute
a formal verification of the general theorems. The mathematical proofs are
in the article. Published foundations are identified in the bibliography
and assumptions ledger; no claim of historical priority or peer review is
made.
