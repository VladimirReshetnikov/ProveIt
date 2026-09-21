# Surcomplex Trigonometry

**Canonical Phases, Arbitrary-Scale Triangles, and Infinitesimal Degeneration**

A self-contained mathematical article developed from the three supplied
surcomplex-analysis manuscripts and additional primary literature.
Date: September 21, 2026.

## Contents

- `surcomplex_trigonometry.pdf`: typeset article with proofs and references.
- `surcomplex_trigonometry.tex`: complete LaTeX source, including its bibliography.
- `verify_examples.py`: exact symbolic checks of algebraic identities and finite Taylor jets.
- `verification_report.txt`: the actual report from running the checks (43 passed).
- `requirements.txt`: pinned SymPy version used for the checks.
- `build.sh` and `build.ps1`: PDF build scripts for Unix-like systems and PowerShell.

The original input archives are not duplicated in this package. Their titles,
filenames, and roles are identified in the article's provenance section and
bibliography. They are not required to build or read this standalone article.

## Main mathematical content

The article constructs the finite-angle parameterization of every surcomplex
unit direction, identifies the canonical global trigonometric normalization,
and proves triangle and circle theorems at arbitrary surreal length scales.
It also develops valuation-sensitive phase estimates, a relative criterion
for nearly flat triangles, square-root degeneration formulas, a collision-stable
quadratic intersection algebra and residue pairing, and sharp conditioned
inverse-cosine estimates. Finite Fourier identities and spherical and
hyperbolic sine/cosine laws are included.

The canonical global construction is attributed to the established
Ehrlich–Kaplan theory, not presented as a new invention. The extra freedom
left by local analytic laws is treated separately. Strong Hahn summation,
coefficientwise integration, and fine-topological convergence are kept distinct.

## Rebuild the PDF

Install a standard LaTeX distribution with pdfLaTeX and the common packages
listed in the source (AMS mathematics, Latin Modern, geometry, microtype,
hyperref, cleveref, fancyhdr, booktabs, enumitem, xcolor).
The bibliography is embedded; BibTeX or Biber is not needed.

On Linux or macOS:

```sh
sh build.sh
```

On Windows with PowerShell:

```powershell
./build.ps1
```

Alternatively, run `pdflatex -interaction=nonstopmode -halt-on-error
surcomplex_trigonometry.tex` three times from this directory.

## Run the optional symbolic checks

```sh
python -m pip install -r requirements.txt
python verify_examples.py
```

The accompanying run used Python 3.13.5 and SymPy 1.14.0. The script exits
nonzero upon a failed check and writes its result to `verification_report.txt`.
The script uses exact algebra and exact Taylor coefficients rather than
floating-point agreement.

## Status and limits

The 43 checks are consistency checks of explicit formulas, not formal proofs
of the general theorems. They neither implement the proper class of surreal
numbers nor establish Hahn summability. General assertions are supported by
the article's mathematical proofs and the foundational references it cites.
No proof-assistant verification or exhaustive claim of novelty is made.

All polygon sizes, Fourier grid sizes, and polynomial degrees are ordinary
finite integers. Arc/sector and integral Parseval formulas use the expressly
defined coefficientwise Hahn functional; they are not claims about a
full-class fine-topological Riemann integral.
