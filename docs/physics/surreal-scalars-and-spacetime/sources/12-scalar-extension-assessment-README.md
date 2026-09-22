# Surreal and Surcomplex Numbers in Theoretical Physics

## Black-hole singularities, asymptotic structure, and the limits of changing the scalar field

Prepared 21 September 2026.

The article is a 34-page critical mathematical assessment with 25 bibliography
entries. It reviews a pinned snapshot of VladimirReshetnikov/Surreal and primary
mathematical and relativity sources. It distinguishes established constructions,
explicit deductions proved in the article, and proposed physical applications.

### Main contents

The article develops the Schwarzschild curvature and proper-time tidal
calculations; a pole-persistence result; a formal Einstein-tensor reduction
theorem; a boundary-layer warning about differentiating standard parts; a
Hayward-type regular-core example with exact inner/outer Hahn support criteria;
Planck-curvature power counting; finite-dimensional Hermitian and quantum-shadow
theorems; and an explicit incompatibility between the canonical integer-part
phase and the normalized Berarducci–Mantova scalar derivation. It also discusses
surreal integration, quantum fields, renormalization, physical interpretation,
and a concrete research program for the repository.

The central assessment is positive about controlled asymptotic applications,
but does not identify scalar extension alone with geodesic completion or a
physical cure of black-hole singularities. No experimentally validated new
physical model, new black-hole solution, or priority claim is made.

### Files

- `article.pdf`: the typeset article.
- `article.tex`: standalone LaTeX source with embedded bibliography.
- `verify.py`: exact SymPy checks of selected finite symbolic identities.
- `verification.txt`: the recorded output; all 45 checks passed.
- `requirements.txt`: the SymPy version used for the recorded checks.
- `source_audit.md`: source and inspection scope.
- `README.md`: this file.

### Building the article

From this directory, with a TeX distribution and latexmk installed:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

No external bibliography, image files, or custom font files are required. The
source uses standard LaTeX packages and Latin Modern. The final build had no
undefined references, undefined citations, overfull boxes, or underfull boxes.
The rendered PDF was visually inspected.

### Running the checks

Python 3.10 or later is recommended. The recorded run used Python 3.13.5 and
SymPy 1.14.0.

```sh
python -m pip install -r requirements.txt
python verify.py
```

The script independently constructs the coordinate connection and curvature of
the general static spherical metric, then checks the formulas used in the
article. Its other checks include infall exponents, regular-core formulas,
matching identities, exact finite remainders, Gaussian regulator integrals,
and a simple probability normalization.

These are finite symbolic checks, not a formal verification of surreal fields,
Hahn summability in general, PDE existence, quantum theory, or any proposed
physical interpretation. The general mathematical arguments are in the article.
No Lean build of the repository was run for this assessment.
