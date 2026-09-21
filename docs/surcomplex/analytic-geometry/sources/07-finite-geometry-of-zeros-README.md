# Finite Geometry of Hahn-Coherent Surcomplex Zeros

**Conservation of Multiplicity, Normal Forms, and Collision-Stable Residues**  
September 21, 2026

## Contents

- `surcomplex_finite_geometry.pdf`: the 29-page article, including proofs, the worked example, support audit, notation, and references.
- `surcomplex_finite_geometry.tex`: self-contained LaTeX source with its bibliography embedded.
- `verify_examples.py`: exact SymPy checks of the length-five example.
- `verification_report.txt`: actual output of the verification script; all 43 checks passed.
- `README.md`: these reproduction and scope notes.

The original uploaded manuscript is cited as an unpublished source but is not required to compile this article. No external figures or bibliography files are required.

## Main mathematical result

For an ordinary holomorphic system of n equations in n variables with an isolated common zero of multiplicity mu, add arbitrary positive-support Hahn-coherent errors. The deformed monad algebra has dimension exactly mu, with the same selected polynomial basis. Normal forms and division certificates are produced on one common ordinary domain and have support inside the input support plus the additive monoid of the perturbation support.

The proof uses a support-controlled conjugacy of Koszul differentials. It does not assume convergence of a sequence in the surreal fine topology or require the value group to have rank one. The article also proves workspace independence, a monad Nullstellensatz, finite-projection statements, and a collision-stable residue pairing with a trace–Jacobian identity.

The worked example is

    x^2 - y^3 - s = 0,
    x y - u = 0.

Its algebra has dimension five. Its full collision equation is

    3125 u^6 - 108 s^5 = 0,

while the determinant of its residue Gram matrix is identically one.

## Compile the article

A standard TeX Live or MiKTeX installation with the packages listed in the preamble is sufficient. The PDF was compiled with pdfLaTeX and latexmk.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error surcomplex_finite_geometry.tex
```

Without latexmk, run pdfLaTeX three times to resolve the table of contents and cross-references.

## Run the exact checks

The script uses Python 3.9 or later and SymPy. It was tested here with Python 3.13.5 and SymPy 1.14.0.

```sh
python -m pip install sympy
python verify_examples.py --output verification_report.txt
```

The checks use exact symbolic arithmetic, not floating-point tolerances. They verify multiplication matrices, characteristic polynomials, discriminants, residue and trace Gram matrices, the trace–Jacobian identities, the explicit double-root specialization, and the three scaling calculations. They are not a formal proof-assistant verification of the general theorems.

## Relation to earlier work and novelty

The article directly addresses the several-variable direction proposed in the supplied `surcomplex_analysis(2).tex` manuscript. Published work by Cluckers–Lipshitz–Robinson and Cluckers–Lipshitz already develops multivariable Hahn analytic structures, preparation, and related normalization/Nullstellensatz results. Those results are credited rather than claimed as new.

The proposed contribution is the combined, explicit common-domain normal-form and residue construction, including arbitrary-support bounds and the workspace-exhaustiveness theorem. The precise package was not found in the literature checked, but this is not an exhaustive priority certification or a claim to settle a separately named published conjecture. Classical inputs and the limits of the conclusions are identified in the article.
