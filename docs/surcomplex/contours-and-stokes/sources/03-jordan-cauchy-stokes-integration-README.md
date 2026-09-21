# Jordan Separation, Cauchy Theory, and Stokes Integration on the Surcomplex Plane

Research article dated September 21, 2026.

## Contents

- `surcomplex_contours.pdf` — 37-page article, including the title page, table of contents, proofs, hypothesis audit, and 20 references.
- `surcomplex_contours.tex` — self-contained LaTeX source; no external bibliography or image files are required.
- `verify_examples.py` — exact symbolic checks using SymPy.
- `verification.txt` — recorded output: 244 exact checks passed.

## Building and checking

A standard TeX installation with pdfLaTeX and the packages listed in the source is sufficient.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error surcomplex_contours.tex
```

Alternatively, run `pdflatex surcomplex_contours.tex` repeatedly until cross-references stabilize.

The verification script requires Python 3.10 or later and SymPy. The included run used Python 3.13.5 and SymPy 1.14.0.

```sh
python verify_examples.py --report verification.txt
```

The script exits with an error on a failed identity and uses no numerical root approximations, network services, or floating-point arithmetic.

## Main mathematical content

The article distinguishes full-class fine topology, intrinsic topology on a set-sized Hahn field, the reduction topology at a chosen scale, and semialgebraic/definable geometry. It gives separate, precisely formulated counterparts of Jordan separation, Cauchy theory, and generalized Stokes rather than treating these as one unqualified transfer principle.

Constructive developments include polynomial simplex integration; the uniform Hahn de Rham complex and its cohomology; support-controlled Taylor pullbacks; Stokes for infinitesimally deformed chains; homotopy and endpoint transport; deformed Cauchy formulas; small-circle realization of radius-free one-variable germ residues; a coordinate-power complete-intersection torus formula; rational periods from algebraic winding; and exact comparisons between coefficientwise and valuation limits of root-of-unity samples.

The comparison section discusses semialgebraic topology, Schnirelman integration, Berkovich geometry, real tropical forms, perfectoid cycle integration, tame integration, and surreal extension/integration operators. Their hypotheses and output spaces are kept distinct.

## Source basis and status

The two user-supplied research manuscripts are explicitly cited throughout:

1. `surcomplex_analysis(3).tex`: *Surcomplex Analysis: Infinitesimal Calculus, Hahn-Coherent Holomorphy, and Contour Theory*.
2. `surcomplex_analytic_geometry.tex`: *Infinitesimal Analytic Geometry over the Surcomplex Numbers: Radius-Free Hahn Germs, a Nullstellensatz, and Conservation of Singular Zeros*.

They are not modified or redistributed in this archive. The article distinguishes their stated results, established external theorems, extensions proved in the article, and further research targets. It does not claim exhaustive priority certification or formal verification of the general proofs.

The exact checks validate finite identities and illustrative calculations, not arbitrary Hahn support conditions or the full theorem statements. The general arguments are mathematical proofs in the article. All computational workspaces and Hahn supports are set-sized; no proper-class summation is used.

## Verification coverage

- 56 triangle Stokes checks on monomial one-forms of total degree at most six.
- 60 tetrahedron Stokes checks on monomial two-forms of total degree at most three.
- 3 geometric integral identities.
- 36 root-of-unity polynomial-reduction identities.
- 5 pole-cluster residue identities.
- 7 radius-free circle coefficient checks.
- 39 two-variable quotient/residue checks.
- 36 two-variable trace–Jacobian checks.
- 2 differential and integrated endpoint-transport checks.

The PDF was compiled without unresolved references, warnings, or overfull/underfull boxes, and its rendered pages were inspected for layout.
