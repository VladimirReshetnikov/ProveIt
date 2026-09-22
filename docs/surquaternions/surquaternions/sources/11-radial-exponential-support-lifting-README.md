# Surquaternions

## Algebra, Infinitesimal Geometry, and Support-Controlled Analysis over the Surreal Numbers

A 32-page mathematical article prepared for Vladimir Reshetnikov, dated
21 September 2026.

## Files

- `surquaternions.pdf`: the compiled article, with linked contents and references.
- `surquaternions.tex`: complete standalone LaTeX source; bibliography is embedded.
- `verify.py`: exact symbolic checks using SymPy.
- `verification_results.json`: the recorded results, including software versions.
- `requirements.txt`: the tested SymPy version.
- `README.md`: this guide.

## Mathematical scope

The construction is the Hamilton quaternion algebra over the surreal scalar
field. Three levels are kept distinct: finite algebra over an arbitrary real
closed field, set-sized Hahn workspaces, and statements about the full surreal
class. The article develops the following subjects with proofs.

**Finite algebra and geometry (Sections 2–6).** Division, conjugation, positive
scalar-valued magnitude, centralizers and complex slices, conjugacy spheres,
the spin description of three-dimensional rotations, matrix realizations,
a constructive fundamental theorem for one-sided quaternion polynomials,
explicit square roots, and finite-dimensional Hermitian spectral theory.

**Valuation and infinitesimal geometry (Sections 7–10).** Quaternion-valued
Hahn normal forms, localization of every set of surquaternions into a divisible
set-sized workspace, exact leading coefficients, residue algebra equal to the
ordinary quaternions, the Neumann support certificate, infinitesimal exp/log,
BCH, the associated graded rotation bracket, and finite-angle polar coordinates
at arbitrary surreal radius. Fine topology and intrinsic workspace topology
are expressly distinguished.

**Global exponential (Sections 11–12).** A conjugation-equivariant radial
exponential using the established Ehrlich–Kaplan scalar phase normalization,
its full logarithm fibres, and its four-coordinate differential. The chosen
normalization produces rank-two critical points at positive radii in pi*Oz,
including the infinite radius omega. This construction is not an everywhere
Hahn-summed power series and is not an additive-to-multiplicative homomorphism
for noncommuting arguments.

**Analysis and perturbation (Sections 13–15).** Admissible slice power series,
common-domain coherent coefficient families, a coefficientwise Cauchy formula,
a polynomial and coherent Fueter–Laplacian identity, support-controlled
multivariable implicit lifting, exact square-root linearization and a
quantified near-singular lifting region, and extension/classification of
scalar derivations. Ordinary contour integration, fine differentiation, and
field derivations are different operations throughout.

**Computation and formalization (Sections 16–17).** Scalar-backend requirements,
exact representations and support certificates, proposed reusable Lean layers,
limitations, and research directions. No Lean implementation is claimed to
have been added to the repository.

## Build the article

Use a TeX distribution with the usual AMS packages, Latin Modern, geometry,
microtype, booktabs, longtable, array, enumitem, xcolor, fancyhdr, hyperref,
and cleveref. No external images or bibliography database are needed.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error surquaternions.tex
```

Alternatively, run `pdflatex` repeatedly until cross-references stabilize.
The delivered build has 32 pages, no undefined references or citations,
and no overfull or underfull boxes. All pages were rendered for visual
inspection, with selected formula-heavy pages examined at a larger size.

## Run the finite checks

Python 3.9 or later is intended. The recorded run used Python 3.13.5 and
SymPy 1.14.0.

```sh
python -m pip install -r requirements.txt
python verify.py
```

All 31 named checks passed in the delivered run. They include generic
associativity, norm multiplicativity, matrix representation, the full
square-map Jacobian, noncommutative polynomial ordering, exp/log inverses
through degree six, BCH through degree four, a displaced square root through
degree seven, and Fueter identities for powers zero through seven.

The script overwrites `verification_results.json` with the results of each
new run. Its arithmetic is exact. These are finite identity and truncation
checks, not a formal verification of the general theorems about proper
classes, arbitrary real closed fields, or infinite well-ordered supports.

## Provenance and status

Repository orientation used the snapshot
`39f2be6667ade51bca2b45daa47e289d69c09764` of
`VladimirReshetnikov/Surreal`. The inspected sources include its root README,
document catalogue, trigonometry overview, and Neumann-support Lean module.
No repository files were modified and its build was not represented as a
verification of this article.

Primary literature is cited in the article. Classical quaternion results and
existing scalar-surreal constructions are attributed rather than presented
as new discoveries. The article is an AI-assisted research draft with written
proofs and finite symbolic checks; it is not refereed or machine-checked in
Lean. It makes no exhaustive first-publication claim.
