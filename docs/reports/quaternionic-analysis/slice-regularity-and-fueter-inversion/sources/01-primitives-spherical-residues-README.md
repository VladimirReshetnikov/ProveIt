# Global Fueter Primitives and Spherical Residues

**A two-period obstruction theory, critical-growth classification, and exact energy asymptotics**

Research manuscript, 21 September 2026. The PDF has 25 pages.

## Contents

- `global_fueter_primitives.tex`: complete, standalone LaTeX source, with bibliography.
- `global_fueter_primitives.pdf`: compiled article with linked contents and references.
- `verify_results.py`: symbolic and numerical checks (not a formal proof checker).
- `verification_output.txt`: output from the successful verification run.
- `README.md`: this guide.

The original user-supplied `quaternionic_analysis.tex` was not modified and is
not required to compile or understand the new article.

## Principal results

Theorem 3.1 gives a necessary-and-sufficient two-period criterion for a
single-valued slice-regular Fueter primitive. Theorem 3.2 identifies the full
affine monodromy. Theorem 4.4 constructs an explicit split cokernel with eight
real dimensions per planar hole.

Theorem 7.1 constructs a holomorphic second-derivative invariant directly from
the target function. Proposition 8.5 proves the reality constraint on its
Laurent coefficients: at an isolated nonreal puncture, the coefficient of
(z-p)^(-2) alone encodes the two quaternionic periods. A simple isolated pole
of this invariant cannot occur.

Theorem 8.3 classifies all axial monogenic singularities of order at most the
reciprocal distance to a conjugacy sphere. Theorems 9.2 and 9.4 give the exact
leading supremum and logarithmic L2-energy coefficient. For residue pair
(a,b) at S_p = s + t*S, the energy coefficient is

    8 * (|s*a+b|^2 + t^2*|a|^2).

Theorem 10.3 gives a global finite spherical principal-part decomposition;
Corollary 10.4 gives exact moment conditions for faster decay at infinity.
The manuscript also proves continuous inverse estimates and quantitative
lower bounds against approximation by global Fueter images.

## Scope and novelty

These results concern axial left Cauchy--Fueter-regular targets and
single-valued slice-regular primitives induced by holomorphic stems.
The Fueter operator is the ordinary four-dimensional Laplacian, with no
additional normalization factor.

Local inverse Fueter theory, the affine kernel, and the special spherical
Cauchy kernels are established background and are explicitly credited.
The proposed contributions are the global obstruction and quantitative
classification package identified in Section 12. No claim is made that a
named published open conjecture has been settled. The stated novelty is
qualified: equivalent results were not located in the primary sources
inspected, but this does not establish bibliographic priority. All asserted
mathematical results have proofs in the article; it has not undergone
external peer review or proof-assistant verification.

## Build the article

A standard TeX Live installation with pdfLaTeX, latexmk, newtx, amsmath,
mathtools, geometry, microtype, booktabs, tabularx, xcolor, enumitem, etoolbox,
fancyhdr, hyperref, and bookmark is sufficient. No external graphics, fonts,
BibTeX database, or shell escape are required.

    latexmk -pdf -interaction=nonstopmode -halt-on-error global_fueter_primitives.tex

Alternatively, run `pdflatex global_fueter_primitives.tex` repeatedly until
cross-references and the table of contents stabilize (normally three runs).

## Run the checks

The script requires Python 3.10 or later, NumPy, and SymPy.

    python -m pip install numpy sympy
    python verify_results.py

The recorded run used Python 3.13.5, NumPy 2.3.5, and SymPy 1.14.0.
It checks the Vekua equations, the target-derived holomorphic invariant,
period normalization, local-stem versus branch-free evaluation, Laurent
admissibility and residue recovery, spherical norms, energy constants,
and the leading exterior moment. All recorded checks passed.

Floating-point contour and asymptotic tests are sanity checks only. The
analytical proofs do not depend on the numerical tests or their tolerances.

## PDF quality checks

The final source compiled without LaTeX warnings, undefined references,
overfull boxes, or underfull boxes. All 25 pages were rendered and inspected;
text bounding boxes remain within the physical page. No original source
manuscript or third-party papers are bundled in this archive.
