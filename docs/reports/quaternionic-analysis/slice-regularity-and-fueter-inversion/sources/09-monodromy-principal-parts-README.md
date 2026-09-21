# Affine Monodromy and Spherical Principal Parts in Quaternionic Fueter Inversion

Research manuscript, 21 September 2026. The PDF is 20 pages.

## Files

- fueter_monodromy.pdf — the complete article.
- fueter_monodromy.tex — self-contained LaTeX source, including the bibliography.
- verify.py — symbolic and numerical consistency checks.
- verification.txt — output of a successful verification run in the preparation environment.

## Main results

Theorem 3.3: a necessary and sufficient two-period criterion for a global
single-valued Fueter primitive, with an explicit reconstruction formula
and affine monodromy.

Theorems 4.1–4.2: the holomorphic encoding J_g = (-P + r Q_x - iota r P_x)/2,
its range, its kernel, and complex moment formulas for the periods.

Theorem 6.1: a split exact sequence on finite-topology bases, an explicit
finite-rank correction, and a real 8m-dimensional cokernel for m holes.

Theorem 8.2 and Corollary 8.3: extension across the real axis, and a
counterexample to unrestricted same-domain global surjectivity on H
minus a nonreal sphere. The arctangent kernels themselves are known
and are explicitly credited in the article.

Theorems 9.2–9.3: a full Laurent–logarithmic spherical normal form,
contour extraction of all principal coefficients, and a constraint
linking the simple and double poles of the holomorphic encoding.

Theorems 10.2–10.3 and Corollaries 10.4–10.5: a real 8N-dimensional
singular quotient at growth O(rho^(-N)), exact leading norm constants,
sharp o(rho^(-1)) removability, and integer finite singularity orders.

Theorem 11.1: period-preserving rational approximation with a minimal
8m-dimensional real correction space.

## Rebuilding the PDF

Use a TeX installation with the packages listed in the source, notably
newtxtext/newtxmath, amsmath, amsthm, mathtools, microtype, geometry,
fancyhdr, hyperref, and bookmark. Run:

    latexmk -pdf -interaction=nonstopmode -halt-on-error fueter_monodromy.tex

Alternatively run pdflatex on the source three times to stabilize the
contents and cross-references. No external images or bibliography files
are needed. Font files are not included.

## Running the checks

Python 3.9 or newer; SymPy is needed for the symbolic tests:

    python verify.py

The numerical tests alone use only Python's standard library:

    python verify.py --numerical-only

The preparation run used SymPy 1.14.0. All symbolic identities and
numerical checks passed. The numerical period and contour tests had
errors below 2e-11; the actual reported errors were much smaller.
These tests are supplementary checks, not a machine-checked proof of
the complete article.

## Scope and research status

The paper concerns axial left Cauchy–Fueter regular functions and
left slice-regular primitives with right quaternionic coefficients.
The central complex unit iota is not a quaternionic imaginary unit.
Most results are on a connected planar base strictly above the real
axis; Section 8 handles conjugation-invariant domains meeting it.

The classical/local inverse Fueter theorem and the arctangent kernels
are not claimed as new. The explicit global obstruction, holomorphic
encoding and spherical singularity package was not located in the
sources inspected. This is not a certified priority claim. All major
mathematical assertions are accompanied by proofs; no peer review or
formal proof-assistant checking is claimed.

The article builds on, rather than rewrites, the supplied exposition:
quaternionic_analysis(1).tex (20 September 2026).
SHA-256 of that exact supplied source:
c06b089b76d574463ae4a9b7782f509139fa16cd09c9c29373d0a4ad7a511807

The original attachment and copyrighted reference papers are not
redistributed in this archive. Section 13 and the bibliography identify
the source-derived background and the scope of the literature check.
