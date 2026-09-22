# Surreal Scalars and Black-Hole Singularities

**What replacing R and C can accomplish, what it cannot accomplish by itself,
and a rigorous research program**

Research assessment prepared for Vladimir Reshetnikov, 21 September 2026.

## Contents

- `surreal_physics.pdf`: the 31-page article, including 23 bibliographic entries.
- `surreal_physics.tex`: self-contained LaTeX source with an internal bibliography.
- `verify_examples.py`: a runnable SymPy program checking 37 finite identities.
- `verification_results.txt`: output from the actual successful verification run.
- `requirements.txt`: the tested Python dependency version.
- `build.sh`: convenience script for compiling the article.

## Main assessment

Surreal and surcomplex numbers are promising as exact asymptotic coefficient
languages. They are not a drop-in replacement for the analytic infrastructure
of real spacetime or complex Hilbert spaces. Merely representing a divergent
classical observable as an infinite field element does not establish a regular
metric, geodesic completeness, unique evolution, or a physical measurement rule.
The article develops constructive alternatives instead of treating this as a
reason to reject all non-Archimedean models.

The main worked examples are Schwarzschild curvature and proper-time infall,
radial tidal Jacobi fields, the small-angular-momentum crossover, a regular-core
metric, regular reduction of formal Einstein equations, finite Hermitian quantum
algebra, and the beyond-all-orders ambiguity of a factorial asymptotic series.

## Rebuild the PDF

A standard TeX Live installation with the packages listed in the source is
sufficient. No external bibliography database, illustrations, or font files
are required.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error surreal_physics.tex
```

Or run `sh build.sh`. The fallback in that script runs `pdflatex` three times
so cross-references and the table of contents settle.

The supplied PDF was compiled with pdfTeX 1.40.26 (TeX Live 2025/Debian).
All references resolved. The final build has no overfull-box warnings; one
minor underfull-box diagnostic does not affect legibility. The rendered PDF
was inspected, including mathematical pages, tables, and the contents.

## Run the symbolic checks

```sh
python -m pip install -r requirements.txt
python verify_examples.py
```

The recorded run used Python 3.13.5 and SymPy 1.14.0 and passed all 37 checks.
Python 3.10 or newer is the intended interface; only the recorded environment
was actually tested.

The checks include a full coordinate Riemann-tensor contraction, not just a
substitution into an assumed curvature formula. They also cover the Ricci
components, horizon determinant, radial and nonradial balances, Jacobi
solutions, the exact crossover integrand factor, central curvature and density
limits, regulator reparameterization, and finite ODE truncation residuals.

## Verification boundaries

This is not a claim of a new experimentally validated physical theory.
The symbolic program does not constitute a proof of general analytic theorems,
a construction of the full surreal field, or a simulation across a physical
singularity. The propositions in the article have mathematical proofs in the
text but were not checked in Lean. No claim of priority is made for the
propositions or benchmark calculations.

Repository evidence is pinned to commit
`39f2be6667ade51bca2b45daa47e289d69c09764` of
`VladimirReshetnikov/Surreal`. Inspection covered the tree and the root,
documentation-catalog, and surcomplex-analysis READMEs. The repository was not
built or fully audited, and no files were changed in it. Pinned links and the
scope of the published mathematical and physical sources are in the article.

The package contains original assessment text and verification code, not
redistributed copies of the cited papers or the repository.
