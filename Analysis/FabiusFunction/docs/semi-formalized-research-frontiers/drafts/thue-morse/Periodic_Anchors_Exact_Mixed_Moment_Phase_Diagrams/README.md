# Periodic Anchors and Exact Mixed-Moment Phase Diagrams

Research article prepared for Vladimir Reshetnikov, 30 September 2026.

## Main contents

The 21-page article develops an exactly solvable class of mixed digital
products whose anchor phases form complete periodic orbits under x -> bx mod 1.
It proves an exact pressure formula and equilibrium-measure classification,
a global mixed-moment exponent for a squared shifted background, pure-product
leading asymptotics and critical windows, an exact seventh-root moment with
period-three leading amplitudes, a finite polyhedral pressure realization
theorem, and a nonlinear expanding-map extension. Eight further research
questions and a formalization roadmap are included.

The principal results concern this structured orbit-balanced class. The article
does not claim to solve arbitrary mixed phase tuples or the general single-phase
regularity problem. It does not rely on unreviewed pressure theorems from ProveIt.

## Files

- `article.pdf`: compiled article, 21 pages.
- `article.tex`: self-contained LaTeX source with inline bibliography.
- `figures/phase_diagram.pdf`: exact three-branch phase diagram.
- `figures/periodic_amplitude.pdf`: exact seventh-root residue-class amplitudes.
- `verify.py`: exact algebraic checks and separate numerical diagnostics.
- `verification_results.json`: reproducible numerical and exact-check output.
- `verification_run.txt`: console output from the executed checks.
- `requirements.txt`: Python dependencies for reproducing checks and figures.
- `environment.txt`: versions used for this build.

## Build the article

Run from this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively, run `pdflatex article.tex` three times. No BibTeX or external
bibliography download is needed. The figure PDFs are already included; Python
is not needed to build the article. A standard TeX Live installation needs the
Libertinus, AMS, geometry, microtype, booktabs, graphicx, fancyhdr, titlesec,
enumitem, xurl, aliascnt, hyperref, and cleveref packages. No shell escape is used.

## Run verification

Use Python 3.10 or newer:

```sh
python -m pip install -r requirements.txt
python verify.py --out verification_results.json
```

To regenerate the figures as well:

```sh
python verify.py --figures --out verification_results.json
```

Run `latexmk` again after regenerating figures to update the PDF. The exact
polynomial operations use Python integers in Z[eta], eta^2 + eta + 2 = 0.
The script verifies the finite norm tables and the seventh-root moment by exact
polynomial division for depths n=0,...,12 (largest N=4096). It also checks
coboundary identities and performs floating-point moment and critical-window
diagnostics. All exact assertions and numerical identity checks passed in the
recorded run.

The all-depth theorem follows from the proof in the article, not from a finite
list of computations. Numerical quadrature is not interval arithmetic; finite
moment estimates do not certify the limiting exponent, prefactor, or a spectrum.
At the triple point the finite-depth effective exponent converges noticeably
more slowly; the article explicitly records this rather than hiding the row.

## Provenance and status

Inspected ProveIt commit:

781594d886f8dc56069221e2b56bd1e94d9c6e5f

Relevant research index:

Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/thue-morse/README.md

The article distinguishes its derivations from prior single-phase pressure
work and from broader published pressure-flexibility results. It is an
unrefereed research draft with ordinary mathematical proofs, not a Lean
formalization. Worldwide priority has not been independently established.
The package makes no changes to the repository.
