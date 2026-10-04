COMPLEX TRANSSERIES REVERSION
Geometry, Exact Convergence, Quartic Criticality, and Sharp Borel Bounds
Research report, 4 October 2026

START HERE
==========
Read complex_transseries_reversion.pdf.
The matching LaTeX source is complex_transseries_reversion.tex.
All files needed to compile the article are included in this archive.

SCOPE AND RESULTS
=================
The article develops precise extensions of the transseries-inversion
material in VladimirReshetnikov/ProveIt. The comparison is pinned to
commit 8e9cd6f00e0ac79c4425ff6abdfa64b497cf3f41.

It contains:
* A necessary and sufficient strict-cone criterion for proper finite
  complex action maps, with a separate finite-fiber criterion.
* A direction-independent completed action algebra and a proof that
  noncollinear actions nevertheless produce dense sorting walls.
* Finite angular atlases with error bounds and an exact totient count
  for the actions 1 and i.
* An exact two-action absolute-convergence domain, a balanced quartic
  N^(-5/4) degree law, a 4/3 logarithmic boundary law, and a uniform
  angle/amplitude crossover including its first correction.
* A sharp Bessel majorant and optimal universal inverse half-planes,
  refining an estimate already present in the repository.
* Uniform off-axis inverse bounds for a two-sine Borel kernel, plus
  filtered continuation via the Kamimoto-Sauzin implicit theorem.
* Exact Stokes transport, a logarithmic-core example, twelve research
  questions, and three proposed near-term projects.

All original mathematical assertions are accompanied by arguments.
Imported closure results and existing repository formulas are credited.
Historical priority has not been established, and no unrestricted
closure theorem for all complex transseries is claimed. The code is
verification support, not proof-assistant formalization or interval
arithmetic.

BUILD
=====
Use a reasonably complete TeX Live or MiKTeX installation. With latexmk:

    latexmk -pdf -interaction=nonstopmode -halt-on-error complex_transseries_reversion.tex

Alternatively run pdflatex three times on the same file to resolve
cross-references and the table of contents. The included Makefile has:

    make pdf
    make verify
    make clean

The bibliography is in the main TeX source; BibTeX is not required.
Included PDF figures and generated TeX tables make Python unnecessary
for compiling the article.

REPRODUCE THE CHECKS AND FIGURES
==============================
The scripts were tested with Python 3.12.14, mpmath 1.3.0, NumPy 2.3.5,
and Matplotlib 3.10.8. See requirements.txt and verification/README.txt.

    python verification/verification.py
    python verification/quartic_saddle_checks.py

The first script also accepts --no-figures.
It checks exact Gaussian-rational inverse coefficients through total
degree 10, exact wall counts and Catalan identities, and high-precision
inverse truncation errors. The second checks the quartic and ordinary
saddle constants and the leading uniform crossover at finite degrees.

The scripts overwrite their own generated JSON, TeX table, and figure
outputs. Rerun LaTeX afterward to incorporate regenerated files.

CONTENTS
========
complex_transseries_reversion.tex   Main source, including bibliography
complex_transseries_reversion.pdf   Compiled article
figures/                           Three PDF figures and PNG previews
verification/                      Scripts, results, tables, and notes
requirements.txt                   Tested Python dependency versions
Makefile                           Build and verification commands
MANIFEST.sha256                    SHA-256 checksums of included files

The appendix records the repository comparison and its limitations.
External repository sources and third-party papers are linked rather
than bundled. No remote repository changes are part of this deliverable.

