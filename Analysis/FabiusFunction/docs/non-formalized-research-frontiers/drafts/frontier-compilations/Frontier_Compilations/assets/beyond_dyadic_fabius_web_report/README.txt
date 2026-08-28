BEYOND THE DYADIC FABIUS WEB
============================

This package accompanies the research report:

  Beyond the Dyadic Fabius Web:
  A geometric q-Fabius--Rvachev family, endpoint laws, zero arithmetic,
  Bernoulli--Bell polynomial calculus, and phase-aware extrapolation

This directory is an archived companion bundle preserving the computations,
data, and figures that accompanied the formerly standalone report.  The report
now appears in the consolidated volume: its source is
../../Frontier_Compilations.tex and its rendered PDF is
../../Frontier_Compilations.pdf.

Repository corpus
-----------------
The comparison corpus is every *.tex file under
Analysis/FabiusFunction/docs in the ProveIt repository, recursively, at
commit 24da985eba70e46d862acdaddd476793a428213e (57 files).  The exact
path ledger is corpus_inventory.txt.

Scope of novelty
----------------
The word "new" in the report is corpus-relative: the stated results were
not found in the inspected repository snapshot.  No claim of global
mathematical priority is made.  Proved statements, conjectures, and open
problems are labeled separately.

Archived companion contents
----------------------------
  ../../Frontier_Compilations.tex    Consolidated volume source
  ../../Frontier_Compilations.pdf    Rendered consolidated volume
  numerical_experiments.py          Deterministic, commented experiments
  q_family_densities.pdf            Generated figure
  standardized_cumulants.pdf        Generated figure
  endpoint_bound_residuals.pdf      Generated figure
  phase_aware_extrapolation.pdf     Generated figure
  numerical_summary.csv             Machine-readable diagnostics
  experiment_output.txt             Human-readable diagnostics
  corpus_inventory.txt              Complete 57-file TeX corpus ledger
  requirements.txt                  Python dependencies
  SHA256SUMS.txt                     Checksums for package files

Reproducing the numerical outputs
---------------------------------
From this directory, with Python 3.10 or later:

  python -m pip install -r requirements.txt
  python numerical_experiments.py

The program uses no Monte Carlo simulation.  It deterministically solves
the distributional fixed-point equation, checks exact cumulant formulas,
evaluates rigorous endpoint bounds, tests phase-aware extrapolation, and
verifies reciprocal-integer Fourier-zero multiplicities.

Compiling the consolidated report
---------------------------------
A recent TeX Live installation is sufficient.  From this archived companion
directory, run exactly three serial pdflatex passes:

  cd ../..
  pdflatex -interaction=nonstopmode -halt-on-error Frontier_Compilations.tex
  pdflatex -interaction=nonstopmode -halt-on-error Frontier_Compilations.tex
  pdflatex -interaction=nonstopmode -halt-on-error Frontier_Compilations.tex

These commands rebuild ../../Frontier_Compilations.pdf.  The source uses
Libertinus when available and falls back to Latin Modern.  The archived figure
PDFs remain beside the numerical script that regenerates them.

Quality-control record
----------------------
Before consolidation, the standalone PDF was compiled with pdfTeX, checked
for unresolved references, opened with PyMuPDF, and rendered page-by-page at
180 dpi.  All 30 pages were visually reviewed; no clipping, overlap, or broken
glyph was found.
