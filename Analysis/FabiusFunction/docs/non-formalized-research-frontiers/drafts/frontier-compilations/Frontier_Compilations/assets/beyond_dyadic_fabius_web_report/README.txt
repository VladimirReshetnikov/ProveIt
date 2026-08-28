BEYOND THE DYADIC FABIUS WEB
============================

Current consolidation status
----------------------------
This retained companion directory preserves the auxiliary files for source
report X (rendered Part X) of the consolidated Frontier_Compilations volume.
The former standalone manuscript now appears in
../../Frontier_Compilations.tex and its rendered PDF in
../../Frontier_Compilations.pdf.  Those volume files are referenced rather
than duplicated here.  Other paths below are relative to this companion
directory unless stated otherwise.

This package accompanies the research report:

  Beyond the Dyadic Fabius Web:
  A geometric q-Fabius--Rvachev family, endpoint laws, zero arithmetic,
  Bernoulli--Bell polynomial calculus, and phase-aware extrapolation

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

Retained companion contents
---------------------------
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
  SHA256SUMS.txt                     Checksums for retained files

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
A recent TeX Live installation is sufficient.  From this retained companion
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
The deleted standalone PDF had 31 pages (the original package guide
incorrectly stated 30).  It was compiled with pdfTeX, checked for
unresolved references, opened with PyMuPDF, and rendered page-by-page at 180
dpi; all pages were visually reviewed for clipping, overlap, and broken glyphs.
The consolidated PDF is built and inspected at the volume level.
