BEYOND THE DYADIC FABIUS WEB
============================

This package accompanies the research report:

  Beyond the Dyadic Fabius Web:
  A geometric q-Fabius--Rvachev family, endpoint laws, zero arithmetic,
  Bernoulli--Bell polynomial calculus, and phase-aware extrapolation

The report is now displayed as Part XIII (absorbed report X) of
../../Frontier_Compilations.tex; this directory retains only its supporting
assets.

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

Supporting-asset contents
-------------------------
  numerical_experiments.py          Deterministic, commented experiments
  q_family_densities.pdf            Generated figure
  q_family_densities.png            Rasterized figure used by the consolidated PDF
  standardized_cumulants.pdf        Generated figure
  standardized_cumulants.png        Rasterized figure used by the consolidated PDF
  endpoint_bound_residuals.pdf      Generated figure
  endpoint_bound_residuals.png      Rasterized figure used by the consolidated PDF
  phase_aware_extrapolation.pdf     Generated figure
  phase_aware_extrapolation.png     Rasterized figure used by the consolidated PDF
  numerical_summary.csv             Machine-readable diagnostics
  experiment_output.txt             Human-readable diagnostics
  corpus_inventory.txt              Complete 57-file TeX corpus ledger
  requirements.txt                  Python dependencies
  SHA256SUMS.txt                     Checksums for retained supporting files

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
From this asset directory, move to the consolidated-volume directory and run
the repository-required three passes:

  cd ../..
  pdflatex -interaction=nonstopmode -halt-on-error Frontier_Compilations.tex
  pdflatex -interaction=nonstopmode -halt-on-error Frontier_Compilations.tex
  pdflatex -interaction=nonstopmode -halt-on-error Frontier_Compilations.tex
  rm -f *.aux *.log *.out *.toc

The canonical source/PDF pair is ../../Frontier_Compilations.{tex,pdf}.

Quality-control record
----------------------
Before consolidation, the standalone PDF was compiled with pdfTeX/latexmk,
checked for unresolved references, opened with PyMuPDF, and rendered
page-by-page at 180 dpi. All 30 pages were visually reviewed; no clipping,
overlap, or broken glyph was found.
