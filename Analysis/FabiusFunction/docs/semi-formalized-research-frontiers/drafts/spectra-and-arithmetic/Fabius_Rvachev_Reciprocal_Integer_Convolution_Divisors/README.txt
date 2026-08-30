Reciprocal-Integer Convolution Divisors of the Rvachev Law
===========================================================

Files
-----
frontier_report.tex   Complete LaTeX source.
frontier_report.pdf   Compiled report.
experiments.py        Reproducible exact/numerical experiments.
figures/              Figures included in the report.
data/                 CSV and text outputs from the experiments.

Reproduce numerical outputs
---------------------------
From this directory, run:

    python experiments.py --output-dir .

Requirements: Python 3.10+, NumPy, Matplotlib, and mpmath.
The script performs exact integer checks before terminating successfully.

Compile the report
------------------
Run exactly three strict serial passes:

    pdflatex -interaction=nonstopmode -halt-on-error -file-line-error frontier_report.tex
    pdflatex -interaction=nonstopmode -halt-on-error -file-line-error frontier_report.tex
    pdflatex -interaction=nonstopmode -halt-on-error -file-line-error frontier_report.tex

Then remove frontier_report.aux, frontier_report.log, frontier_report.out, and
frontier_report.toc.  The source uses the repository's canonical A4/Libertinus
preamble and embeds the PNG figures from figures/.  The committed report was
compiled and visually inspected from all 34 rendered PDF pages.  All 25 fonts
are embedded and subset, the prose faces are Libertinus, and no Type 3 font is
present.

Research status
---------------
Results labeled theorem/proposition/lemma/corollary are proved in the report.
Conjectures are explicitly labeled.  "New" means not found in the audited repository
snapshot or limited literature search; it is not a claim of mathematical priority.
