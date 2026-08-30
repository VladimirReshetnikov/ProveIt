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
Run twice (or use latexmk):

    latexmk -pdf -interaction=nonstopmode frontier_report.tex

The source uses only standard TeX Live packages and embeds the PNG figures from
figures/.  The report was compiled and visually inspected from rendered PDF pages.

Research status
---------------
Results labeled theorem/proposition/lemma/corollary are proved in the report.
Conjectures are explicitly labeled.  "New" means not found in the audited repository
snapshot or limited literature search; it is not a claim of mathematical priority.
