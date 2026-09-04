> **Absorbed into the consolidated volume.**
> This directory is the preserved verification package of a report that is now
> **Part IV** of `geometric_q_fabius_frontiers.tex`, two levels up. The
> report's own `.tex` and `.pdf` were deleted when it was merged; git history
> is the archive, and the volume's Provenance section pins the absorbed
> snapshot by SHA-256. The scripts, data, and figures here are still live —
> the volume includes them from `assets/rvachev_fourier_frontier_report/`. Any build or path
> instruction below describes the original standalone package and no longer
> resolves as written.

Fourier Images of Recursive Piecewise-Polynomial Approximations
================================================================

Contents
--------
rvachev_piecewise_fourier_frontier.tex
    Full LaTeX source of the research report.

rvachev_piecewise_fourier_frontier.pdf
    Compiled PDF report.

rvachev_fourier_experiments.py
    Fully commented symbolic/numerical experiment script.  It uses exact
    rational arithmetic for coefficients and moments, plus arbitrary-precision
    mpmath evaluation for infinite products and quadrature.

numerical_output/
    Reproducible figures, exact coefficient table, and a text summary.

Reproduce numerical output
--------------------------
python rvachev_fourier_experiments.py --out-dir numerical_output

Compile the report
------------------
pdflatex rvachev_piecewise_fourier_frontier.tex
pdflatex rvachev_piecewise_fourier_frontier.tex

Python dependencies
-------------------
mpmath, sympy, numpy, matplotlib

Research status
---------------
Results called theorems are supplied with proofs.  Conjectures are explicitly
labeled.  Novelty claims are relative to the reviewed ProveIt repository as of
2026-08-28 and are not claims of exhaustive priority over all literature.

> **Editorial note (2026-08-28):** the report source and compiled PDF listed above (and, where listed, the supplied source scan/OCR) were removed from this directory after their content was merged into the volume `Exponents_and_q_Series_Frontiers.tex`; their SHA-256 hashes remain in the volume provenance list, and Git history archives the files. This directory keeps only figures, data, and scripts.
