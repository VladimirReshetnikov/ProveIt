> **Absorbed into the consolidated volume.**
> This directory is the preserved verification package of a report that is now
> **Part VII** of `geometric_q_fabius_frontiers.tex`, two levels up. The
> report's own `.tex` and `.pdf` were deleted when it was merged; git history
> is the archive, and the volume's Provenance section pins the absorbed
> snapshot by SHA-256. The scripts, data, and figures here are still live —
> the volume includes them from `assets/Fabius_Q_Connections_Report/`. Any build or path
> instruction below describes the original standalone package and no longer
> resolves as written.

BEYOND THE DYADIC FABIUS WEB
============================

Contents
--------
- fabius_q_connections_report.pdf : compiled 29-page research report
- fabius_q_connections_report.tex : complete LaTeX source
- q_fabius_experiments.py         : deterministic numerical verification code
- numerics/                       : residual tables, q-Lagrange weights, cumulants
- figures/                        : vector PDF and PNG versions of the report figures

Compilation
-----------
The report was compiled with LuaLaTeX. From this directory, run:

    lualatex fabius_q_connections_report.tex
    lualatex fabius_q_connections_report.tex
    lualatex fabius_q_connections_report.tex

Numerical reproduction
----------------------
Python 3 with NumPy, mpmath, and Matplotlib is required. Run:

    python q_fabius_experiments.py

The program writes its generated tables and figures to its selected output
directory. It contains detailed comments explaining every experiment and the
identities tested.

Status labels used in the report
--------------------------------
The report distinguishes proved theorems, computational observations, and
explicitly labeled conjectures. Claims of novelty are relative to the audited
ProveIt Fabius-function LaTeX corpus and the cited literature, not an assertion
of exhaustive priority across all unpublished work.

> **Editorial note (2026-08-28):** the report source and compiled PDF listed above (and, where listed, the supplied source scan/OCR) were removed from this directory after their content was merged into the volume `Exponents_and_q_Series_Frontiers.tex`; their SHA-256 hashes remain in the volume provenance list, and Git history archives the files. This directory keeps only figures, data, and scripts.
