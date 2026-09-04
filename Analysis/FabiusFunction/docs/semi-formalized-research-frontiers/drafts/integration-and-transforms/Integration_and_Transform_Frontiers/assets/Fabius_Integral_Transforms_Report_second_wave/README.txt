Fabius Integral and Transform Calculus Report: archived second-wave companion
=============================================================================

Consolidated report
-------------------
../../Integration_and_Transform_Frontiers.tex
    Canonical consolidated source; this report is Part XII.

../../Integration_and_Transform_Frontiers.pdf
    Compiled consolidated volume.

Retained companion files
------------------------

fabius_integral_transforms.py
    Commented deterministic numerical checks.

numerical_results.txt
    Output produced by the Python program with a 2^17 grid.

corpus_manifest.txt
    Complete 87-path recursive TeX manifest for the pinned Git tree.

requirements.txt
    Exact NumPy and SciPy versions used for the numerical checks.

PDF_VALIDATION.txt
    Historical preflight, render, reference, and numerical reproducibility
    checks for the removed standalone PDF.

SHA256SUMS.txt (retired repository-wide on 2026-09-01; historical bytes are
available from Git history only)
    SHA-256 checksums for the retained files and the consolidated source/PDF.

Corpus snapshot
---------------
The theorem comparison was pinned to ProveIt commit:
a6555a64671b54f851563a04a391bb7845bd6571

The audit covered *.tex under Analysis/FabiusFunction/docs recursively.
The pinned Git-tree enumeration contained 87 paths; duplicate bundles,
archived variants, generated TeX fragments, and external-paper transcriptions
were grouped by content lineage for theorem-level comparison.

Reproduction
------------
python -m pip install -r requirements.txt
python fabius_integral_transforms.py --grid-power 17

The numerical program requires Python 3, NumPy, and SciPy.  Rebuild the
consolidated PDF from the volume directory with exactly three explicit
`pdflatex -interaction=nonstopmode -halt-on-error
Integration_and_Transform_Frontiers.tex` passes.

> **Editorial note (2026-08-28):** the standalone report source and PDF were
> removed after their content was merged into Part XII.  Git history and the
> consolidated provenance section preserve the absorbed snapshot; this
> directory is an ancillary asset bundle, not an independent build root.
