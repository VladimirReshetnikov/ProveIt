Fabius Integral and Transform Calculus Report
=============================================

Files
-----
Fabius_Integral_Transforms_Report.tex
    Main LaTeX source.

Fabius_Integral_Transforms_Report.pdf
    Compiled PDF.

fabius_integral_transforms.py
    Commented deterministic numerical checks.

numerical_results.txt
    Output produced by the Python program with a 2^17 grid.

corpus_manifest.txt
    Complete 87-path recursive TeX manifest for the pinned Git tree.

requirements.txt
    Exact NumPy and SciPy versions used for the numerical checks.

PDF_VALIDATION.txt
    PDF preflight, render, reference, and numerical reproducibility checks.

SHA256SUMS.txt
    SHA-256 checksums for every deliverable file in this directory.

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

The PDF was compiled with the LaTeX source in this directory.  The numerical
program requires Python 3, NumPy, and SciPy.

> **Editorial note (2026-08-28):** the report source (.tex) and compiled PDF listed above were removed from this directory after their content was merged into the volume `Integration_and_Transform_Frontiers.tex`; their SHA-256 hashes remain in the volume provenance section, and git history archives the files. This directory keeps only figures, data, and scripts.
