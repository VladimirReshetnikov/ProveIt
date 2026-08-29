Fabius Integral and Transform Calculus Report: archived second-wave companion
=============================================================================

Files
-----
../../Integration_and_Transform_Frontiers.tex
    Current consolidated LaTeX source containing this companion's report.

../../Integration_and_Transform_Frontiers.pdf
    Current compiled consolidated volume.

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

SHA256SUMS.txt
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

The numerical program requires Python 3, NumPy, and SciPy. The original
standalone source and PDF were removed after consolidation; use the two
relative paths listed above for the maintained report and compiled volume.

Editorial note (2026-08-28)
---------------------------
The standalone report source and PDF were removed from this directory after
their content was merged into the consolidated volume. Their historical
SHA-256 hashes remain in the volume provenance section, and Git history
archives the files. This directory retains the audit, data, and script record.
