# Nearest-pole simplification of the theta-lift proof

Start with `nearest_pole_theta.pdf`. The paper gives a mathematical replacement for `IsPolar.landau` using a finite-disk pole argument and local Taylor positivity. It preserves the original arithmetic estimate and all five conclusions. It also gives a weaker sufficient twist-selection interface; no improved prime density estimate is claimed.

Files:
- `nearest_pole_theta.tex`, `nearest_pole_theta.pdf`: complete report and compiled PDF.
- `LEAN_PLAN.md`: staged, uncompiled Lean implementation specification.
- `check_nearest_pole.py`, `checks.txt`: exact finite algebraic regressions and recorded outputs.
- `source_anchors.tsv`, `proposal_audit.tsv`, `verify_sources.py`: pinned source/proposal provenance and local Git comparison script.

Rebuild: `latexmk -pdf -halt-on-error nearest_pole_theta.tex`. Run tests: `python3 check_nearest_pole.py`.

The source snapshot is ProveIt commit `ef7d441dcb37ea944b7ac15731bb766f2e1354ea`. The ten proposal READMEs and their mathematical TeX sections were inspected through the GitHub connector. The source audit is targeted, not a complete proof audit. The independent verification record (https://math.mit.edu/~drew/shortgrh/) applies to upstream commit `72fead102f663d5c7a407964a13dc0cf9d977207`; comparison of recursive Git trees found that 802 of 803 Lean source blobs match the current snapshot, with `New/Determinant/Chain/TriangleNorms.lean` differing. The analytic endpoint sources match. The local verification script requires a checkout and was not run here. The exact Python tests were run, LaTeX compiled and the PDF rendered. No Lean compiler or cache was available. No integrated Lean proof, benchmark, or new verification of the full current repository is claimed. No GitHub files were modified.
