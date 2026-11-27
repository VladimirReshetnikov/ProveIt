# Dirichlet Li kernels

Two research papers prepared on 27 November 2026. Both use the Dirichlet zero-line theorem at the pinned revision below. Each proof can be read independently.

## Papers

- **li-kernel.pdf** (10 pages). Small-time laws for the Dirichlet Li heat kernel. Theorem 1.1 gives the main statements. Section 3 proves the minimal representation count. Section 4 proves the sharp almost-everywhere approximation and density laws. Section 5 gives the exact Hausdorff spectrum. Section 6 computes two neighboring two-jump centers for zeta.
- **single-time.pdf** (4 pages). Which observation times determine a circle jump measure? Theorem 1.1 classifies all determining times for integral jump measures with the specified drift. Theorem 1.2 proves that every positive observation time determines all primitive factors of a Dirichlet product. The observation is the full probability distribution on the circle at that time, equivalently its frequency-labelled Fourier coefficients.

## Reproduction

The two editable sources are li-kernel.tex and single-time.tex. Keep spectrum.pdf alongside li-kernel.tex. Standard TeX Live suffices. From the extracted directory run

    pdflatex -halt-on-error li-kernel.tex
    pdflatex -halt-on-error li-kernel.tex
    pdflatex -halt-on-error single-time.tex
    pdflatex -halt-on-error single-time.tex

The two exact arithmetic checks require only Python 3 with assertions enabled.

    python3 check_zeta_angles.py
    python3 gauss-check.py

Their recorded outputs are zeta-check.txt and gauss-check.txt. The zeta check starts with padded decimal prefixes from Andrew Odlyzko's tabulation and uses rational enclosures for arctangents. The Gauss check uses integer polynomial arithmetic for selected discriminants. These examples illustrate the general proofs in the papers. The figure is a plot of the proved dimension formula. To regenerate it from its editable source, use Python 3 with NumPy and Matplotlib and run

    python3 plot-spectrum.py

## Provenance and verification

- [Vendored theorem statements](https://github.com/VladimirReshetnikov/ProveIt/blob/b6253012cf30c80a989c871906e097a27f23a27c/Analysis/GeneralizedRiemannHypothesis/vendor/grh-lean/grh/src/Statements.lean)
- [Vendored exported theorems](https://github.com/VladimirReshetnikov/ProveIt/blob/b6253012cf30c80a989c871906e097a27f23a27c/Analysis/GeneralizedRiemannHypothesis/vendor/grh-lean/grh/src/Main.lean)
- [Article section on Li coefficients](https://github.com/VladimirReshetnikov/ProveIt/blob/b6253012cf30c80a989c871906e097a27f23a27c/Analysis/GeneralizedRiemannHypothesis/Article/sections/li.tex)
- [Article section on recovery](https://github.com/VladimirReshetnikov/ProveIt/blob/b6253012cf30c80a989c871906e097a27f23a27c/Analysis/GeneralizedRiemannHypothesis/Article/sections/rec.tex)

The ProveIt commit is b6253012cf30c80a989c871906e097a27f23a27c. The vendored grh subtree and the upstream readable edition at commit 72fead102f663d5c7a407964a13dc0cf9d977207 have the same Git tree ID, 2e133df63d7f4da6b3059c4195324f8e9187ba73. The upstream package pins Lean 4.35.0 and Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679. Its README reports the proof checkers and axioms. The new results are mathematical proofs in LaTeX. A fresh kernel replay of the upstream package and a Lean formalization of these two papers were outside the verification performed for this archive.
