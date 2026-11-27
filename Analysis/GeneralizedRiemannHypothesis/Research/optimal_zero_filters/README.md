# Shortest robust positive filters for Dirichlet zeros

Research packet, 27 November 2026.

- `paper.tex`: self-contained mathematical manuscript (11 pages).
- `paper.pdf`: compiled manuscript.
- `verify.py`: optional high-precision numerical illustrations (Python 3 + mpmath).
- `results.json`: output of the supplied script.

Rebuild: `pdflatex -interaction=nonstopmode -halt-on-error paper.tex` three times, or until references stabilize. Reproduce the numerical illustrations: `python -m pip install mpmath` and `python verify.py > results.json`.

Main mathematical result: the unique shortest positive filter for an arbitrary sufficiently small perturbation of a strictly positive mirror-band configuration has exactly n+1 atoms and analytic locations and weights. Its width differential at the base is `dD = -(h^2/pi) sum_j m_j d gamma_j`. The exact mirror criterion, finite-order pair formulas, and stability estimates are proved in the manuscript.

Status: the extremal results are unconditional mathematical proofs; the application to the critical-line zero contributions uses the Dirichlet GRH proposition exported by the vendored Lean development. We inspected the source and did not run a complete Lean replay. The new proof is not formalized. The numerical examples are not interval-certified and do not establish global optimality beyond the theorem's neighborhood. Prior-art research was focused, not exhaustive; two-mode low-order formulas have antecedents in engineering. The main novelty candidates are the analytic continuation theorem for general mixed complex spectra and its differential, not the familiar two-mode examples. No repository files were changed.
