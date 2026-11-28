# Sharp torsion selection across nonunit power patterns

Research note for ProveIt, 27 November 2026.

## Contents

- `torsion_power_patterns.tex` — complete standalone LaTeX manuscript, with theorems, proofs, source links and limitations.
- `torsion_power_patterns.pdf` — compiled manuscript.
- `check_patterns.py` — exact finite-word and torsion-node covering checks, including the eight-state dual certificate for E = {0,1,3}.
- `checks.txt` — recorded output of that script.
- `check_small_grid.py` — exact cyclotomic field arithmetic and finite kernel certification of a two-dimensional example.
- `grid_checks.txt` — recorded output of that script.
- `Makefile` — reproduction commands.
- `SHA256SUMS` — integrity hashes for the files above and this README.

## Reproduction

The manuscript uses a standard TeX Live installation (pdfLaTeX, AMS packages, Latin Modern, geometry, microtype, hyperref, enumitem, booktabs, xcolor). Run `make pdf` or run `pdflatex -interaction=nonstopmode -halt-on-error torsion_power_patterns.tex` three times. The bibliography is self-contained; no BibTeX or network access is required.

The two check scripts use Python 3 and its standard library only. Run `make check` to recompute the two output files, or run each script directly. The computations are exact, except for purely illustrative decimal renderings of rational bounds in the first script. Verify the archived bytes before rebuilding with `sha256sum -c SHA256SUMS`.

## Status and scope

The manuscript addresses the explicit question `tors:q:powers` of [the merged article's torsion section](https://github.com/VladimirReshetnikov/ProveIt/blob/main/Analysis/GeneralizedRiemannHypothesis/Article/sections/tors.tex), extending the selection mechanism of [the vendored RootsOfUnity.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/main/Analysis/GeneralizedRiemannHypothesis/vendor/grh-lean/grh/src/New/Congruences/Selmer/RootsOfUnity.lean). It provides exact one-variable obstruction costs, an exact finite reduction in all dimensions, and a sharp dimension-uniform leading asymptotic for pure p-power patterns. The proofs are unconditional; they neither use nor reverify the reported RH/Dirichlet GRH theorem. The main general asymptotic is proved analytically, not inferred from computational tests. The exact small-grid example uses finite arithmetic certification. No Lean formalization of these new theorems is supplied, no global priority claim is made, and the exact mixed-level multivariate problem and quantitative Selmer valuation control remain open. No prominent external conjecture is claimed resolved.
