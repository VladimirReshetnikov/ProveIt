# Sharp support constants for positive filters of Riemann and Dirichlet beta zeros

27 November 2026 — research packet for ProveIt.

## Contents

- `paper.tex` — complete self-contained LaTeX research note, with the main proofs, source comparison and further research questions.
- `paper.pdf` — compiled paper.
- `examples.py` — optional floating-point experiments for positive symmetric atomic measures, including a double-jet example and a mixed zeta/beta example.
- `examples.json` — actual outputs of `examples.py`, including approximate input ordinates, weights and independent high-precision residual evaluations. These are illustrations, not rigorous certificates.
- `source_audit.md` — repository files inspected and their blob identifiers; precise scope of source assumptions.

## Rebuild

Run `pdflatex -interaction=nonstopmode -halt-on-error paper.tex` twice. All references are internal LaTeX bibliography entries; no BibTeX required. To repeat the optional examples: `python -m pip install numpy scipy mpmath`, then `python examples.py`.

## Main theorem

For fixed nonnegative integers r,s with r+s>0, the minimum half-width of a positive probability measure canceling every nonzero ordinate through height B of the zeta and beta zero divisors, with multiplicities r and s added, is `(r+s)/2 * log B + O(log log B)`, using the vendored RH/Dirichlet GRH statements as mathematical input. The leading coefficient is sharp. The compactification proof is unconditional for real Fourier zeros, and works for arbitrary Fourier jets of positive kernels with double-exponential tails.

The new proof is classical and not Lean-verified. No rebuild of the vendored Lean package was performed. Literature priority is not established. The proof does not rely on numerical computations. No repository files were changed.
