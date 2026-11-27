# Inverse spectral rigidity for Dirichlet L-functions

Research note dated 2026-11-27. The new result is a proof of tail divisor rigidity and uniform finite-window error correction for a labelled Dirichlet L-function coupling. It takes the vendored Dirichlet GRH theorem as input, with no new unproved hypotheses beyond that theorem. Novelty is a research claim subject to literature verification; no priority certification or Lean kernel replay is claimed.

## Contents
- `research.tex`: complete human-readable proof, source analysis, examples and bibliography.
- `research.pdf`: compiled LaTeX article.
- `SOURCE_AUDIT.md`: retrieved source identifiers, proof dependencies, audit instructions and formalization roadmap.
- `verify.py`: exact finite algebra/character checks plus high-precision numerical interpolation example.
- `checks.txt`: output of the executed verification script.
- `SHA256SUMS`: integrity hashes.

## Reproduction
Compile twice with `pdflatex -interaction=nonstopmode -halt-on-error research.tex`. Run `python verify.py` with Python 3, SymPy and mpmath installed. The exact checks enumerate 729 signed/zero-edge matrices and compare principal-minor profiles to switching signatures. The numerical interpolation uses 100 decimal digits and is illustrative, not certified interval arithmetic. None of the infinite theorems relies on these numerical checks.

The finite observation height is existential, not computed. The theorem handles errors in exact zero multisets rather than approximate coordinates, assumes distinct primitive nonprincipal characters of one parity, and reconstructs Hermitian couplings only up to equality of all principal minors. Real symmetric matrices have precisely the switching ambiguity and labelled nonnegative weighted graph Laplacians are determined exactly.
