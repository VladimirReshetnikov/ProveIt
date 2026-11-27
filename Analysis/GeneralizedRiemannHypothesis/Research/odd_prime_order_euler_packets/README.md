# Sharp local agreement for products of odd-prime-order Dirichlet L-functions

Research note, 27 November 2026. This packet addresses the open question in the merged ProveIt Article (`rec:sec:open`, pooled zero statistics) concerning odd-prime-order Euler-factor matching densities.

## Contents

- `paper.tex` and `paper.pdf`: complete written proofs and scope of the result.
- `verify.py`: self-contained Python 3 finite-field checks, including an exhaustive certificate for the rank-two order-seven five-factor exception. It also illustrates two cubic-character examples with actual primes. No external dependencies.
- `verification.txt`: output of the successful run.
- `sources.md`: pinned repository source files and dependency/verification status.
- `formalization.md`: a suggested Lean formalization route, not a claimed checked Lean development.
- `SHA256SUMS`: integrity hashes.

## Reproduce

Run `python3 verify.py` from this directory (Python 3.10+). Compile the manuscript with `pdflatex -halt-on-error paper.tex` three times, or `latexmk -pdf paper.tex`. Standard LaTeX packages are used.

## Status

The exact finite-field density theorems are unconditional, including the exceptional value 24/49 at order seven and rank two, whose exclusion certificate was run. The prime-window and weighted error-correction bounds use the vendored Dirichlet GRH theorem as stated. The upstream Lean development was inspected at its public interfaces and reduction files, not rebuilt or independently kernel checked here. The new proof is a written proof. The literature search was targeted, not exhaustive; the contribution is new relative to the reviewed article, with worldwide priority provisional. The entire odd-prime-order spectrum is still open in this note. No changes were made to the user's repository.
