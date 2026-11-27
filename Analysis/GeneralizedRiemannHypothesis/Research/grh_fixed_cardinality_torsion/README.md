# Fixed-cardinality torsion specialization

Research archive, 27 November 2026.

## Main results

* The exact zero-tolerance selector for at most n polynomials has least guaranteed order exponent H_n(B) satisfying log_p iterated n-1 times of H_n(B) = p^(h0-1) B + O(log(2+B)), with a matching lower bound up to an additive constant. The case n=1 is exact.
* Exact finite optimization over colored torsion root multisets, for any nonnegative tolerance. Fixed-cardinality selection stabilizes at zero tolerance.
* Dimension-free extension to integral power series and a prime-conductor realization using Dirichlet GRH.

The local results are unconditional; the prime-conductor corollary uses the supplied Dirichlet GRH and the standard Bach--Sorenson least-prime theorem. The paper gives complete mathematical proofs, not a machine-checked Lean proof. The source Lean package was inspected, not rebuilt. Novelty is relative to the inspected source and focused literature search; priority is not certified. In particular, the asymptotic at fixed positive tolerance and a closed finite formula for all cardinalities remain open.

## Files

- `paper.tex`: complete LaTeX manuscript with references and further research questions.
- `paper.pdf`: compiled 12-page manuscript.
- `packet_exact.py`: standard-library Python implementation of the exact finite-state recurrence, with independent small-instance capacity and cost checks. Supply a prime p. This is deliberately exhaustive and is only practical at small shell sizes.
- `verification.txt`: output of the reproducible exact checks (27 capacity checks and 16 packet instances).
- `SHA256SUMS`: checksums of the above files and this README.

## Reproduce

```sh
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
python3 packet_exact.py --verify
python3 packet_exact.py --p 2 --h0 1 --H 3 --n 2 --delta 1/4
sha256sum -c SHA256SUMS
```

## Repository evidence

Inspected through GitHub: `Analysis/GeneralizedRiemannHypothesis/vendor/grh-lean` (vendored upstream commit `72fead102f663d5c7a407964a13dc0cf9d977207`) and `Analysis/GeneralizedRiemannHypothesis/Article` on main. The paper lists the exact blob hashes for the central source files and identifies the article's open problem `cost:q:cardinality`. The new results are not represented as having been merged into ProveIt.
