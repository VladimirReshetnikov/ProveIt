# Sharp growth of integral Gram determinants and generic modular column numbers

Research packet for ProveIt, 27 November 2026.

## Results

* For fixed rank `r >= 2`, the minimum normalized Gram determinant of a generic integral `r x n` matrix is `Theta_r(n^(3r-2))`. Equivalently, the minimum mean squared normalized maximal minor has growth `Theta_r(n^(2r-2))`. This answers the order-of-growth question `src:q:gram` in the merged GRH article.
* For fixed rank `r >= 2`, the maximum number of columns of a generic integral matrix whose largest absolute maximal minor is **exactly** `Delta` is `Theta_r(Delta^(1/(r-1)))`. This supplies an affirmative answer to Kriepke–Kyureghyan–Schymura, Question 3.4 (JCTA 212, 106003, 2025). The construction works for every sufficiently large integer Delta, not just a subsequence. All non-anchor minors have absolute value at most Delta/2.
* The lower Gram bound extends to matrices with controlled hyperplane occupancy and, in particular, to any fixed bound on the number of vanishing maximal minors.

The proofs are unconditional. The connection to the GRH proof is through determinant/index comparisons and integral lattice geometry. Neither the upstream GRH build nor the entire article was reverified. Sharp constants in higher rank and a Lean formalization are not supplied. Global priority has not been established by an exhaustive literature review.

## Contents

- `paper.tex`, `paper.pdf`: complete mathematical argument, definitions, explicit constants, literature comparison, examples.
- `code/verify.py`: exact Python 3 certificate generator and checker; standard library only.
- `data/verification.json`: full integer matrices and certificate data.
- `data/verification.txt`: execution summary.
- `SOURCE_AUDIT.md`: repository locations, provenance, and external literature.
- `PROOF_REVIEW.md`: proof dependencies, key pitfalls addressed, and scope.
- `SHA256SUMS`: checksums for the delivered files.

## Reproduction

From this directory run:

```sh
python3 code/verify.py > data/verification.txt
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
```

The included certificate data pass all checks: 162,973 maximal minors in each of two exact passes, and 17,367 integer points in seven boxes. The anchor examples additionally check every non-anchor minor against the bound Delta/2. The computations illustrate the results; the symbolic proofs do not depend on finite enumeration. The archive is a standalone research note, not a modification of the GitHub repository.
