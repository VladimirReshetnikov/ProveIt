# Maximum principal nullity and squarefree prime products

Two research papers prepared on 26 November 2026. Each PDF has a complete standalone LaTeX source of the same name.

- **principal_nullity.pdf** answers the typical-size question for the maximum kernel dimension of the principal submatrices of a uniform binary dot-product orthogonal matrix. The paper proves concentration on two adjacent integers, single-value concentration away from squares, an asymptotic with the exact constant for rare exceedances near the threshold, and the large-deviation rate for every feasible linear fraction.
- **prime_products.pdf** proves equidistribution of products of exactly k distinct primes, uniformly after arbitrary deletion of a proportion below one half by any fixed margin. It also proves a sharp threshold for individual characters of order at least d. Its analytic input is the verified Dirichlet GRH, through a published uniform estimate for character sums over primes.

## Provenance

The matrix question comes from [Vaas's post](https://math.stackexchange.com/questions/5119604/principal-submatrices-of-random-binary-orthogonal-matrices) and the [earlier ProveIt bound](https://github.com/VladimirReshetnikov/ProveIt/blob/02dbe7d5754f1e0b6879185e60302813738de756/Analysis/GeneralizedRiemannHypothesis/Research/grh_method_transfers_orthogonal_jets_2026-11-26/sections/binary.tex). The main paper describes how the matrix question sits in the catalog of 61 research packets. The archive's two papers are ordinary mathematical proofs. The exact computations below check finite identities and examples.

The shorter Lean development is pinned at [72fead10](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/Main.lean). Its independent builds and statement comparisons are documented in [Sutherland's verification record](https://math.mit.edu/~drew/shortgrh/). We inspected the upstream source and that record. Verification of the new results here consists of the written proofs and accompanying finite checks.

## Reproduce

From this directory, with Python 3.10 or later and a standard full TeX Live installation:

```sh
python3 checks/check_matrices.py
python3 checks/check_prime_products.py
pdflatex -halt-on-error principal_nullity.tex
pdflatex -halt-on-error principal_nullity.tex
pdflatex -halt-on-error prime_products.tex
pdflatex -halt-on-error prime_products.tex
```

The scripts use the Python standard library. Their expected outputs are in `checks/check_matrices_output.txt` and `checks/prime_products.txt`. Run Python with assertions enabled. The papers include separate further research questions and linked bibliographies. The file `SHA256SUMS` records hashes of the distributed sources, PDFs, programs, recorded outputs, and this README.
