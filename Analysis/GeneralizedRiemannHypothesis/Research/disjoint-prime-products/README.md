# When do disjoint products of small primes cover every residue tuple?

Read **prime_products.pdf** for the statements, complete proofs, source analysis, finite examples, and further research questions. The principal results give exact quadratic and cubic support tests above quarter retention, a criterion for pointwise mixing, and sharp-order growth of the number of independently prescribed moduli at every fixed positive retention density.

## Rebuild the paper

From this directory run the following with a standard TeX Live installation.

    pdflatex -halt-on-error prime_products.tex
    pdflatex -halt-on-error prime_products.tex

The main source includes growing.tex and mixed.tex. The bibliography is included in the main source.

## Reproduce the arithmetic and combinatorial checks

The two scripts use the Python standard library. Run from this directory with Python 3.8 or later.

    python3 checks/verify.py
    python3 checks/repair.py

Compare the outputs with checks/results.txt and checks/repair_results.txt. The first script checks binary and ternary allocation criteria and computes joint residue counts. The second verifies the bounded-edit table repair and enumerates a mixed-modulus example. These finite checks supplement the mathematical proofs.

## Source revisions

The source analysis uses ProveIt at b6253012cf30c80a989c871906e097a27f23a27c and the expanded merged article at 3d8689ceae76501a5c50f67da37e85369aac4fb6. The vendored readable grh tree matches upstream lsernau/grh-lean at 72fead102f663d5c7a407964a13dc0cf9d977207. The paper cites immutable source links. The source theorem is used as mathematical input. The new theorems are proved in the paper.
