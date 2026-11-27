# Identifying Dirichlet characters from a short window of zeros

Read **local_euler_recovery.pdf** for the theorem statements, proofs, source analysis, numerical example and further questions. **local_euler_recovery.tex** is the complete editable manuscript.

## What is proved

- **Theorem 1** identifies a product of at most d primitive Dirichlet L-functions of conductors at most Q from one unlabeled multiset of high zero ordinates. The factor count and multiplicities are recovered. The radius is bounded by an absolute constant times d² log²(2Q) log(2d), plus a collar of size (1/π) log log log(QT) + O(1). The height condition is in the theorem. This application uses Dirichlet GRH.
- **Theorem 2** estimates a single Euler coefficient at p with absolute error O(2⁻ᵐ) using a radius of 16pm plus the collar. With full complex zero locations the proof is unconditional. The displayed formula uses an even-parity gamma integral which is independent of the unknown character.
- **Corollary 6** gives a lower bound for the number of unmatched occurrences and the total displacement of matched ordinates when two distinct primitive characters are compared.

The proof does not evaluate numerical values for the absolute constants in the general identification theorem. The collar gives a sufficient window radius. Optimality remains open.

## Reproducibility

Compile in this folder with a standard TeX Live installation.

    pdflatex -halt-on-error local_euler_recovery.tex
    pdflatex -halt-on-error local_euler_recovery.tex

The numerical diagnostic requires Python 3, NumPy and SciPy.

    OPENBLAS_NUM_THREADS=1 python3 numerical/local_readout.py

The program regenerates the zeros and checks its counts by an independent numerical argument-principle calculation. It runs all twelve individual readings and an identification among 20 pooled product candidates. The recorded run is in **numerical/output.txt**. **numerical/README.md** documents the numerical methods and the scope of the checks. The arguments in the manuscript establish the general analytic conclusions. The new results have not been formalized in Lean.

## Source revisions and closest research notes

The upstream theorem is in lsernau/grh-lean at commit 72fead102f663d5c7a407964a13dc0cf9d977207, grh/src/Main.lean. The comparison with ProveIt uses commit e5a86180eeea85173073bedb1d5edef3c5e6855c, principally Analysis/GeneralizedRiemannHypothesis/Article/sections/zer.tex. Permanent web links appear in the bibliography. The upstream verification is attributed to its published checkers.

Three earlier project notes are identified below to make their scope and provenance traceable.

| Archive | Locations consulted | Relation to the present theorem |
| --- | --- | --- |
| prime_pole_windows.zip | prime_pole_windows.tex, Theorem 2, “Local independence of zero multiplicities” section | Fixed-group extraction from weighted observations and full-strip rank on radii with coefficient strictly greater than 1/π. |
| dirichlet_prime_frequency_inverse.zip | prime_frequency.tex, Theorems 1, 2 and 5 and the local distinction corollary | Fixed-prime Gaussian readout, differential-operator recovery, and local comparisons on a double-logarithmic scale. |
| quadratic_spectra.zip | quadratic_spectra.tex, Theorems 3.1 and 3.3 and Corollary 3.2 | Quadratic characters recovered from a central cutoff and a global matching-displacement estimate. |

The new manuscript treats translated windows, arbitrary orders, conductors and primes varying together, and unlabeled products. The literature comparison supports a scoped novelty claim. Historical priority has not been independently certified.
