# Dirichlet zeros from prime sums

Two research papers, with standalone LaTeX sources and exact finite checks. Both use the ProveIt snapshot c0f2782360ddffd79a20c6d828d582e214a2b8c3. The upstream readable Lean edition is pinned at 72fead102f663d5c7a407964a13dc0cf9d977207.

## Papers

- **coalescence.pdf** (12 pages) proves a criterion for density-one simplicity from the variance of a three-point prime sum. Section 2 proves the Tauberian converse for arbitrary unequal gaps. Section 3 reconstructs pairwise multiplicity moments and proves the identity-class criterion. Sections 4 and 5 establish the dyadic simplicity criterion and sharpen the upper factor to 1.3208. Section 6 proves the full residue-class covariance rates, the cyclotomic simplicity criterion, and its unconditional characterization including the critical-line assertion. Section 7 gives a five-point contrast that loses information for abstract positive measures.
- **carriers.pdf** (4 pages) gives one explicit real positive prime weight whose ordinary autocorrelation determines all signed and labelled Dirichlet zero multiplicities. It includes the deterministic main term and prime-square correction, a prefix precision bound, and a bounded-height inversion. Measurements are limiting Fourier coefficients. Their finite observation horizon is open.

The analytic input is the critical-line assertion for Dirichlet L-functions as exported by the vendored Main.lean. The new arguments are classical mathematical proofs. The authors of the upstream package describe their own verification in its README. The archive does not contain a newly checked Lean formalization.

## Reproduce

From the extracted archive, run the following commands on a system with standard TeX Live packages and Python 3.8 or newer.

    cd papers
    pdflatex -halt-on-error coalescence.tex
    pdflatex -halt-on-error coalescence.tex
    pdflatex -halt-on-error carriers.tex
    pdflatex -halt-on-error carriers.tex
    cd ..
    python3 checks/check_contrasts.py
    python3 checks/check_carriers.py

The scripts check spline constants, finite character-transform identities, noisy digit decoding, and recovery of synthetic signed divisors with forced collisions. Their recorded outputs are included. They do not assume or numerically test the density-one simplicity conjecture.

## Source locations

- [Readable Lean entry point](https://github.com/VladimirReshetnikov/ProveIt/blob/c0f2782360ddffd79a20c6d828d582e214a2b8c3/Analysis/GeneralizedRiemannHypothesis/vendor/grh-lean/grh/src/Main.lean)
- [Cubic coalescence, explicit formula, and open questions](https://github.com/VladimirReshetnikov/ProveIt/blob/c0f2782360ddffd79a20c6d828d582e214a2b8c3/Analysis/GeneralizedRiemannHypothesis/Article/sections/zer.tex)
- [Universal zero reconstruction and the positive-weight question](https://github.com/VladimirReshetnikov/ProveIt/blob/c0f2782360ddffd79a20c6d828d582e214a2b8c3/Analysis/GeneralizedRiemannHypothesis/Article/sections/rec.tex)
