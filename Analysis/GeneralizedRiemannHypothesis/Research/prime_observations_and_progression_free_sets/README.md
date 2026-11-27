# Sparse prime observations and progression-free sets

Three research papers · 26 November 2026

## Papers

| File | Main result | Input about zeros |
| --- | --- | --- |
| mellin/mellin.pdf (7 pages) | For every finite Galois extension of the rationals, finite weighted counts of its completely split rational primes at an explicit set of radii recover the entire nontrivial zero multiset of its Dedekind zeta function. The growth exponent of the centered observations is the rightmost zero abscissa. | The inverse theorem holds unconditionally. An exact square-root bound on the observations is equivalent to the critical-line hypothesis for the field. |
| dyadic/dyadic.pdf (5 pages) | For fixed modulus q, one sequence of weighted prime-power sums at the powers of two determines the zero multiplicity for each Dirichlet character at every ordinate. The decoding permits arbitrarily many frequencies in a single class modulo 2π/log 2. | The verified Dirichlet GRH supplies the critical-line expansion. The algebraic and analytic decoding argument then inverts its samples. |
| progressions/progressions.pdf (6 pages) | At each length k ≥ 3, finitely many coupled prime-exponent rules beat the greedy ordinary density while forbidding every positive rational-ratio geometric progression of length k. The gain can be prescribed independently in reduced residue classes. | The existence proof uses the divergent prime reciprocal sum. The residue-class refinement uses classical nonvanishing of Dirichlet L-functions at 1. |

The corresponding .tex file beside each PDF contains its complete proof and bibliography.

## Specific results

- In the splitting-field paper, Theorem 6.1 and Corollary 5.1 give the finite-prime version. At most a constant times log(X) log log(X) sample centres lie below X, and the primes at x can be restricted to [x^(1−δ), x^(1+δ)] for any fixed 0 < δ ≤ 1. Errors of size O(x^α) for any α < 1/2 preserve every zero and multiplicity. The theorem concerns an infinite sequence. The S3 example illustrates the correction to the central residue contributed by prime squares.
- In the dyadic paper, Theorems 1 and 4 give the character-labelled reconstruction and its explicit precision tolerance at each folded Fourier coefficient. The Gaussian factor makes high ordinates costly in absolute precision. No noncoincidence of zeros or arithmetic independence of their ordinates is assumed.
- In the progression paper, Theorem 1 answers the density question after Theorem 3 of Brown and Gordon (1996) for every length. Theorem 3 quantifies the deficit caused by bounding the size of each block of primes, and Theorem 4 localizes the density gain in arithmetic progressions. The proof establishes strict improvement and does not give a sizable numerical increase for the integers.

## Reproduction

With a standard full TeX Live installation, enter a paper directory and run pdfLaTeX twice on the main .tex file, or run latexmk -pdf on that file. Each manuscript builds independently.

The scripts were replayed with Python 3. For the Mellin script install mpmath (tested with 1.3.0). The other scripts use only the standard library. Run from the extracted top-level directory, with assertions enabled.

    python3 mellin/check_mellin.py
    python3 dyadic/check_dyadic.py
    python3 progressions/check_progressions.py

The recorded output is next to each checker (.txt or .json). The Mellin output includes numerical illustrations whose last digits may vary by platform. Its integer checks cover interpolation nodes, coefficient cancellation and permutation characters. The dyadic checker operates exactly in Q(√2) on model spectra with collisions and bounded perturbations. The progression checker tests bounded exponent boxes and finite weight identities. The proofs in the papers establish the infinite statements. Verify the distributed files before rebuilding with:

    sha256sum -c SHA256SUMS

## Sources and comparison

The upstream development at commit 72fead102f663d5c7a407964a13dc0cf9d977207 has five exports, covering the Riemann zeta function and Dirichlet L-functions for positive moduli, including imprimitive characters. The readable proof obtains a one-sided estimate for smoothed prime sums from a comparison of arithmetic lattices, controlled lifts and a determinant, then uses the estimate to exclude zeros. The two analytic papers work with the logarithmic-derivative connection to prime sums. The density paper develops a separate line of research in the ProveIt collection.

- [Formal endpoints](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/Main.lean)
- [Upstream guide](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/GUIDE.md)
- [Independent kernel verifications](https://math.mit.edu/~drew/shortgrh/)
- [Supplied Riemann hypothesis overview](https://en.wikipedia.org/wiki/Riemann_hypothesis)
- [ProveIt collection at the inspected revision](https://github.com/VladimirReshetnikov/ProveIt/blob/2c45d198070f93209d6f0faa2d387ef0a2c4e72c/Analysis/GeneralizedRiemannHypothesis/README.md)
- [Brown and Gordon's density question](https://doi.org/10.1090/S0025-5718-96-00765-X)

The ProveIt index records 61 deposited packets and describes their verification status. Each manuscript identifies the closest mathematical predecessors examined. Further earlier notes on factorial sampling and on bounded multiplicity vectors at a specified zero are discussed in the dyadic paper. The matrix question revisited during this research had already been treated in the earlier paper *The largest principal kernel of a random binary orthogonal matrix*. The three papers here give written proofs and reproducible finite checks. None has a new Lean formalization. We used the independent upstream verification record and did not rerun the upstream kernel build. Publication priority beyond the cited comparisons remains unverified.
