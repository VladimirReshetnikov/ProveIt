# Source audit and provenance

Inspected October 8, 2026. All mathematical proofs in the article are self-contained.
The sources below supply context and comparison, not unverified proof premises.

## Supplied repository

- Repository: https://github.com/openai/math
- Inspected commit: `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`
- Commit timestamp: `2026-10-08T05:20:00Z`
- README: differing verification levels are explicitly acknowledged by the repository.
- Inspiration: family 097, *The Euclidean Steinitz-Bergstrom theorem* (September 24, 2026).
- Directly inspected source:
  `preprints/The-Euclidean-Steinitz-Bergstrom-theorem-September-24-2026/build/introduction.tex`
- Introduction blob: `a2744e9bdb2d3928a96c6b3b76716755ee58c81b`
- Manuscript README blob: `d0c00dd1f1c7f05bedcee0787eca7e80d60b4e67`

The connection is ordering, cancellation, and simultaneous prefix control. We do
not use the claimed square-root Steinitz theorem or its proof. The optimization
problem and the kernel criterion were developed independently in this package.

## Primary literature consulted

1. Benjamin Recht and Christopher Re (2012), *Toward a Noncommutative
   Arithmetic-geometric Mean Inequality: Conjectures, Case-studies, and Consequences*.
   PMLR 23, 11.1-11.24.
   https://proceedings.mlr.press/v23/recht12.html
   Comparison: noncommutative matrix-product/norm approach to sampling laws.

2. Christopher M. De Sa (2020), *Random Reshuffling is Not Always Better*.
   NeurIPS 33.
   https://proceedings.neurips.cc/paper/2020/hash/42299f06ee419aa5d9d07798b56779e2-Abstract.html
   Comparison: existing counterexamples to blanket superiority; Section 4 also
   studies small-step norm comparisons. These are not the all-state Gram
   Loewner criterion proved here.

3. Zijian Liu (2026), *Random Reshuffling Dominates Stochastic Gradient Descent*.
   arXiv:2606.32005v1; COLT 2026.
   https://arxiv.org/abs/2606.32005
   Key scope check: the footnote on the first page defines domination by the
   order of convergence rates. It does not assert an exact, per-instance,
   all-starting-state ordering of actual objective values.

4. Jackie Lok, Rishi Sonthalia, and Elizaveta Rebrova (2025), *Error Dynamics of
   Mini-batch Gradient Descent with Random Reshuffling for Least Squares Regression*.
   arXiv:2406.03696v2; ALT 2025.
   https://arxiv.org/abs/2406.03696
   Context: discrete matrix dynamics and higher-order step-size effects.
   No theorem from that paper is needed in the present derivation.

## Novelty qualification

The search did not establish historical priority. In particular, it is not enough
to fail to find an exact title match. The full classification, weighted coefficient,
and constructive consequences need an independent equivalence/priority review
before they are advertised as first-in-literature results. General reshuffling
counterexamples and the matrix-product viewpoint are explicitly credited above.
