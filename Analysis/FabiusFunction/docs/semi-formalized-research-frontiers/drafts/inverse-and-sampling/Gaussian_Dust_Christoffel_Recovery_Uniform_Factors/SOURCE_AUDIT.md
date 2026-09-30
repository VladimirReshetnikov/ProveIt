# Source audit and nonduplication boundary

## Repository scope

Repository: `VladimirReshetnikov/ProveIt`.
Pinned commit: `458ccfb80b9940220819091da107e82bb970dcca`.
Research date: 29 September 2026.

Live GitHub tools were used to inspect the repository root, recursive tree,
selected directory listings, and the following relevant material. This was a
focused audit, not a complete reading of all ProveIt mathematical sources.

Let BASE be:
`Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/`.

| Source relative to BASE | Inspected content | Role |
|---|---|---|
| `inverse-and-sampling/README.md` | Lines 1–165 | Maps current reports and marks archival reports unreviewed |
| `inverse-and-sampling/Sharp_Stability_Strata_Fabius_Rvachev_Deconvolution/README.md` | Full | Fixed-capacity baseline and explicit infinite-rank limitation |
| `inverse-and-sampling/Sharp_Stability_Strata_Fabius_Rvachev_Deconvolution/article.tex` | Source lines 780–1080 | Translation Taylor estimates and finite-cluster cancellation; not imported as unproved assumptions |
| `inverse-and-sampling/Gaussian_Confounding_Sharp_Recovery_Uniform_Factors/README.md` | Full | Fixed-capacity unknown-Gaussian experiment and rates |
| `inverse-and-sampling/Recovering_Uniform_Factors_Fabius_Rvachev/README.md` | Full | Existing infinite-spectrum instability and attribution to Billey–Swanson |
| `representations/Fabius_Rvachev_New_Frontiers-2/CORPUS_AUDIT.md` | Source lines 1–130 | Existing Christoffel reconstruction of the physical up-density |

An exploratory search also inspected an automata reversal-coloring report;
that topic was not selected because significant related results were already
present. Later default-branch code search returned a newer commit; all source
claims used in the article were tied back to the pinned commit above.

## External primary sources

1. Sara C. Billey and Joshua P. Swanson, *The metric space of limit laws for
   q-hook formulas*, arXiv:2010.12701v2. The abstract and HTML full text were
   inspected, particularly the generalized uniform and DUSTPAN sections,
   Theorems 1.15 and 3.13, and Corollaries 3.28–3.29.
   https://arxiv.org/abs/2010.12701v2
2. Edouard Pauwels, Mihai Putinar, and Jean-Bernard Lasserre, *Data analysis
   from empirical moments and the Christoffel function*, arXiv:1810.08480v2.
   The HTML full text, especially Section 2.2, was inspected for the classical
   variational and moment-matrix formulas.
   https://arxiv.org/abs/1810.08480v2
3. NIST DLMF Section 4.19, especially 4.19.7, for the logarithmic sine series.
   https://dlmf.nist.gov/4.19
4. NIST DLMF Section 18.27, including little q-Jacobi orthogonality, for the
   classical geometric-measure context. No new q-polynomial family is claimed.
   https://dlmf.nist.gov/18.27
5. Gerth, Hofmann, Hofmann, Kindermann, *The Hausdorff Moment Problem in the
   light of ill-posedness of type I*, arXiv:2104.06029. Abstract/bibliographic
   information inspected; cited only as contextual literature, not as a
   theorem dependency for this model.
   https://arxiv.org/abs/2104.06029

No third-party papers are redistributed. The bibliography is embedded in the
LaTeX source. The article's theorem proofs are self-contained apart from named
standard foundational facts such as polynomial approximation, the elementary
probability convergence theorems, and Dini's theorem.

## What is inherited

- Square-summable generalized uniform sums, their cumulants, their entire
  characteristic functions, and exact spectrum identification.
- The DUSTPAN compactification and its bounded-energy parameter topology.
- Christoffel minimization and Schur-complement/inverse-moment-matrix formulas.
- Cauchy determinants and geometric orthogonality measures.
- ProveIt's finite-capacity stability and Gaussian-confounding questions.
- ProveIt's existing physical up-density Christoffel reconstruction, which is
  distinct from the factor-spectrum measure used here.

## What is developed here

The explicit smoothed statistical problem is treated using
`rho = 3s delta_0 + sum_j a_j^2 delta_(a_j^2)`. The main developed conclusions
are exact global and local finite-sample minimax risks; the compact-class
uniform-consistency equivalence; finite-cumulant certificates and their tail
bounds; a rank-free L1 expansion with explicit constants; the exact geometric
specialization; bounded-coefficient noise control; and constructive statistical
upper rates and pointwise consistency. The general Christoffel and closure
mechanisms themselves are expressly credited.

No exhaustive search of the worldwide literature was performed. Consequently
these are proposed research contributions relative to the inspected sources,
not certified claims of publication priority or resolution of an unrelated
named conjecture. No existing repository proof is assumed merely because its
file is present. No automated proof assistant was run.
