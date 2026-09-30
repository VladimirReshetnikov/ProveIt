# Source provenance

Date of research and repository access: 29 September 2026.

## Pinned repository

Repository: https://github.com/VladimirReshetnikov/ProveIt

Commit inspected:

    0c973d8f5e7ef4550f4df1bf486d890037fd9f14

The GitHub connector was used to read repository content. The main directly
inspected sources were:

1. `Analysis/Transseries/docs/series-and-transseries/README.md`
   https://github.com/VladimirReshetnikov/ProveIt/blob/0c973d8f5e7ef4550f4df1bf486d890037fd9f14/Analysis/Transseries/docs/series-and-transseries/README.md

2. `Analysis/Transseries/docs/series-and-transseries/Negative_Ray_Summation_Exponential_Feedback/article.tex`
   https://github.com/VladimirReshetnikov/ProveIt/blob/0c973d8f5e7ef4550f4df1bf486d890037fd9f14/Analysis/Transseries/docs/series-and-transseries/Negative_Ray_Summation_Exponential_Feedback/article.tex

The second source's subsection "Angular summability of the quadratic model"
occurs in the retrieved source range 1330--1410. It explicitly asks whether
an open arc containing pi can support the exponential Borel-growth bounds
required for angular summability. The present article supplies a negative
answer for the quadratic unit-amplitude model and an extension to rational
amplitudes with eventually quadratic slopes.

Other inspected passages describe the definition of fine summability,
Lagrange exponential blocks, their signed coefficient measures, the Bessel
representation, and the article's stated limitations. The source review was
focused and was not a claim-by-claim audit of the repository's large volumes.
The repository index says the recent research packages are unmerged and not
formalized; those caveats are preserved.

The regularity classification article is cited contextually as described
in the index and negative-ray article. Its sharp coefficient asymptotics
are not a proof dependency. No formalization status is inferred from its
presence in a repository containing Lean code.

## Primary literature checked

- David Sauzin, *Introduction to 1-summability and resurgence*,
  arXiv:1405.0356 (2014).
  https://arxiv.org/abs/1405.0356
  Fine versus angular summability and nonlinear stability; Theorem 17.3
  supplies the standard inversion-closure result used to transfer the
  angular obstruction from Q to U. The theorem was read in the primary PDF.

- D. A. Lutz, M. Miyake, R. Schaefke, *On the Borel summability of divergent
  solutions of the heat equation*, Nagoya Mathematical Journal 154 (1999),
  1--29. DOI: 10.1017/S0027763000025289.
  https://doi.org/10.1017/S0027763000025289
  Publisher metadata and abstract checked. Classical context, not an
  unproved dependency substituted for the article's heat-rigidity proof.

- Slawomir Michalik and Bozena Podhajecka, *The Stokes phenomenon for certain
  partial differential equations with meromorphic initial data*,
  arXiv:1603.04209 (2016).
  https://arxiv.org/abs/1603.04209
  Primary abstract checked for the meromorphic heat-data context.

- L. Han, Y. Li, D. Sauzin, S. Sun, *Resurgence and Partial Theta Series*,
  arXiv:2112.15223v3 (2022).
  https://arxiv.org/html/2112.15223v3
  Primary text checked for periodic quadratic phases, rational boundary
  points, rational generating data, discrete Fourier transforms, and the
  distinction between Borel continuation and growth.

- Ira M. Gessel, *Lagrange inversion*, Journal of Combinatorial Theory,
  Series A 144 (2016), 212--249; arXiv:1609.05988.
  https://arxiv.org/abs/1609.05988
  https://doi.org/10.1016/j.jcta.2016.06.018
  Primary preprint and publisher metadata checked.

## Attribution boundary

The Lagrange-block construction is credited to the negative-ray research
article in its general form. Classical summability, heat, and partial-theta
techniques are credited to the primary literature. The present draft's
proposed contribution is the analytic-curve noncancellation argument applied
to a nonlinear implicit inverse, the resulting natural boundary and angular
obstruction, and the rational-amplitude dichotomy. No exhaustive publication
priority search or independent peer review is claimed.

Only newly written source, the resulting PDF, and newly written verification
artifacts are included in this package. No third-party paper PDFs, repository
source copies, or font files are redistributed.
