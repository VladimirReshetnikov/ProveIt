# Source audit and contribution boundary

## Repository pin and retrieval scope

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned commit used for the comparison:
`11e1e900114e7c0cfdcd19fe346ddb4f2852dbc5`.

Repository material was read through the GitHub connector. Search-index hits at
other commits were used for discovery, not identified with the pinned tree.
The top-level repository map and the relevant Fabius/inverse-research subtree
were inspected. This was a focused comparison, not an exhaustive audit of all
research files in the repository.

### Principal predecessor

`Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/inverse-and-sampling/Gaussian_Confounding_Sharp_Recovery_Uniform_Factors/`

The complete pinned README and the returned opening sections of `article.tex`
were inspected. The large source response was truncated; no claim is made to
have read the entire predecessor proof through that response. The complete
README establishes the comparison used here: global known/unknown-variance
rates, the global shifted-moment inequality, detection rates, model hypotheses,
and the prior report's conventional-proof status.

Pinned README:
https://github.com/VladimirReshetnikov/ProveIt/blob/11e1e900114e7c0cfdcd19fe346ddb4f2852dbc5/Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/inverse-and-sampling/Gaussian_Confounding_Sharp_Recovery_Uniform_Factors/README.md

### Flat-boundary companion

`Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/inverse-and-sampling/Flat_Boundaries_Sharp_Recovery_Uniform_Factors/`

Its complete pinned README was inspected. It states global rates including
zero Gaussian variance for infinite-uniform backgrounds and explicitly lists
mixed collision strata among the remaining questions. Those global results
are credited as prior work. This article settles the mixed-stratum
classification under positive Gaussian smoothing; it does not claim to settle
the unsmoothed mixed-stratum problem.

Pinned README:
https://github.com/VladimirReshetnikov/ProveIt/blob/11e1e900114e7c0cfdcd19fe346ddb4f2852dbc5/Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/inverse-and-sampling/Flat_Boundaries_Sharp_Recovery_Uniform_Factors/README.md

The prior reports themselves cite earlier snapshots. Those are their own
historical baselines and are not the pin used for this article.

## Primary literature checked

The following primary arXiv records were checked for titles, authors, dates,
and the background claims actually used in the introduction. This is not a
claim to have independently audited all proofs in those papers. No deep
mixture-model theorem is imported to prove the present convolution-model rates.

1. Dmitry Batenkov and Yosef Yomdin, *Geometry and Singularities of the Prony
   mapping*, arXiv:1301.1336 (2013).
   https://arxiv.org/abs/1301.1336
   Role: classical collision geometry, Prony/Vieta/hyperbolic polynomial context.

2. Philippe Heinrich and Jonas Kahn, *Optimal rates for finite mixture
   estimation*, arXiv:1507.04313 (2015).
   https://arxiv.org/abs/1507.04313
   Role: distinction between local-uniform minimax and nonuniform pointwise rates.

3. Yihong Wu and Pengkun Yang, *Optimal estimation of Gaussian mixtures via
   denoised method of moments*, arXiv:1807.07237 (2018), version 2 (2019).
   https://arxiv.org/abs/1807.07237
   Role: feasible moment fitting, adaptive moment comparisons, unknown variance
   in a different statistical model.

4. Juan Arias de Reyna, *An infinitely differentiable function with compact
   support: Definition and properties*, arXiv:1702.05442 (2017).
   https://arxiv.org/abs/1702.05442
   English translation of the 1982 paper in Rev. Real Acad. Ciencias Madrid
   76, 21–38. Role: Fabius/up-function probability background. The cumulant
   formula for the explicitly defined random series is derived in the article.

## Contribution boundary

The contribution developed here is the mixed-stratum blockwise classification,
its sharp localized moment inequalities and missing-first-sum certificate,
the adaptive fitting argument, and analytic/asymptotically normal variance
recovery at positive collisions. Exact hard paths and weighted likelihood
expansions provide self-contained lower bounds in the stated model.

The all-zero rates reproduce the predecessor and are not claimed as new.
The methods use classical cumulants, symmetric polynomials, elementary ODE
existence, Gaussian differentiation, dominated convergence, the delta method,
and two-point testing. The search was focused and cannot establish worldwide
publication priority. No repository files were modified.
