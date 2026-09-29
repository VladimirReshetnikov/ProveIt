# Source audit and contribution boundary

Date: 29 September 2026.

## Repository snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned tree obtained from the live GitHub tree endpoint:

    c130dba623c420551d90db41dae7b3d9cff72dfd

Principal comparison files at that commit:

1. `Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/inverse-and-sampling/Sharp_Stability_Strata_Fabius_Rvachev_Deconvolution/article.tex`
   - The abstract and introductory/model sections were read (source lines 1–210).
   - The abstract gives the finite-factor total-variation stability classification
     for a known smooth compactly supported background and explicitly excludes
     a statistical minimax lower-bound claim.
   - The manuscript is dated 28 September 2026.
   - Its theorems are not used as an unproved analytic dependency here: the
     shifted-moment and likelihood arguments needed for this article are proved
     independently under this article's own assumptions.

2. `Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/inverse-and-sampling/README.md`
   - Read for neighboring packages and the repository's status descriptions.
   - It lists the finite-factor report as an unreviewed archival intake of
     29 September 2026, with no Lean statement.
   - It also identifies the preceding infinite-factor recovery report and its
     scope. That report's infinite-capacity claims are not reused as new results.

3. `README.md` and `Analysis/FabiusFunction/README.md`
   - Used to navigate the research topics, not as independent mathematical
     validation of every claim elsewhere in the repository.

Focused GitHub code searches looked for convolution recovery, stability,
Gaussian nuisance parameters, and minimax discussion. Search-index results
sometimes identified commit `eaf787d505510dabb63f0e85804855b193e00cfc`, rather
than the pinned live tree. Search hits were discovery aids; their versions
were not silently equated with the pinned files.

This was a focused source comparison, not an exhaustive audit of every
ProveIt report. Absence from these searches is not proof of global novelty.

## Primary literature consulted

- Juan Arias de Reyna, *An infinitely differentiable function with compact
  support: Definition and properties*, arXiv:1702.05442 (2017), the English
  translation of the author's 1982 article.
  https://arxiv.org/abs/1702.05442
  Role: historical up-function background and the probabilistic product model.
  The particular cumulants needed here are also derived in the article.

- Dmitry Batenkov and Yosef Yomdin, *Geometry and Singularities of the Prony
  mapping*, arXiv:1301.1336 (2013).
  https://arxiv.org/abs/1301.1336
  Role: prior moment-inversion, Vandermonde/Vieta, and collision geometry.
  Not a source of the new convolution-model rates.

- Philippe Heinrich and Jonas Kahn, *Optimal rates for finite mixture
  estimation*, arXiv:1507.04313 (2015).
  https://arxiv.org/abs/1507.04313
  Role: prior distinction between local uniform and pointwise rates in mixture
  estimation. Its mixing-distribution model is not this independent-sum model.

- Yihong Wu and Pengkun Yang, *Optimal estimation of Gaussian mixtures via
  denoised method of moments*, arXiv:1807.07237v2 (2019).
  https://arxiv.org/abs/1807.07237v2
  Role: prior feasible moment fitting and known/unknown Gaussian variance in
  finite location mixtures. The main-rate page of the PDF was visually checked
  during source review. Its variable mixing weights and locations differ from
  the equal-multiplicity uniform convolution factors treated here.

These papers are cited for context and attribution. The central bounds in
this article are proved rather than imported with missing hypotheses.

## What the article adds within this comparison

- The sharp consecutive shifted-power-sum inverse exponent for nonnegative
  equal-weight nodes, with a direct sign-counting proof for every integer shift.
- An explicit elementary-symmetric flow conserving p_2 through p_m while
  changing p_1 and p_(m+1).
- A weighted Gaussian likelihood expansion establishing leading chi-square
  and Hellinger constants after exact moment cancellation.
- Matching minimax half-length and Gaussian-variance rates for the stated
  Gaussian-smoothed convolution experiment.
- A separate capacity-independent detection threshold and a uniform factor-count
  impossibility consequence.

Classical cumulant identities, Newton identities, Vandermonde geometry,
Hermite identities, finite-grid fitting principles, and the two-point testing
method are not claimed as new. No assertion of worldwide publication priority,
independent peer review, or Lean/Rocq verification is made.
