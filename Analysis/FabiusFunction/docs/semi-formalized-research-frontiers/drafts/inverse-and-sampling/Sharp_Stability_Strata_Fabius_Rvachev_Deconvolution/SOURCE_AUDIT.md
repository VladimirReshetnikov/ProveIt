# Source scope and provenance

## Repository

Repository: https://github.com/VladimirReshetnikov/ProveIt

The recursive Git tree response used for the pinned source comparison identified
commit `0e0368b216b302d5822890b48bd19f2337af4d04`.

The following principal sources were read at that pinned commit:

1. `Analysis/FabiusFunction/Lean/FabiusFunction/GeneralizedRvachevIdentifiability.lean`
   - Blob SHA returned by the file read:
     `f209b00d6f89e6d1d731fa713dd5fd2a8cdf5872`.
   - The module establishes recovery of admissible dyadic natural exponent
     sequences from analytic zero orders and injectivity of the entire product.
   - It is not a total-variation stability theorem for arbitrary real scales.
   - The file was read; its Lean dependencies were not built in this session.

2. `Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/spectra-and-arithmetic/fabius_holonomic_frontiers_report/fabius_holonomic_frontiers.tex`
   - Report title: *Holonomic Rank, Exact Overlaps, and Non-P-Recursiveness in the
     Fabius–Rvachev System*, dated 30 August 2026.
   - Relevant inputs: the finite uniform convolution model and the up
     normalization as the sum of 2^{-j} U_j for j >= 1.
   - Its unrelated holonomic claims are not assumptions of the present article.

Additional discovery reads included the root README, the Fabius README, the
Fabius documentation directory, the draft manifest, and the information-geometry
report `fabius_information_frontier.tex`. Those default-branch reads were used
for topic selection and context, not to establish a synchronized full-tree audit.

Targeted code searches included `identifiability` with `sinc`, `dilation
multiset`, and combinations of `multiset`, `cumulants`, `recovery`, and `stability`.
Some code-index responses identified the different tree
`6a354f52f6e146f654a2c21b5ef6880bc0de02a4`. No assertion about its ancestry relative
to the pinned tree is required here. Known principal files were fetched at the
pinned tree rather than inferred from an index hit.

This is a selected-source and claim-oriented comparison. It is NOT an exhaustive
search of all repository reports, all branches, all previous generated articles,
or the entire mathematical literature. A missing search result is not treated
as proof that a theorem has never appeared elsewhere.

## External primary sources

Bibliographic records and abstracts were checked online during preparation:

- Juan Arias de Reyna, *An infinitely differentiable function with compact
  support: Definition and properties*, arXiv:1702.05442 (2017), translation of
  the 1982 paper in Rev. Real Acad. Ciencias Madrid 76, 21–38.
  https://arxiv.org/abs/1702.05442

- Dmitry Batenkov and Yosef Yomdin, *Geometry and Singularities of the Prony
  mapping*, Journal of Singularities 10 (2014), 1–25.
  DOI: 10.5427/jsing.2014.10a.
  https://journalofsingularities.org/volume10/article1.html

- R. Schätzle, *On the perturbation of the zeros of complex polynomials*,
  IMA Journal of Numerical Analysis 20(2) (2000), 185–202.
  DOI: 10.1093/imanum/20.2.185.
  https://academic.oup.com/imajna/article-abstract/20/2/185/868093

These sources supply historical context and attribution. No uninspected
full-paper theorem with a hidden hypothesis is needed for the main arguments:
the article gives its own root-matching, cluster-factor, cumulant, smoothness,
and sharpness proofs, using standard elementary algebra and analysis.

## Priority and claim boundary

The main claim is the proved optimal stability classification for the stated
finite-capacity, known-smooth-background model. Classical moment and Vieta
reconstruction are not presented as new. The article does not claim to settle
an explicitly named published open conjecture, to establish worldwide priority,
or to supply independent peer review or machine-checked verification.

The generalization to infinite unknown capacity, sharp statistical lower bounds,
and weaker smoothing remain separate research questions. No repository files
were written or changed.
