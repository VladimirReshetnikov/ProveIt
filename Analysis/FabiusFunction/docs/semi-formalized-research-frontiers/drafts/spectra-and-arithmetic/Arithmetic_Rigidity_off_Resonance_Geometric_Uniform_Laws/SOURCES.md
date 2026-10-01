# Sources and scope of review

Article date: 30 September 2026. Repository retrieval and package production
straddled midnight UTC; local article date remains 30 September.

## Repository snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt

HEAD resolved through GitHub's commit endpoint:
`ffddaa8b9c89e7bf027e1442cc6216bb010906d0`

The endpoint reported commit timestamp `2026-09-30T23:38:21Z`.
GitHub search also returned older indexed references at `0a543d5e...`.
Search hits were navigation aids, not evidence that every repository file had
been inspected at the HEAD snapshot. File content was fetched separately.

## Specifically inspected mathematical sources

### 1. Divisibility-ladder predecessor

Path:
`Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/spectra-and-arithmetic/Arithmetic_Convolution_Factors_Fabius_Type_Laws/README.md`

Blob: `a9d4a8ccbdc09a5e5f6e26c718b50dd196461dc7`

Pinned link:
https://github.com/VladimirReshetnikov/ProveIt/blob/ffddaa8b9c89e7bf027e1442cc6216bb010906d0/Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/spectra-and-arithmetic/Arithmetic_Convolution_Factors_Fabius_Type_Laws/README.md

Read: README in full, including its principal results and editorial amendments.
The associated long article was not retrieved in full. Relevant recorded results
include arithmetic divisibility ladders, geometric integer-base targets, and
classification/regularity barriers. Its editorial note credits the subsequent
prime-power simultaneous result and base-six obstruction.

### 2. Simultaneous-divisor predecessor

Path:
`Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/spectra-and-arithmetic/Simultaneous_Convolution_Divisors_Fabius_Type_Laws/README.md`

Blob: `7a1c7890535822f71cea9104e8e9d83edc40f757`

Pinned link:
https://github.com/VladimirReshetnikov/ProveIt/blob/ffddaa8b9c89e7bf027e1442cc6216bb010906d0/Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/spectra-and-arithmetic/Simultaneous_Convolution_Divisors_Fabius_Type_Laws/README.md

Read: README in full, including its theorem summary, normalization, tests,
limitations, and editorial amendments. The article itself was not retrieved
in full. The h=1 prime-power Hall criterion and base-six obstruction are
explicitly treated as prior results. They are independently rederived in the
present manuscript, so correctness does not depend on an unseen proof.

Normalization: that report uses uniforms on [-1,1], whereas the present article
uses [-1/2,1/2]. Its geometric-series variable is twice the present variable.

### 3. Formal dyadic multisection source

Path:
`Analysis/FabiusFunction/Lean/FabiusFunction/GeometricUniformMultisection.lean`

Blob: `c12da6b03a43cdcaa98f90de5aae761e849ec44b`

Pinned link:
https://github.com/VladimirReshetnikov/ProveIt/blob/ffddaa8b9c89e7bf027e1442cc6216bb010906d0/Analysis/FabiusFunction/Lean/FabiusFunction/GeometricUniformMultisection.lean

Read: lines 1-130, including the header's precise fixed-ratio scope and the
measurable/independent coordinate construction. It is a fixed normalized
[0,1]-digit dyadic two-section result, not a formal proof of every multisection
or factorization theorem in the present article. No Lean build was run.

### 4. Fabius project overview

Path: `Analysis/FabiusFunction/README.md`
Blob: `8a19a7c8de8939c4a55ec63fc443ce08d6fe74ce`
Read: lines 1-180. Used for primary-paper identification, development scope,
and normalization awareness. Unread portions and the full documentation census
were not used to make a novelty claim.

The root README and a few other project overviews/search hits were used to choose
the project; unrelated root-level mathematical claims are not dependencies.

## Primary literature

- Juan Arias de Reyna, *An infinitely differentiable function with compact
  support: Definition and properties*, arXiv:1702.05442.
  https://arxiv.org/abs/1702.05442
  Abstract/bibliographic page inspected. Used for context; the product arguments
  needed here are written out in the article.
- Juan Arias de Reyna, *Arithmetic of the Fabius function*, arXiv:1702.06487v3.
  https://arxiv.org/abs/1702.06487
  Abstract/bibliographic page inspected. Context only.
- Paul Erdős, *On a family of symmetric Bernoulli convolutions*, American
  Journal of Mathematics 61 (1939), 974-976.
  https://doi.org/10.2307/2371641
  https://www.jstor.org/stable/2371641
  Publisher landing page accessible but full paper text not retrieved. The
  specific golden-ratio argument is proved in full in the present article;
  no unread passage is used as proof evidence.
- Pablo Shmerkin, *On the exceptional set for absolute continuity of Bernoulli
  convolutions*, Geometric and Functional Analysis 24 (2014), 946-958.
  https://arxiv.org/abs/1303.3992
  Abstract/bibliographic page inspected. The statement about a zero-dimensional
  exceptional parameter set is context only; none of the new proofs imports it.

## Novelty boundary

The rationally separated source theorem, the nonresonant geometric-stream
classification, the h-channel and finite-orbit extensions, and the quantitative
separation/perturbation results were developed here. This is a comparison against
the inspected sources, not a complete literature or repository audit.

Known mechanisms and inherited results are labeled explicitly: integer uniform
refinement, multisection, the h=1 Hall theorem, the composite base-six example,
and the golden-ratio Bernoulli singularity mechanism. No claim is made that the
entire repository's research questions, all resonant cases, or all probability
convolution factors have been classified.

The GitHub repository was not modified. No external papers or font files are
redistributed in this archive.
