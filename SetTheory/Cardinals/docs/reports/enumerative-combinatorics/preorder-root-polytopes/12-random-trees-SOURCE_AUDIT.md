# Source audit — 30 September 2026

## Repository provenance

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned commit: `b8b0fa2184a044d46ce9ed0f25f88d7bb60fa042`

Main source:
`SetTheory/Cardinals/docs/reports/enumerative-combinatorics/preorder-root-polytopes/article.tex`

Blob: `ba1cc4a6c99abd5ff808aae97df75efe434833e9`

The GitHub connector was used to read repository metadata, the root README,
the report README, and contiguous ranges of the report's TeX source.
The operative pinned ranges are:

* 14560–14710: incidence–apex model, matching-support semantics, hull and
  skeleton definitions, `mts:thm:main` and its dependency explanations.
* 15210–15385: `mts:tab:ADE`, spectral criterion, at-most-four-leaf consequence,
  deterministic diameter bounds, and the distinction between host and skeleton.
* 15900–16200: the explicit question `mts:q:random`, other research boundaries,
  the source's contribution audit and conclusion.

Some initial contextual reads used the then-current `main` branch; the final
mathematical source is pinned to the commit and blob above. No whole-repository
correctness audit was performed, and no remote file was modified.

The report already settles real-rootedness of the stable-neighbourhood size
polynomial (exactly the path hosts), as well as arbitrary-neighbourhood
classification and deterministic enumeration. None is reclaimed as new.

## External primary sources checked

1. Choe, Oxley, Sokal, Wagner, “Homogeneous multivariate polynomials with the
   half-plane property,” Advances in Applied Mathematics 32 (2004), 88–187.
   LSU author/institutional record and abstract:
   https://repository.lsu.edu/mathematics_pubs/1235/
   DOI: https://doi.org/10.1016/S0196-8858(03)00078-2
   Used for context and attribution, not an unquoted new stability criterion.

2. Flajolet and Sedgewick, Analytic Combinatorics (Cambridge UP, 2009).
   Official author book page and detailed chapter guide:
   https://sedgewick.io/books/analytic-combinatorics/
   Official booksite: https://ac.cs.princeton.edu/home/
   Used to credit labelled constructions, singularity methods, and parameter
   deformations. The concrete coefficient and limit calculations are supplied.

3. McKee and Smyth, “Integer symmetric matrices having all their eigenvalues
   in the interval [-2,2],” Journal of Algebra 317 (2007), 260–290.
   Author publication record:
   https://webhomes.maths.ed.ac.uk/~chris/papers/papers.html
   Related primary abstract/HTML:
   https://arxiv.org/abs/0907.0371
   https://arxiv.org/html/0907.0371v1
   Spectral context only. The operative ADE tree list is the pinned report's.

4. Aldous, “The continuum random tree III,” Annals of Probability 21 (1993),
   248–289. DOI: https://doi.org/10.1214/aop/1176989404
   Publisher/search bibliographic record was checked; full-text access through
   the fetched publisher page was not obtained. Cited only for a proposed
   further question, not as a normalization input or proof dependency.

## Search and priority limitations

Focused searches combined random labelled trees, marked trees, ADE skeletons,
matching-support stability, and half-plane-property terminology. Some broad
searches returned irrelevant machine-learning or commercial pages; those were
not used as mathematical evidence. An attempted arXiv URL fetch failed and
was not used. The review did not locate a prior publication giving these
precise formulas, but it was not exhaustive and does not establish first
priority. Classical ingredients and the existing repository results are
explicitly credited in the article and proof ledger.
