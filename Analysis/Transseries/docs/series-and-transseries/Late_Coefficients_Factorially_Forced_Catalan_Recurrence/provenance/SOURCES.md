# Sources and scope of comparison

Access date: 2 October 2026. This metadata is written for the report; no third-party full text is included.

## Exact sequence targets

- OEIS A229741: https://oeis.org/A229741
  - Definition: a(0)=1; a(n)=n!+sum a(i)a(n-1-i)
  - Official public export: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A229/A229741.seq
  - Inspected export revision line: #17 May 30 2026 16:40:41
  - The supplied calculation checks all 24 displayed numerical terms
- OEIS A260879: https://oeis.org/A260879
  - The inverse-power coefficients of a(n)/n!
  - Official public export: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A260/A260879.seq
  - Inspected export revision line: #5 Aug 02 2015 06:12:34
  - The supplied calculation checks all 21 displayed numerical terms
  - Inspected entry labels the leading late-coefficient equivalent as a conjecture
- Direct b-file access was unavailable in the initial retrieval. The package makes no claim of a comparison against full b-files
- Browser/search responses can be indexed snapshots; the date of inspection does not guarantee the absence of a later unindexed edit

## Primary literature

1. Stefan Forcey, Aaron Lauve, Frank Sottile, *Cofree compositions of coalgebras*, Annals of Combinatorics 17 (2013), 105–130
   - DOI: https://doi.org/10.1007/s00026-012-0170-5
   - https://arxiv.org/html/1012.3483v1 — Section 2.3, Theorem 2.6 and permutation-over-tree specialization
   - https://webpages.math.luc.edu/~lauve/papers/CCC.pdf — corresponding later result is Theorem 2.7
   - Contribution used: exact combinatorial recurrence; no credit claimed here for this result
2. Michael Borinsky, *Generating asymptotics for factorially divergent sequences*, Electronic Journal of Combinatorics 25(4) (2018), P4.1
   - DOI: https://doi.org/10.37236/5999
   - https://arxiv.org/html/1603.01236v4 — Definition 1, Example 13, Proposition 22, Theorem 32
   - Contribution used: factorial asymptotic classes and analytic outer composition, applied with zero-constant inner series z and F−1
3. Edward A. Bender, *An Asymptotic Expansion for the Coefficients of Some Formal Power Series*, Journal of the London Mathematical Society (2) 9 (1975), 451–458
   - https://doi.org/10.1112/jlms/s2-9.3.451
   - Publisher abstract and Borinsky's description were inspected; the full paywalled paper was not inspected
   - Contribution credited: earlier analytic-composition asymptotic framework

## Relevant existing repository material

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned revision: 4b874cea0012c51a6841ad9c58f6e20fa57c71da

A targeted comparison retrieved 185 selected text sources, including generating-functions-and-asymptotics reports, factorial/Catalan/Borel/Fubini/inverse neighbors, and the canonical volumes. The directly relevant existing source is:

https://github.com/VladimirReshetnikov/ProveIt/blob/4b874cea0012c51a6841ad9c58f6e20fa57c71da/Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex

Its chapter “The Fubini numbers: an exact pole lattice”, label q2:sec:fubini, already contains ordinary and weighted pole formulas and exponential pole-tail estimates. Labels q2:thm:fubini and q2:thm:weighted identify the associated results. This is substantive methodological overlap and is explicitly credited in the article.

## What the comparison does and does not support

The inspected sources did not contain a proof of the specific A260879 late-coefficient expansion. This supports a narrowly worded contribution: the specific conjecture proof, rigorous positive transfer remainder, finite correction generator, and stated inverse corollaries. It does not support claiming new factorial-series calculus or a new general Fubini pole theorem.

This was not exhaustive worldwide priority research. Unpublished work, inaccessible full texts, unindexed sources, equivalent statements with different language, historical branches, binary-only artifacts, and repository areas outside the selected scope were not all excluded. No external publication, OEIS entry, or repository was changed.
