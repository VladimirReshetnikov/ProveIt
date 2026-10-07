# Sources and bounded duplicate ledger for Report 234

Research date: 5 October 2026. This ledger distinguishes known material,
sequence-specific refinements, and retrieval limits. It is not a priority
certificate. Third-party papers and private working audits are not bundled.

## Sequence identification

- OEIS A368246, https://oeis.org/A368246
  The complete indexed primary entry supplied definition, offset 0, values,
  formula, examples, program, and the A143946 cross-reference. Direct fresh entry
  and internal-page requests failed, including HTTP 403. No fresh live revision
  timestamp is claimed. Its historical 29 December 2023 attribution of the
  leading constant conjecture is not represented as a currently open problem.
- OEIS A143946, https://oeis.org/A143946
  The retrieved related primary entry gives the record-position triangle and
  row polynomial z(z^2+1)(z^3+2)...(z^n+n-1), with the A368246 diagonal.
  The report independently proves the finite polynomial and exact index shift.

## Primary mathematical sources

1. Igor Kortchemski, Asymptotic behavior of permutation records, Journal of
   Combinatorial Theory Series A 116 (2009), 1154–1166.
   https://arxiv.org/abs/0804.0446
   Author copy: https://igor-kortchemski.perso.math.cnrs.fr/articles/records.pdf
   Inspected for the record statistic and its different large-deviation regime.
2. Guy Louchard, Sum of positions of records in random permutations: asymptotic
   analysis, Online Journal of Analytic Combinatorics 9 (2014), Paper 1, 20 pp.
   https://doi.org/10.61091/ojac-901
   https://guy.louchard.web.ulb.be/louchard.papers/srecn3.pdf
   Complete paper inspected. Equation (1) already gives the finite polynomial;
   Eq. (2) gives probability normalization; introduction and Eq. (4) explicitly
   discuss the Dickman local limit and prior attribution.
3. Rita Giuliano, Zbigniew Szewczak, Michel Weber, Almost sure local limit theorem
   for the Dickman distribution, arXiv:1309.1578 (2013).
   https://arxiv.org/abs/1309.1578
   Actual 37-page paper inspected. Theorem 2.1 states
   n P(T_n=kappa_n) -> exp(-gamma)rho(x) for kappa_n/n -> x>0.
   At kappa_n=n this already proves b_n -> exp(-gamma).
4. Régis de la Bretèche, Gérald Tenenbaum, On strong and almost sure local limit
   theorems for a probabilistic model of the Dickman distribution,
   arXiv:2012.00528, v4, 8 March 2021.
   https://arxiv.org/abs/2012.00528
   Actual 9-page paper inspected, especially Theorem 1.1 and Eqs. (2.14), (3.1).
   Its diagonal remainder is too large to identify the n^-2 correction in b_n.
   A displayed total-variation oscillation is not the coefficient of this report.
5. Philippe Flajolet, Éric Fusy, Xavier Gourdon, Daniel Panario, Nicolas Pouyanne,
   A hybrid of Darboux's method and singularity analysis in combinatorial
   asymptotics, Electronic Journal of Combinatorics 13 (2006), R103, 35 pp.
   https://doi.org/10.37236/1129
   https://monge.univ-eiffel.fr/~fusy/Articles/FlFuGoPaPo06.pdf
   Actual published paper inspected, with detailed attention to Theorems 1–2,
   Section 3, and Proposition 1. The general all-root and natural-boundary
   method is classical. Its worked product has z^j, not z^(j+1). Its smooth
   corrections must not be imported into A368246. A literal Theorem 2 invocation
   can take L=2K+6; the report proves its sharper L=K+6 cutoff directly by global
   boundary derivative estimates.

## Attribution boundary

Already known or elementary: the finite counting polynomial; its shifted
infinite-product coefficient reduction; the leading exp(-gamma) constant;
Gamma grouping at roots of unity; the hybrid Darboux/singularity framework.

The sequence-specific cancellation of every nonoscillatory algebraic correction,
the displayed second/third-order amplitudes, and their inverse refinements were
not found in the inspected sources. This is a bounded search observation. No
worldwide priority, peer-review status, or formal proof verification is claimed.

The theorem is for each fixed order K. No convergence of an infinite
transseries, uniformity as K grows, effective remainder constant/onset, or
unconditional rounding rule is established.

## Repository duplicate checks

Current catalogues were fetched during reconnaissance:
- https://github.com/VladimirReshetnikov/ProveIt/blob/main/SetTheory/Cardinals/docs/reports/README.md
- https://github.com/VladimirReshetnikov/ProveIt/blob/main/Analysis/Transseries/docs/series-and-transseries/README.md

Actual current sources were inspected, under the repository's
SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/ tree:
- a039831-two-fourier-peaks/article.tex, blob eef2a4545c358403228fc49edd44dff595daae04
- a372395-acyclic-orientation-partitions/article.tex, blob 22f5f4163f2b7a9152c3ef616f0888ad74a010f4
- a279619-level-seven-gamma-constant/article.tex, blob e1aa354a4d78869d206671cf96b160f8041d2bfa
- a238016-restricted-partitions-cubic-boundary/article.tex, blob 0fa433e5b67f5cd33845783352d0a9d3c1a8d7ee
- a189281-path-forest-expansions/article.tex, complete current article inspected

These concern different models. Exact-number A368246 repository searches
returned no match. Neither catalogue absence nor negative exact-number searches
are exhaustive semantic duplicate checks.

## Available document collection

Exact sequence numbers and semantic phrases involving record positions, cycle
minima, and Dickman asymptotics were searched. Actual returned near matches were
opened and identified as unrelated deterministic record-walk, diagonal-alignment,
expression-growth, or surreal-embedding models. Results were fuzzy, and some
inspection was limited to initial pages sufficient to identify the model.
No inspected item duplicated the shifted record product. This does not establish
that no semantically matching work exists elsewhere in that collection.
Private file identifiers and internal working reports are deliberately omitted.
