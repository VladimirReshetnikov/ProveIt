# Report176 source and overlap audit

Audit date: 3 October 2026 UTC. This is a bounded source comparison, not a global priority certificate. No external source was changed or published.

## Target and attribution

https://oeis.org/A297487

The live entry was read during the research and independently during the mathematical audit. The 16 displayed values were checked against exact integer enumeration. Its leading equivalent and fifth-order recurrence are explicitly credited to Vaclav Kotesovec, 6 February 2026. Andrew Howroyd's positive-sum PARI program is dated 30 December 2017. Its hypergeometric formula already contains the even perfect-matching subtraction. Report176 claims none of those as new.

https://oeis.org/A297487/b297487.txt

This URL returned a cache miss. No full b-file verification is claimed. The package's 101 values for n=0,...,100 are independently generated exact values; they are not described as 101 externally verified source values.

## Analytic reference

https://dlmf.nist.gov/5.11
https://dlmf.nist.gov/24.2

NIST Digital Library of Mathematical Functions, gamma asymptotic expansions and Bernoulli polynomial definitions. The relevant pages were opened during preparation. The standard sectorial log-gamma expansion and its remainder theory justify a finite differentiated central expansion; all coefficient substitutions are derived in the report and code.

## Closest primary literature

1. R. B. Paris, "Asymptotics of Integrals of Hermite Polynomials", Applied Mathematical Sciences 4(61), 2010, 3043-3056.
   https://www.m-hikari.com/ams/ams-2010/ams-61-64-2010/parisAMS61-64-2010.pdf
   The full 14-page primary journal PDF was read during research. Section 5, equation (5.7), already gives an all-order expansion of the four-equal-Hermite moment. This is prior art for the nearby perfect-matching problem, rather than evidence that every OEIS entry lacking printed corrections is a fresh target. No marked maximal-tripartite theorem was located in that full text. Other related Hermite literature has not been exhausted.

2. R. Azor, J. Gillis, J. D. Victor, "Combinatorial Applications of Hermite Polynomials", SIAM Journal on Mathematical Analysis 13(5), 1982, 879-890.
   https://epubs.siam.org/doi/10.1137/0513062
   Primary abstract and metadata were consulted. They describe pairings classified by homogeneous pairs. Full text was unavailable; no theorem-by-theorem nonoverlap claim is made. Paris discusses an older four-Hermite expansion from this literature and corrections to its printed formula.

3. W. Song, L. Miao, H. Wang, Y. Zhao, "Maximal matching and edge domination in complete multipartite graphs", International Journal of Computer Mathematics 91(5), 2014, 857-862.
   https://www.tandfonline.com/doi/full/10.1080/00207160.2013.818668
   Primary publisher abstract was consulted through an indexed source. Its stated subject is maximum/minimum cardinalities of maximal matchings and edge domination. Full text was unavailable. This closest title match is therefore explicitly acknowledged but not certified theorem-by-theorem disjoint.

4. M. Drmota, L. Ramos, C. Requile, J. Rue, "Maximal Independent Sets and Maximal Matchings in Series-Parallel and Related Graph Classes", AofA 2018, 18:1-18:15.
   https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.AofA.2018.18
   Primary abstract and beginning of the PDF were examined. They count graph-and-marking pairs over subcritical graph classes, different from the fixed dense K_n,n,n model. No conflicting theorem was identified at the examined depth.

## Bounded overlap screen

The accessible public catalogue files were read in full:
- https://github.com/VladimirReshetnikov/ProveIt/blob/main/SetTheory/Cardinals/docs/reports/manifest.tex
  Observed blob: 9b13df172d324a2a87a3e63043c7871679299f9a
- https://github.com/VladimirReshetnikov/ProveIt/blob/main/SetTheory/Cardinals/docs/reports/README.md
  Observed blob: 398c8bff1f3cdacf3014acb759578d8047a2f4e3

Literal ID and subject scans found no A297487 or maximal-tripartite asymptotic report. Existing matching-rank-normalization and preorder matching-support descriptions concern different problems. Whole-repository read-only searches for A297487 and tripartite returned empty results. These are bounded negative checks, not exhaustive absence proofs.

Search queries covered A297487, maximal matchings in complete multipartite/tripartite graphs, asymptotic enumeration, Poisson descriptions, and shifted/multivariate Hermite integrals. No proof of the marked fixed-order expansion and unmatched-vertex laws developed here was located. Safe description: a self-contained derivation and refinement of the credited OEIS leading equivalent, without a global first-priority claim.

## Scope boundaries retained in the article

- Fixed algebraic truncation order only; no convergence of the formal infinite series
- Real v in a compact subset of (0,infinity)
- No fixed complex-v neighborhood theorem
- No exponentially resolved count-parity transseries
- Exact rare numerators permit relative rare-probability expansions despite that count limitation
- Existential constants and asymptotic onsets, not calibrated numerical guarantees
- Boundary-safe integer ceiling enclosures, not unconditional rounding
