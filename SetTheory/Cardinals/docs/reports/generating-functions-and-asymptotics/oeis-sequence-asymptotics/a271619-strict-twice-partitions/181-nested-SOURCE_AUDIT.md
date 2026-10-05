# Report 181 source and overlap audit
Date: 2026-10-03, approximately 19:03 UTC
Status: bounded audit supporting Report 181; no exact prior asymptotic result or delivered duplicate located. This is NOT an exhaustive priority clearance. No external writes. The original search was completed before report numbering.

## Result and recommended scope
A358836 was selected as a distinct sequence-specific asymptotic target. The exact generating product is prior, and all generic Fermi/Sommerfeld, q-Pochhammer, modular, saddle-point, and reversion tools must be credited. The report proves the nested-denominator reduction with controlled error and the coefficient/probabilistic transfer for this exact model. It does not claim discovery of the product or generic analytic machinery.

## OEIS primary record
https://oeis.org/A358836
Actual live page read, including formula, comments and references.
- Definition: multiset partitions of integer partitions of n with all distinct block sizes.
- Sequence author: Gus Wiseman, Dec 05 2022.
- Andrew Howroyd, Dec 31 2022, gives Product_{k>=1}(1+[y^k]P(x,y)), P(x,y)=1/Product_{k>=1}(1-y*x^k).
- Therefore Product_{k>=1}(1+q^k/(q;q)_k) is the elementary standard q-binomial specialization of a published OEIS formula, NOT a new exact product.
- Gus Wiseman, Aug 21 2024, gives compositions whose maximal weakly decreasing run leaders are strictly increasing.
- Entry has Howroyd b-file through n=1000, no asymptotic statement and no research-paper citation.
- Linked Wiseman classification: https://oeis.org/A374629/a374629.txt (read).
- Initial coefficients 1,1,2,4,8,15,28,51,...; no coefficient recomputation was assigned to this audit.

## Live ProveIt overlap
Repository search default branch returned no A358836 matches. Search on quoted neighboring identifiers 358836/358830/271619 returned no match. These are bounded code-search negatives, not evidence about every unpublished artifact.
Actual full README reads:
1. https://github.com/VladimirReshetnikov/ProveIt/blob/main/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a022629-distinct-partition-norms/README.md
README blob sha ef1b42edd4fc30ecea6177060d0db55dbcc257d4.
Five merged sources cover fixed powers k^alpha, convolution powers mu, and slot multiplicities k^beta: Product(1+k^alpha q^k)^mu and Product(1+k^alpha q^k)^(k^beta). All-order log expansions, relative saddle expansions, inverses, extreme-value and shape statements are already delivered. None is the q-dependent nested denominator of A358836.

2. https://github.com/VladimirReshetnikov/ProveIt/blob/main/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a291698-moving-fugacity-partitions/README.md
README blob sha 1100837c4187debe5c6636efe6f7d85380f28fcc.
Actual article also fetched/read for relevant theorem scope, source audit and research questions:
https://github.com/VladimirReshetnikov/ProveIt/blob/main/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a291698-moving-fugacity-partitions/article.tex
Article blob sha 36949d3f2a0c2b3c933959abb2dfbe80236f1849.
Covers [q^n] Product(1+n^alpha q^k), alpha in fixed positive compact ranges. Its Section 10.3 explicitly leaves beyond-polynomial fugacity open, identifies log u~n^(1/6) as a new regime, and says the theorem does not cover it.
For the candidate's effective u=P(e^-t), log u~pi^2/(6t) and at the proposed saddle t~n^(-1/4), log u~n^(1/4). Hence the prior theorem cannot be used by direct substitution; q-dependence also changes coefficient extraction.
The Jacobi exact identity and general analytical toolkit are nevertheless overlapping method-level prior.

The comparison was based on the following inspected repository documents:
- a022629-distinct-partition-norms-README.md
- a291698-moving-fugacity-partitions-README.md
- a291698-moving-fugacity-article.tex

## Library audit
Successful read-only calls.
- Searches A358836 and quoted A358836 returned irrelevant fuzzy content hits, no relevant exact match.
- Exact title searches A358836, A271619 and nested partition returned zero exact results.
- Searches multiset partitions, distinct block sizes, nested partitions, Moving Fugacity and A358830 did not locate this model.
- A291698 content query failed to recover the known repository report and fugacity title query returned only unrelated A005163 files. This demonstrates incomplete retrieval: Library miss must not be described as full absence.
- A022629 query located OEIS_Norm_Weighted_Partitions.pdf, actual PDF pages 1-5 read. It is a 26-page delivered report dated Oct 1 2026. Product Fr,s(q)=Product(1+k^r q^k)^s for fixed r>0 and positive integer s; all-orders log and relative saddle expansions/inverses/conditional laws. Confirms distinct model and already-covered methodology.
- The supplied prior-coverage guidance was fully read.

## External primary literature inspected
1. Vivien Brunel, A general asymptotic formula for distinct partitions, arXiv:1709.04955; journal DOI 10.1016/j.aop.2018.03.023.
https://arxiv.org/pdf/1709.04955
Actual PDF text read through the main distinct-partition setup and formula (Section 3).
This is prescribed-number ordinary distinct partitions, using Product(1+exp(-alpha-beta*k)), Euler-Maclaurin and a two-variable saddle. It is relevant Fermi-gas prior, not this nested product.
Caution: early displayed partition products in extracted PDF text include sign/inverse defects; Section 3 equation (26) unambiguously has sum log(1+exp(-alpha-beta*k)). Cite its interpretation, not malformed extraction.

2. Arash Arabi Ardehali and Hjalmar Rosengren, A New Product Formula for (z;q)_infinity, with Applications to Asymptotics. Published Sep 19 2026.
https://link.springer.com/article/10.1007/s00365-026-09783-2
Actual open-access primary text read, especially Introduction and Corollary 2.
Exact gamma-product identity for q-Pochhammer; uniform moving-argument expansion. Corollary 2 fixes arg beta and requires Re y>=-Y with Y fixed, |Im y|<=pi. The candidate effective argument y=t-log P(e^-t)+i*pi has Re y~ -pi^2/(6t), outside that region. Direct application is not justified. Its exact identity, modular transformations, q-product asymptotics and classical references are relevant prior. The article itself says its Section 5 optimal truncation discussion is heuristic/computational, not rigorous.

3. Richard J. McIntosh, Some Asymptotic Formulae for q-Shifted Factorials, Ramanujan Journal 3 (1999), 205-214.
https://link.springer.com/article/10.1023/A:1006949508631
Primary publisher abstract and bibliographic metadata read; full text is subscription content and was NOT read. Abstract confirms complete expansions of q-shifted factorials in polylogarithms and Bernoulli polynomials. Do not claim it rules out the exact candidate.

4. Mircea Merca, Family of MacMahon-type q-series and their combinatorial interpretations, Ramanujan Journal 70, article 4 (2026), published Apr 16 2026.
https://link.springer.com/article/10.1007/s11139-026-01382-w
Actual primary abstract and introductory definitions read. H_k^+- series use factors q^n/(1∓q^n) with weakly increasing selected magnitudes and fixed number k; its inversion formulas involve (±q;q)_infinity q^k/(q;q)_k. It is not the product over these whole block generating series. No exact candidate asymptotic was located there.

5. Knopfmacher–Odlyzko–Pittel–Richmond–Stark–Szekeres–Wormald, The asymptotic number of set partitions with unequal block sizes, EJC 6 (1999), R2, 36pp, DOI 10.37236/1434.
OEIS A007837 and a primary-paper PDF search excerpt were inspected. Full direct EMIS mirror fetch returned 403 and the entire paper was NOT read. It studies labeled set partitions with EGF Product(1+x^k/k!), not A358836. Relevant analogous Fermi filling/hole analysis, but no claim of exact asymptotic overlap can be made from this audit.

## Neighbor distinctions
- A271619 live record read: Product(1+p(k)q^k), distinct block sums, not distinct block lengths; no asymptotic supplied in its inspected entry.
- A261049 live record read: Product(1+q^k)^{p(k)}, distinct block contents; different restriction. It cites R. Kaneiwa, An asymptotic formula for Cayley's double partition function p(2;n), Tokyo J. Math. 2 (1979),137-158. Project Euclid page was inaccessible (one-line response); full Kaneiwa text NOT read.
- A358830 is the twice-partition version, distinguished in OEIS cross-references; not an identification with A358836.
- Do not infer A358836 equals any of these from the word strict/distinct.

## Search boundary
Queries included exact sequence id, product fragments q^k/(q;q)_k, multiset partitions with distinct block sizes, partitions of partitions with distinct lengths, composition run leaders, and q-analog unequal-block set partitions. No exact primary asymptotic match located. Search results often broaden mathematical strings, so this is a targeted bounded search, not proof of novelty.


## Supplement: exact classical references (19:14 UTC)
The provisional mathematical argument was read in full during the source audit. These references support its classical ingredients; they do not certify its new product reduction, small-disk estimates, all-arc bound, or conditioned limit laws.

### Jacobi triple product and Gaussian Poisson transformation
- NIST DLMF 17.8.1, direct equation permalink: https://dlmf.nist.gov/17.8.E1 . Actual formula read: sum_{m in Z}(-z)^m q^{m(m-1)/2}=(q,z,q/z;q)_infinity. Taking z=-P^(-1) gives precisely D(q)(-P^(-1);q)_infinity(q;q)_infinity=sum_m exp[-mu*m-t*m*(m-1)/2] in the dossier. This identity is classical.
- NIST DLMF 20.7.32, direct equation permalink: https://dlmf.nist.gov/20.7.E32 . Actual formula and principal-square-root convention read. This is the theta-3 modular transformation, equivalently Gaussian Poisson summation. In the dossier's real variables it gives
  sum_m exp[-t(m-c)^2/2]=sqrt(2*pi/t) sum_l exp[-2*pi^2*l^2/t] exp(2*pi*i*l*c).
  The sign of the Fourier phase can be reversed by l -> -l. Use c=1/2-mu/t.
- DLMF 20.7(viii) cites Lawden (1989), pp.16-17; Bellman (1961), p.61; Serre (1973), p.109; and Whittaker-Watson (1927), pp.474-475. These bibliographic pointers were verified on DLMF; those books were not separately read.
- Scope: exact identities and their ordinary domains are established references. Uniform bounds after the argument c moves with t, particularly on the candidate's O(t^2) complex disk, still need the dossier's explicit estimates; citing a modular identity alone does not establish those bounds.

### Ordinary partition modular product and exponential remainder
- NIST DLMF 27.14.12 (eta product) and 27.14.14 (eta transformation):
  https://dlmf.nist.gov/27.14.E12
  https://dlmf.nist.gov/27.14.E14
  Actual displayed formulas and multiplier read. Equivalent transformation and multiplier:
  https://dlmf.nist.gov/23.18.E5
  https://dlmf.nist.gov/23.18.E6
- Especially convenient explicit primary-paper reference: Arabi Ardehali-Rosengren (2026), equation (15), https://link.springer.com/article/10.1007/s00365-026-09783-2 . Actual formula and surrounding text read:
  (e^-t;e^-t)_infinity=sqrt(2*pi/t) exp(t/24-pi^2/(6*t)) (e^(-4*pi^2/t);e^(-4*pi^2/t))_infinity.
  The paper identifies this as the classical Dedekind eta modular transformation; do not attribute discovery to the 2026 paper.
- Taking minus logarithms gives exactly
  log P(e^-t)=pi^2/(6*t)+(1/2)log(t/(2*pi))-t/24-log(Q;Q)_infinity,
  Q=exp(-4*pi^2/t).
  Thus the real-positive remainder is O(exp(-4*pi^2/t)); the dossier's weaker O(exp(-c/t)) follows. This consequence of the displayed identity was checked algebraically.
- This exact eta specialization has a larger valid domain than that paper's Corollary 2 moving-argument uniform expansion. The earlier warning about Corollary 2 does not restrict use of this exact identity.

### MacMahon Mellin transform and complete logarithmic expansion
- Product reference: NIST DLMF 26.12.20,
  https://dlmf.nist.gov/26.12.E20
  verifies MacMahon's generating function M(q)=Product_{k>=1}(1-q^k)^(-k).
- Accessible primary/reference treatment: Sergiy Koshkin, Quantum Barnes Function as the Partition Function of the Resolved Conifold, International Journal of Mathematics and Mathematical Sciences (2008), article 438648, DOI 10.1155/2008/438648:
  https://onlinelibrary.wiley.com/doi/10.1155/2008/438648
  Published Theorem 3.1 (Ramanujan-Wright), equation (3.22), and its residue proof were read.
  Author preprint: https://arxiv.org/pdf/0710.2929 ; Theorem 1 and equation (42), PDF page 17 (printed page 17), with proof continuing on page 18. Actual PDF extracted theorem and proof read; numbering differs from the published article.
- The theorem states the Mellin kernel Gamma(s) zeta(s-1) zeta(s+1), Re s>2, and the full real-positive expansion
  log M(e^-t) ~ zeta(3)/t^2+(log t)/12+zeta'(-1)
    +sum_{g>=2}[(2g-1) B_(2g) B_(2g-2)/((2g-2)(2g)!)] t^(2g-2).
  Equivalently the t^(2m) coefficient is zeta(1-2m)zeta(-1-2m)/(2m)!.
  At m=1, zeta(-1)zeta(-3)/2=(-1/12)(1/120)/2=-1/2880.
  Therefore every listed classical MacMahon term in the dossier is prior, including the constant zeta'(-1), not a new discovery.
- Historical primary: E. M. Wright, Asymptotic Partition Formulae: I. Plane Partitions, Quarterly Journal of Mathematics, os-2 (1931),177-189:
  https://doi.org/10.1093/qmath/os-2.1.177
  https://academic.oup.com/qjmath/article-abstract/os-2/1/177/1565947
  Bibliographic metadata verified on publisher site; original full text was not accessible/read. Koshkin explicitly credits Wright with the first rigorous asymptotic and calls the complete expansion Ramanujan-Wright. Cite Wright historically and Koshkin for the actually inspected theorem/proof.
- Scope: Koshkin's displayed theorem is stated as t approaches 0 on the positive real axis. Its proof records the poles and classical Gamma/zeta estimates, but do not cite the theorem as if it explicitly supplies this dossier's moving-complex-disk remainder. The latter can be justified independently by the same Mellin contour argument (Gamma decay dominates zeta polynomial growth in any fixed closed sector inside |arg t|<pi/2), with the contour shifted sufficiently far for the desired finite order. Likewise the asymptotic series is not claimed convergent.


## Manuscript scope after mathematical review

The manuscript incorporates a uniform c t² zero-free disk proof, the finite-end four-region estimates, derivative losses handled by extra expansion orders, the rare-absence mixture inequality on every angle, and an integrated weighted Taylor remainder for all fixed Edgeworth orders. The optional probability results include the moving complex saddle and global arcs, followed by truncated-product conditioning and joint independence.

The elementary relative equivalent includes the constant-order completion with proved O(n^(-1/4) log^4 n) logarithmic error. Higher-order discrete inversion uses pointwise integer bounds divided by the slope and two-floor envelopes. A fixed piecewise-linear logarithmic interpolant has an order-t^4 horizontal curvature barrier; the report does not repeat an unrestricted arbitrary-accuracy interpolation claim. These mathematical completions do not broaden the source-search or historical-priority claims.

## General saddle reference added during manuscript preparation

The official Analytic Combinatorics booksite, https://ac.cs.princeton.edu/home/, was read on 3 October 2026. It identifies Chapter VIII as saddle-point analysis and provides the full textbook. The citation is general methodological background; this source comparison does not claim that the entire textbook was reread or that it proves the nested-product estimates.
