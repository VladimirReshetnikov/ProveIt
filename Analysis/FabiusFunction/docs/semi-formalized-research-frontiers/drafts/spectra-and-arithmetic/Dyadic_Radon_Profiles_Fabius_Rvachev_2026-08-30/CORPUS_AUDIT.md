# Corpus audit and nonduplication boundary

## Scope

Target tree:

`https://github.com/VladimirReshetnikov/ProveIt/tree/main/Analysis/FabiusFunction/docs`

The review covered the current public documentation tree and its recursive
`*.tex` corpus, together with historically indexed paths that were subsequently
absorbed into consolidated frontier volumes.  The public tree was inspected on
2026-08-30.  The current documentation root includes the primary
Fabius--Rvachev exposition, the mathematical glossary, the non-elementarity
study, the Lean walkthrough, papers, archives, and the semi-formalized and
non-formalized frontier systems.

The semi-formalized frontier README and draft manifest record a reorganization
on 2026-08-28.  Earlier living drafts were absorbed into thematic consolidated
volumes.  For that reason, the current consolidated sources were used as the
controlling mathematical interface; old path counts were used as negative
controls and provenance aids, not as independent papers.

## Counting caveat

Two preserved inventories use different conventions:

* `corpus_inventory_2026-08-27.txt` records 78 visible TeX paths at its
  checkpoint.  It counts generated table fragments and several frozen source
  revisions as paths, while documenting their dependence on parent reports.
* A later audit package records 57 distinct theorem-bearing TeX artifacts after
  a stronger deduplication/consolidation convention.

The difference is not a coverage gap.  It reflects a living tree, generated
fragments, frozen revisions, and consolidation.  The present novelty boundary
is claim-oriented rather than count-oriented.

## Source families screened

The review included the following mathematical interfaces.

1. **Primary Fabius/Rvachev theory:** normalizations; the centered random
   uniform series; functional-differential equations; exact dyadic values;
   support, smoothness, Fourier products; moments and cumulants; inverse Fabius.
2. **Thue--Morse:** finite products, Prouhet cancellations, summation
   hierarchies, automatic/Mahler formulae, digital identities, rarefaction and
   finite-block transforms.
3. **Exponents and q-series:** q-Pochhammer symbols, Gaussian binomial
   coefficients, reciprocal-base identities, geometric laws, q-interpolation,
   inverse q-special functions, q near 0/1/infinity, and cyclotomic limits.
4. **Spectra and arithmetic:** integer and half-integer zeros, multiplicities,
   spectral zeta functions, determinants, heat traces, arithmetic rays,
   Fourier envelopes, and Pascal--Rvachev hierarchies.
5. **Inverse and endpoint theory:** inverse germs, Lambert-W and Bell
   transseries, quantile transport, dyadic inverse values, and endpoint phase
   functions.
6. **Representations:** Legendre/Jacobi/Chebyshev systems, finite shifted-up
   synthesis, Lagrange/Newton interpolation, multiresolution, convolution and
   repeated-integration models.
7. **Transforms and operators:** Fourier/Laplace/Mellin/Cauchy/Stieltjes
   transforms, fractional calculus, Appell deconvolution, self-sampling,
   Koopman/Stein constructions, and related operator models.
8. **Archived and imported papers:** the classical Fabius and Rvachev sources,
   Arias de Reyna, Haugland, and historical repository versions.
9. **Prior generated frontier packages in the user's library:** Pascal spectral
   arithmetic, free/Boolean cumulants, Stein--Koopman theory, geometric-comb
   interpolation, cyclotomic q limits, inverse-q reports, and related negative
   controls.

## Established material not presented as new

The report explicitly treats the following as imported:

* the rank-one Rvachev random series and infinite sinc product;
* zero multiplicity `1 + nu_2(n)` for the classical product;
* Bernoulli--Mersenne cumulants and complete Bell moments;
* exact dyadic Fabius values and q-binomial identities;
* inverse-Fabius Lambert-W asymptotics;
* classical and higher-rank self-sampling/comb ideas;
* the previously defined Pascal--Rvachev product hierarchy and its
  rank-specific zero divisor, sign sequence, zeta function, and Fourier
  asymptotics;
* Legendre expansions and finite polynomial synthesis;
* cyclotomic q natural boundaries and root-of-unity blow-ups;
* Stein--Koopman and free/Boolean results from prior packages.

## Exact and close-variant novelty searches

The current repository corpus and the user's prior report library were searched
for exact and semantic variants of:

* `Radon projection` + Fabius/Rvachev/up-function;
* `direction profile`, `dyadic direction multiplicity`, `profile law`;
* `zero profile inversion`, `second difference zero multiplicity`,
  `c_v = m_v - 2 m_{v-1} + m_{v-2}`;
* `cumulant tomography`, `C(4^{-n})`, `dyadic Hausdorff measure`;
* `automatic iff parity word eventually periodic`;
* `inverse-Fabius projection coordinates`;
* `Pascal factorization into classical Rvachev variables`;
* general-profile sharp Fourier limsup constants;
* reconstruction of a direction profile from comb precision.

No direct treatment of the complete theorem package in the manuscript was
found.  Several neighboring ideas were found and excluded from the novelty
claims, especially rank-specific Pascal products, spectral zero arithmetic,
self-sampling, Appell deconvolution, and generic tensor-product cubature.

A targeted external web search was also made for Fabius/Rvachev Radon
projections and direction-profile classifications.  It returned classical
Radon-transform material and unrelated uses of the name Rvachev, but no exact
match for the formulas developed here.  This search is not exhaustive enough
to certify worldwide priority.

## Corpus-relative additions in this report

The manuscript proves, relative to the audited corpus:

1. a general infinite-dimensional dyadic Radon projection law built from
   independent rank-one Rvachev variables;
2. exact integer-zero multiplicities
   `m_v = sum_{h<=v} c_h (v-h+1)`;
3. complete spectral inversion by the second difference
   `c_v = Delta^2 m_v` and a discrete-convex classification;
4. the zero-divisor Dirichlet transform
   `Z_c(s) = zeta(s) C(2^{-s})/(1-2^{-s})`;
5. normalized even-cumulant sampling
   `kappa_{2n}(Y_c)/kappa_{2n}(X) = C(4^{-n})`;
6. the dyadic Hausdorff moment representation, complete monotonicity, Hankel
   positivity, and cumulant rigidity;
7. a finite Bell--Legendre--q transform for every profile;
8. a generalized spectral sign formula and the automaticity criterion
   “2-automatic iff exponent parity is eventually periodic”;
9. the exact Prouhet cancellation order of every finite sign block;
10. a sharp general Fourier envelope for `a_j ~ A j^d`;
11. an explicit factorization of every Pascal--Rvachev rank as a dyadic
    projection of classical up-laws;
12. general-profile positive comb cubature with exact sharp precision;
13. inverse-Fabius quantile coordinates for the entire profile cone;
14. a conjectural general-profile Lambert-W endpoint program.

## Priority caution

“New” in the report means *apparently new relative to the audited repository
corpus and the prior packages screened in the user's library*.  It is not a
claim of worldwide historical priority.  Classical ingredients such as Radon
pushforwards, Poisson summation, Hausdorff moments, Bell polynomials, Legendre
polynomials, automatic sequences, and Lambert-W are clearly separated from the
new deductions made by composing them with the Fabius--Rvachev profile law.

## Reproducibility

The archive contains:

* the complete LaTeX source and compiled PDF;
* fully commented Python experiments;
* exact and high-precision CSV data;
* vector and raster figures;
* a human-readable numerical summary;
* this audit;
* the preserved recursive TeX path ledger;
* build instructions, dependency versions, and SHA-256 checksums.
