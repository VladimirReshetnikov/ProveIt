# Provenance ledger

## Current five-publication synthesis

This canonical package combines material from two former, coequal canonical
publications and three retired general-guide donors. The immutable
pre-retirement snapshot of all five source packages is commit
`9560165ae2eb33590404a090ab26bd3ca715f32f`, recorded in
`audit/MERGE_SOURCE_REVISION`; the completed `source_concordance.csv` gives a
reviewed disposition for all 547 source result environments. Directory names
in the table are historical paths in that pinned snapshot, not live package
paths.

| Historical source package | Role in this synthesis |
| --- | --- |
| `q_pochhammer_q_binomial_monograph/` | Forward algebraic, combinatorial, analytic, arithmetic, geometric-interpolation, Thue--Morse, and Fabius--Rvachev backbone. |
| `inverse_q_analogs_and_series/` | Universal and branch-aware inversion, asymptotic transfer, certification, inverse observables, five labelled conjectures, and the six-package provenance/assets preserved below. |
| `general-q-series-guides/q-series-proof-oriented-article/` | Donor of stronger or independent very-well-poised, theta/modular, sums-of-squares, Bailey, and continued-fraction material. |
| `general-q-series-guides/q_series_from_first_principles/` | Donor of the general Bailey parameter-lowering step and full Andrews--Gordon theorem. |
| `general-q-series-guides/q_series_monograph/` | Donor of exact eta asymptotics, coefficientwise-limit, Borwein-reciprocity, and selected frontier material after correction. |

The three guides arrived respectively in commits
`1360db6064c676f83bceb23bece5ed304dd09ce8`,
`c167e550348bfb33b4297684100d55dfb48b8c1a`, and
`1f0f98390d551725fc7d2274638dbd7de86ee346`. They had no unique non-document
assets: each donor package consisted only of TeX, PDF, and a historical digest
receipt. Their superseded PDFs were retired with the donor packages
and are not canonical renderings of this larger source. The former forward
and inverse manuscript PDFs were removed for the same reason. The merged
master retains one publication checkpoint,
`q_pochhammer_q_binomial_monograph.pdf`. This retained PDF is a historical
389-page A4 artifact of 3,254,138 bytes with SHA-256
`b8add607c85ee35be98dabf36879e1d45fb093c6b453e93679c80295fae715bc`.
It was synchronized to the source checkpoint at commit
`736a241d1a025d64ac73b1573b17a7b3fc02652d`: 16,339 lines and 810,779
bytes, with SHA-256
`14c444feb14c435bc300becd9c8cd2765c1e96f608dd79da462becc41b28ed22`.

The live working source now postdates that receipt. No live `SHA256SUMS` file
is maintained or should be recreated; this is historical artifact metadata
only, and the retained PDF does not claim render parity with the current TeX.
The record in `README.md` gives the retained artifact's page, size, and font
metadata and makes the same no-current-parity qualification.
PDFs retained beneath `assets/` are research figures, not manuscripts.

The current source incorporates exhaustive crosswalks for
`QPochhammerEntire` (zero definitions and five legacy compatibility theorems),
`QPochhammerInfinite` (one definition and twenty-nine theorems),
`QPochhammerDissection` (zero definitions and two theorems),
`GaussianBinomialFixedColumnRate` (zero definitions and ten theorems),
`GaussianBinomialGreaterOneAsymptotics` (zero definitions and two theorems),
`GaussianBinomialPalindromic` (zero definitions and fourteen theorems),
`GaussianBinomialPolynomialStructure` (zero definitions and five theorems),
`GaussianBinomialCumulants` (two definitions and twenty-four theorems),
`GaussianBinomialBounds` (zero definitions and six theorems),
`FinitePolynomialFunctional` (zero definitions and sixteen theorems),
`GeometricPochhammerNormalConvergence` (zero definitions and three theorems),
`GeometricResidualMoments` (zero definitions and nine theorems),
and `GeometricUniformRealization` (one definition and seventeen theorems).
It also inventories `QMultinomial` (one definition and nine
theorems), `QuantumMultinomial` (zero definitions and five theorems),
`QPochhammerInfiniteBounds` (zero definitions and five theorems),
and `QPochhammerComplexOrder` (one definition and four theorems),
`BasicHypergeometricSeries` (two definitions and five theorems),
`HeineTransformation` (two definitions and five theorems), and
`QGaussSummation` (zero definitions and two theorems). The next tranche adds
`QExponential` (three definitions and eight theorems), `JacksonIntegral` (one definition and seven
theorems), `ThetaQuasiPeriodicity` (one definition and six theorems),
`QPochhammerLogDerivative` (zero definitions and ten theorems),
`QPochhammerOrderDerivative` (zero definitions and three theorems), and
`JacobiCubic` (zero definitions and two theorems). The current tail adds
`CentralQBinomialReduction` (zero definitions and six theorems),
`RegularCentralQBinomialSum` (two definitions and one theorem), and
`CyclotomicFactorization` (zero definitions and seven theorems), followed by
`CyclotomicDivisibility` (zero definitions and three theorems),
`PrimitiveRootBlock` (zero definitions and three theorems), `QCatalan` (one
definition and eleven theorems), and `QLucas` (zero definitions and seven
theorems; its local `two_mul_choose_two` helper is private, while the public
theorem of that name belongs to `QChuVandermonde`). The latest tail adds
`QBetaIntegral` (one definition and eight
theorems) and `NewtonInterpolation` (three definitions and nineteen theorems),
followed by `GaussianBinomialInteger` (one definition and ten theorems),
`GaussianBinomialComplexOrder` (one definition and five theorems), and
`QPfaffSaalschutz` (zero definitions and three theorems),
`TwoPhiOneReversal` (two definitions and twelve theorems), and
`QChuVandermonde` (zero definitions and ten theorems), together with
`GaussianBinomialBounds` (zero definitions and six theorems). The
`QPochhammerEntire.lean` leaf proves the fixed-nome
single-symbol locally uniform product and differentiability, the
division-free factor-zero criterion including `q = 0`, the reciprocal-power
zero lattice for nonzero nome, and simple analytic order at every zero. The
generic `QPochhammerInfinite.lean` surface now owns actual derivative
nonvanishing from every raw factor equation, including `q = 0`, and analytic
order exactly one at every zero; `QPochhammerEntire.lean` preserves the legacy
complex-wrapper naming surface. Only `thm:poch-entire` is promoted by those
single-symbol results. The newer three-theorem leaf proves
the additional outer product's local-uniform (normal) convergence for every
complex strict contraction, including `q = 0`, and gives the dyadic Rvachev
product and bounded-Fabius Fourier specializations. The compound
`thm:qF-spectral` row remains Partial because its named centered/MGF packaging
and exterior reciprocal, pole-divisor, and zero--pole clauses are absent. The
live facade audit contains 921 modules and 11,575 public declarations with no
documentation gaps. Those corpus-wide totals include the q--Chu, Richardson,
geometric-law barycenter, Lagrange--Rvachev matrix, arbitrary-space geometric
realization, regular-central-sum, Lambert branch-gap Bernoulli, affine
Prouhet, and complex moment-product follow-ups; they do not make the retained
historical artifact current. Ten declarations come from the sibling
`FabiusFunction.GeometricRichardsonGenerating` source-only module; three more
are the explicit Gaussian second-derivative and division-free moment
identities. The sibling `LambertWBranchGapBernoulli.lean` leaf contributes
zero definitions and exactly five theorems:
`summable_norm_bernoulli_mul_pow_div_factorial`,
`summable_bernoulli_mul_pow_div_factorial_iff`,
`hasSum_bernoulli_mul_pow_div_factorial`,
`hasSum_bernoulli_mul_pow_div_factorial_complex_iff`, and
`principalLambertW_lowerLambertW_eq_bernoulliSeries`. They cover real absolute
convergence for `|z| < 2*pi`, complex summability exactly when
`‖z‖ < 2*pi` and hence divergence on and outside the boundary, the nonzero
real Bernoulli-EGF quotient, the actual complex `HasSum` value
`(complexExpm1Div z)⁻¹` throughout the open disk, and the paired strict Lambert
branch formulas when the positive gap is below `2*pi`. Together with the
three finite branch-coordinate modules, the exhaustive Lambert union has
4 definitions + 37 theorems = 41 public declarations. The radius/boundary
clause, Guide label `eq:pair-Bernoulli-general`, and canonical-removable
reading of `eq:bernoulli-gen` are Exact. Here `complexExpm1Div 0 = 1` and it
equals `(exp z - 1) / z` away from zero; this is not the literal totalized
quotient at zero and asserts no holomorphy. Higher/full Puiseux and logarithmic
expansions remain open. None of these sibling source-only changes alters this
monograph's forward-status counts or retained historical artifact, and no
render parity is claimed. The
one-definition/seventeen-theorem `GeometricUniformRealization.lean` leaf
proves the missing arbitrary-space bridge: `iIndepFun` unit-interval
coordinates with uniform marginal laws have joint law `uniformProduct`, so
the actual pointwise geometric series inherits convergence, bounds, exact
support, mean, reflection, and the CDF identities. Its affine theorem uses a
fresh canonical-law copy independent of the head coordinate. The
two-definition/one-theorem `RegularCentralQBinomialSum.lean` leaf proves the
regular central sum for `0 < q < 1` under the exact simultaneous denominator
condition `qPochhammerInfIn (q^(alpha+1)) (q^2) != 0`. This excludes the full
complex lattice `alpha = -1 - 2*j + 2*pi*I*m/log q`, not merely its real
negative-odd slice. Even negative integral parameters remain admitted, where
the field-totalized `qGammaC` quotient is zero in agreement with the product
side; no holomorphy at a pole is claimed. The
zero-definition/ten-theorem `GaussianBinomialFixedColumnRate.lean` leaf gives
two generic finite-product defect bounds, the denominator-free relative
Gaussian estimate, fixed and shifted nonasymptotic additive errors, the
shifted `Tendsto`, and all four fixed/shifted relative/additive Big-O wrappers.
It works over the stated generic multiplicative-norm ring or normed-field
interfaces and includes `q = 0`; the older unshifted limit remains in
`QBinomialTheoremInfinite.lean`.

The current q-series increment starts with the one-definition/eight-theorem
`GeometricUniformMomentPolynomial.lean` leaf. Its exhaustive public surface is
`geometricUniformMomentPolynomial`,
`geometricUniformMomentPolynomial_zero`,
`geometricUniformMomentPolynomial_succ`,
`geometricUniformMomentPolynomial_natDegree_le`,
`geometricUniformMomentPolynomial_eval_zero`,
`geometricUniformMomentPolynomial_one`,
`geometricUniformMomentPolynomial_two`,
`geometricUniformMomentPolynomial_three`, and
`geometricUniformMomentPolynomial_four`.  The recursive rational polynomial,
its zeroth value and residual-product recurrence, the triangular degree bound,
the value at zero, and the first four nonconstant cases are exact.  The
downstream `GeometricUniformMomentPolynomialBridge.lean` leaf contributes zero
definitions and the single public theorem
`geometricUniformMomentPolynomial_eval₂_eq_mgf_taylorCoefficient`.  On the
full real domain `|q| < 1`, it identifies the recursive polynomial with the
finite-q-Pochhammer normalization of the genuine geometric-uniform MGF Taylor
coefficient; the theorem is regular at `q = 0` and includes negative
contractions.  The next `GeometricUniformComplexMomentProduct.lean` leaf has
one definition, `geometricUniformComplexMomentProduct`, and exactly two public
theorems, `hasProdLocallyUniformly_geometricUniformComplexMomentProduct` and
`geometricUniformMomentPolynomial_eval₂_eq_complexMomentProduct_taylorCoefficient`.
They construct the actual manuscript product for every complex `‖q‖ < 1`,
including `q = 0`, prove its locally uniform convergence, and identify the
recursive polynomial with the finite-q-Pochhammer normalization of its Taylor
coefficient.  This makes the inner complex product/coefficient bridge exact.
The following `GeometricUniformExteriorComplexMomentGerm.lean` leaf has one
definition, `geometricUniformExteriorComplexMomentGerm`, and exactly two
theorems, `analyticAt_geometricUniformExteriorComplexMomentGerm` and
`geometricUniformMomentPolynomial_eval₂_eq_exteriorComplexMomentGerm_taylorCoefficient`.
For every complex `1 < ‖q‖`, it constructs the actual reciprocal germ, proves
analyticity at zero, and gives the same normalized Taylor-coefficient identity.
Conservatively, `thm:qF-moment-polynomial` remains Partial rather than Exact:
no single Lean `RatFunc` packages the common inner/exterior coefficient, and no
theorem proves that clearing that rational function's root-of-unity poles gives
the same total polynomial at the removable value `q = 1`.  The broader
`thm:geometric-uniform-mgf` remains Partial.  The exhaustive
zero-definition/three-theorem `GeometricUniformMomentPolynomialDegree.lean`
surface is `coeff_geometricUniformMomentPolynomial_choose_two`,
`coeff_geometricUniformMomentPolynomial_choose_two_sub_one`, and
`geometricUniformMomentPolynomial_natDegree_eq`.  It proves the leading
coefficient `bernoulli' n/n! = (-1)^n B_n/n!`, the displayed subleading coefficient
`-bernoulli' n/n! + bernoulli' (n-1)/(2*(n-1)!)` for `n >= 2`, and exact
degree `n.choose 2` for `n=1` or even `n`, otherwise `n.choose 2-1`.
Consequently `prop:qF-P-degree-sharp` is Exact, with no analytic or
root-of-unity hypothesis.

The base 904/11,457, real-bridge 905/11,458, inner-complex 906/11,461, and
pre-merge exterior-branch 907/11,464 counts remain historical checkpoints.
The actual merged-main pre-local checkpoint is 919/11,569; the exterior leaf
gives the next historical checkpoint 920/11,572 without another status move;
and the sharp-degree leaf gives the live 921/11,575 census.
The facade also contains the zero-definition/two-theorem
`GaussianBinomialGreaterOneAsymptotics.lean` leaf; its exhaustive declarations
are `gaussianBinomial_gt_one_fixedColumn_relativeError_isBigO` and
`gaussianBinomial_gt_one_central_isEquivalent`. For real `q > 1` they prove,
respectively, the exact printed normalized fixed-column error
`(q⁻¹;q⁻¹)_k (q^(k*(n-k)))⁻¹ [n,k]_q - 1 = O((q⁻¹)^(n-k+1))` and
the central equivalence `[2m,m]_q ~ q^(m*m) (q⁻¹;q⁻¹)_∞⁻¹`. Natural
subtraction is total in the first statement, while reciprocity is needed only
eventually when `k ≤ n`; together with `gaussianBinomial_inv`, these make
`cor:qgreaterone` Exact without asserting a shifted-central or wider
nome-domain result. `GeometricResidualMoments.lean` contains zero definitions
and nine public theorems. The pair
`sum_geometricLagrangeWeight_mul_scaled_geometric_pow_of_pos` and
`sum_geometricLagrangeWeight_mul_eval_scaled_geometric` proves respectively
the positive-degree moment formula and polynomial exactness at zero over an
arbitrary field, under injectivity of `k |-> q^k` on the finite node range.
The polynomial theorem accepts arbitrary `c`, so the manuscript's `c != 0`
hypothesis is subsumed and the mass-one boundary `c = 0` is also covered.
This exact-by-composition API promotes `cor:scaled-geometric-moments` without
changing any other row. The new generic theorem
`sum_weight_mul_eval_affine_of_topCoeff_extractor` in
`FinitePolynomialFunctional.lean` transports any same-ring top-coefficient
extractor across `a + b * node i` over every commutative semiring. Composed
with `halfQBinomial_negativeDyadic_polynomial_sum_eq_mersenne`, it makes
`cor:geometric-prouhet-affine` Exact under the canonical rational-polynomial
convention. It assumes neither `b != 0` nor distinct transformed nodes and
therefore includes `b = 0` and `n = 0`. The current semantic-union census is
921/11,575.
Neither these source-only additions nor the preceding Lambert addition changes
the retained historical artifact, and no render parity is claimed. The
forward status inventory covers 282 labelled results:
178 Exact / 81 Partial / 15 None / 8 N/A; the relevant
Dyadic Gaussian--Thue--Morse chapter is 9/46/1/0, and the 191-result pre-Fabius core is
36 / 29 / 123 / 3.
The five-publication concordance
has 91 Lean-proved, 387 human-proved frontier, 60 not-applicable, and 9
conjecture rows. The zero-definition/one-theorem
`HalfQBinomialRootSimplicity.lean` leaf contributes
`halfQBinomial_sum_rootMultiplicity_two_pow`; together with
`halfQBinomial_sum_eq_zero_iff` and
`gaussianBinomial_half_eq_halfQBinomial`, it makes
`cor:halfbase-root-locus` Exact under the canonical rational-polynomial
convention. The unrelated `cor:qbinom-inversion-law` remains Partial. Both the
retained `thm:fixed-column-limit` source row and the
older `prop:fixed-k-limit` row redirected to it now inherit the exact canonical
status. The `cor:positivity`, `thm:qbinom-structure`, and
`prop:gq-positive-palindromic` rows are Exact: both Gaussian structure APIs
support the structure row, and the fourteen-theorem generic API now gives
the strict-interior coefficient-of-`q` formula and all boundary zeros. The
central-reduction row is Exact through its division-free commutative-ring
identity and field quotient wrapper. The cyclotomic-factorization row is Exact
for the factorial form over every commutative ring and the Gaussian form over
every integral domain, with the exponent bounds explicit. The complete root
block, evaluated q-Lucas theorem, square-free cyclotomic criterion, and
q-Catalan row are Exact. The primitive-root value in the Babbage corollary is
formalized, but its derivative clause keeps that compound row Partial. The
half-base Gaussian valuation row remains Partial because its concluding
odd-integer valuation statement has not yet been formalized. The q-beta integral and
recurrence rows are Exact on their stated positive real domain, and the
geometric Newton and triangular-coefficient rows are Exact through the generic
field-valued interpolation module and its geometric-grid specialization. The
terminating q-Pfaff--Saalschütz row is Exact under its explicit denominator
hypotheses; the integer-index Gaussian identities and reciprocal series and
the two complex-order series rows are also Exact on the domains recorded in
the crosswalk, while the separate complex-parameter property rows remain
unformalized. The two q-Chu--Vandermonde evaluations and the terminating
reversal lemma are Exact for the actual `twoPhiOne` tsum, including the
full-domain second sum, reflection involutivity, and double reversal. The
separate reversal-derivation proposition remains Partial: its compiled route
assumes `C ≠ 0` and `(A;q)_n ≠ 0`, while the full-domain proof uses direct
finite q-Cauchy; rational continuation and the commutative-ring extension are
not formalized. The quantum-multinomial row is Exact over every semiring under
the displayed q-commutation hypotheses, without assuming that q is central or
that the ambient semiring is commutative. `GaussianBinomialBounds` reuses
`finiteQPochhammerIn_self_pos` from `GeneralQConditionNumber` and supplies
evaluated reciprocity and the finite growth bounds on both sides of `q = 1`;
the imported positivity theorem is not counted as a declaration of the
bounds leaf. Its six exported theorems close the exact finite-growth row, while
the two-theorem greater-than-one leaf closes the remaining fixed-column and
central asymptotic clauses in their printed normalization. No PDF was generated locally while resolving this merge; the
389-page artifact remains the retained historical publication checkpoint and
does not render the current source.

The former q-Pochhammer/q-binomial monograph arrived in commit
`47172bc03ec078961d8b023dfe156ecd712efb65`. Its pre-repair source SHA-256 was
`9c6aec1066e71bedc612703c12d29b44d44e166e3d72a25566b86d89291c95be`;
the detailed seven-sibling consolidation and correction history remains in the
repository draft manifest. The completed five-publication concordance is kept
separate from the older inverse-source concordance so neither immutable audit
domain is silently reinterpreted.

## Five-publication result inventory

`audit/extract_merge_sources.py` inventories every theorem-style environment
from the five source publications at `audit/MERGE_SOURCE_REVISION`. The pinned
snapshot contains exactly 547 environments:

| Historical source package | Result environments |
| --- | ---: |
| `q_pochhammer_q_binomial_monograph/` | 276 |
| `inverse_q_analogs_and_series/` | 103 |
| `general-q-series-guides/q-series-proof-oriented-article/` | 63 |
| `general-q-series-guides/q_series_from_first_principles/` | 43 |
| `general-q-series-guides/q_series_monograph/` | 62 |
| **Total** | **547** |

By source kind these are 237 theorems, 76 propositions, 50 lemmas, 114
corollaries, 45 definitions, 10 examples, 7 conjectures, 6 problems, and 2
algorithms. The immutable ten-field source projection has SHA-256
`f2e8eb72de37e7f0e05e1d9bee126ebe369cd96ed7882c75ddbdf1015d9494a4`.
Every one of the 168 guide rows has a reviewed disposition and an explicit
canonical destination label. This includes historical-status destinations for
the retired Borwein-sign conjecture and the donor's already-developed
bilateral-Bailey-lattice prompt.

The same extractor generates all thirteen concordance columns, not only the
immutable ten-column source projection. Its default mode exact-compares every
generated editorial decision with the checked ledger. The explicit
`--write-reviewed-csv` mode uses only the pinned revision, requires every
override selector to match exactly once, validates a temporary serialization,
and atomically installs the result. Thus later deduplication redirects and
historical literature dispositions are reproducible rather than hidden manual
edits.

The concordance is deliberately result-level: it does not pretend to be a
byte archive of repeated proof prose, remarks, formula tables, bibliographies,
or publication renderings. The pinned Git revision supplies that complete
archival role. The canonical source supplies the reviewed statements, strongest
proved forms, complete retained proofs, useful explanatory material, and
precisely delimited open problems.

Before donor retirement, a separate semantic audit covered all 23 guide
remark environments, 96 section or subsection headings, five longtables, and
53 bibliography entries, rather than relying on theorem extraction alone. It
identified and transferred fifteen non-theorem product-identity source records,
their exact finite quality-control boundary, the missing Rogers--Ramanujan and
Andrews--Gordon formula-atlas entries, six compact proof or discovery insights,
and the literature needed to correct two outdated open-status claims. The
remaining convergence ledgers, notation indexes, proof-completeness tables,
central formula rows, and repeated explanations were represented by stronger
canonical statements or existing dependency and formalization appendices.

The remainder of this ledger preserves the earlier six-package inverse-q
consolidation. Historical names, archive hashes, source paths, and the pinned
revision are facts about that prior merge and deliberately remain unchanged.

The canonical volume absorbed the following six source packages.  The paths
below are historical paths relative to their former sibling layout under
`exponents-and-q-series/`.  The exact normalized source tree is pinned by
[`audit/SOURCE_REVISION`](audit/SOURCE_REVISION), and repository history
preserves every retired path.

| Source package | Canonical role |
| --- | --- |
| `inverse_q_analog_functions_report/` | Branchwise narrative, parameter selection, real and complex branch atlases, numerical continuation. |
| `inverse_q_analog_jet_atlas/` | Universal inverse jets, Bell-polynomial organization, mixed derivatives, Lagrange-Good inversion, coefficient atlases. |
| `inverse_q_analogs_extended_report/` | Corrected special regimes, certification arguments, radial inverses, and Fabius-Rvachev recovery material. |
| `inverse_q_analogs_report/` | Discriminant and remote-branch analyses, interval and continuation certificates, early conjecture register. |
| `inverse_q_analogs_report-2/` | Independent branch synthesis, reciprocal regimes, compact coefficient tables, algorithmic cross-checks. |
| `q_pochhammer_q_binomial_expansions_report/` | Canonical forward expansion engine for finite and infinite products, Gaussian and multinomial coefficients, roots of unity, and q-special functions. |

## Intake archive provenance

All six packages arrived on 2026-08-30.  These hashes identify the submitted
archive bytes, before repository normalization or later editorial changes.

| Historical package | Delivered archive | Outer SHA-256 |
| --- | --- | --- |
| `inverse_q_analog_jet_atlas/` | `inverse_q_analog_jet_atlas_2026-08-30.zip` | `9c9a0353eb355e6defb87845c4a2a79d85c537fe5a6c38c5473f9d3d56448ead` |
| `inverse_q_analog_functions_report/` | `inverse_q_analog_functions_report.zip` | `19cc7da37f71ddbbc0c46b91c55c23059a1e305500260bd0a306394f4c21f4de` |
| `inverse_q_analogs_extended_report/` | `inverse_q_analogs_all_parameters_report.zip` | `0263542a7a6a50459eeb0359015b4086245e7311528e80e3875657529825669f` |
| `inverse_q_analogs_report-2/` | `inverse_q_analogs_report_bundle.zip` | `82ab1dc2cbdd4e69d638cfc045d9ca331e8152e1faeba763732fa9231578b875` |
| `inverse_q_analogs_report/` | `inverse_q_analogs_report.zip` | `471ee715022df77f2c5f45b86c213e50e980478eee1a6fc48dd91556cdaeb627` |
| `q_pochhammer_q_binomial_expansions_report/` | `q_pochhammer_q_binomial_expansions_report.zip` | `e8c6e5be4512abc0bacfd904e3f0027b35fd5e47e916a6ad11cc76b2893b3a07` |

The archive hashes identify delivery bytes.  `theorem_concordance.csv`
records normalized result-level provenance, `assets/ASSET_DISPOSITION.csv`
records path-level disposition, and `audit/SOURCE_REVISION` pins the immutable
pre-retirement Git tree used by the source extractor.

The source packages were independently delivered reports, not a linear series
of editions.  Shared titles or formulas therefore do not imply ancestry.  The
concordance records semantic provenance per result rather than selecting a
single package wholesale.

## Post-retirement audit reconciliation

The later integration commit `53c431137` replayed seven audit-only sidecars
from an older branch into the already retired paths
`inverse_q_analogs_report/` and
`q_pochhammer_q_binomial_expansions_report/`.  They contained no new theorem
statement, proof, TeX source, PDF, experiment program, figure, or numerical
payload.  Their nonduplicative evidence was reviewed and is preserved here;
the redundant sidecars were then retired again so that the canonical package
remains the sole live inverse-q document.

For `inverse_q_analogs_report/`, the sidecars confirm that the original
17-file delivery matched the archive hash already recorded above.  No
submitter-provided digest receipt existed; a repository arrival audit recorded
digests for all 17 payloads before normalization.  Twelve agree with the
pinned normalized snapshot, while five CSV digests differ solely because the
arrival audit preserved their pre-normalization line endings.  A later
normalized edition passed three
strict serial pdfLaTeX runs, a complete 51-page visual inspection, and
deterministic replay of all seven textual data outputs.  That edition had TeX
SHA-256
`de375ee059e0ee9485286aea13e917363854d610b5ff77672001828fa663699b`
and PDF SHA-256
`1ef95365aa42fc5426dc7f7533096ecdc9605479fa1eb6c2b8757fc25e086fdb`.
The superseded source and rendering are recoverable at commit `444cd6ac2`.
Its repaired endpoint, safeguarded-Newton, near-unit truncation-cost, and
conditional-radicals statements are represented in the source concordance and
the corrected canonical proofs.  The late audit's stronger assertion that the
order-five Maxwell collision was proved is not promoted: it treats a large
secondary-discriminant factorization as exact symbolic output without a
retained certificate.  The canonical *Finite q-Pochhammer inversion* chapter
proves the elementary uniqueness statement for the displayed reciprocal
polynomial but correctly keeps the Maxwell-factor identification uncertified.
The exact reship
`Fabius_Rvachev_Frontier_Report_2026-08-30-E.zip`, with outer SHA-256
`174bf733156cd874cf4f9321c6ab71ca44f311856cc01dc158ddf83dc00cf813`,
was byte-identical to the filed package after documented line-ending
normalization and introduced no additional mathematical content.

For `q_pochhammer_q_binomial_expansions_report/`, the sidecars confirm a
seven-file normalized digest audit, exact replay of the retained 44-line numerical
output, three clean serial pdfLaTeX passes, and visual inspection of the
39-page report.  The validated source had SHA-256
`2d3d47cb82ebeea01d43858599e78ddff3d0c97ac62cbe4f09e3ad7314eb4aee`
and its PDF had SHA-256
`88f8e5b4272a949a0521561d2328eb8312167726fbad5c80088ee017921463c5`.
The superseded source and rendering are recoverable at commit `1d5c97985`.
The retained program and numerical output already live in the canonical asset
tree.  These seven late sidecars are intentionally absent from the 77-row
asset-disposition ledger.  That ledger's 73 tracked source hashes are frozen
against asset snapshot `f46e5d7f6f225bf0a43d8945e67d6f0e4aec8d54`, where
all 73 match.  The separate theorem/source-concordance pin
`6fe9fb8f50e1b8a9a800fa0e8ef6f688f5bb5838` matches only 66 of those 73 asset
rows.  Git commit `53c431137` remains the byte-level archive for all seven
sidecars summarized in this section.

For that reason the earlier six-package consolidation chose the neutral
`inverse_q_analogs_and_series/` directory: promoting the broadest precursor in
place would have falsely suggested that its five peers were merely earlier
editions. The wider merger initially used the similarly neutral
`q_series_and_inverse_analogs/` name. Commit
`7a002460dabbd2094f11be980f4929e2506ec022` then placed exact copies of the
master and PDF at the previously published `q_pochhammer_q_binomial_monograph/`
URL as a temporary compatibility measure. The canonical package now occupies
that published path directly, so the stable URL and the live repository
identity agree. The same-stem path beneath `q-pochhammer-and-inversion/` remains
only a historical source location in the pinned pre-retirement snapshot.

## Source-result inventory

`audit/extract_source_results.py` inventories every theorem-style source
environment from the pinned pre-retirement Git revision.  The six inventoried
snapshots contain 260 such environments:

| Kind | Count |
| --- | ---: |
| theorem | 131 |
| proposition | 28 |
| lemma | 2 |
| corollary | 16 |
| conjecture | 32 |
| problem | 9 |
| research problem | 19 |
| principle | 4 |
| definition | 9 |
| algorithm | 5 |
| computational result | 1 |
| example | 4 |

The generated `theorem_concordance.csv` retains source package, path, line,
label, result kind, title, enclosing chapter and section, and whether a proof
environment followed the statement.  Editorial columns then record the
canonical label, proof status, Lean counterpart when one exists, and the
reason for merging, correcting, retaining, or retiring the source item.

## Non-TeX asset audit and migration

At the pinned pre-retirement revision, the six packages contained 65 tracked
non-TeX files totalling 5,832,780 bytes:
six Python experiment programs, two requirements files, six READMEs, six
historical digest manifests since retired, six generated report PDFs, twenty generated figures, and
nineteen generated data or audit files.  Four additional untracked files in
the forward-expansion package are ordinary `.aux`, `.log`, `.out`, and `.toc`
build intermediates.

Every historical digest in those six manifests matched its corresponding file
at that revision.  SHA-256 comparison found no byte-identical pair among the
69 tracked and untracked non-TeX files.  Similar names therefore did not
license deletion:
for example, the three scripts named `inverse_q_analogs_experiments.py`, the
two PDFs named `inverse_q_analogs_report.pdf`, and the two
`qgamma_inverse_branches.pdf` figures all have different contents.

Only two source packages themselves recorded an immutable repository snapshot:

- `inverse_q_analog_jet_atlas/` records
  `1cea73234a363ddbc392816f6babb5a57920e984`;
- `inverse_q_analogs_extended_report/` records
  `23b19a515ceb44a513b1ec56aeb5c9e99dda5952`.

Both names resolve to commits in the repository.  The other four packages
recorded no package-local immutable source commit, so their build statements are preserved
as historical package claims, not promoted to current validation evidence.
Independently, the theorem/source-concordance audit pins the normalized sources
of all six packages at
`6fe9fb8f50e1b8a9a800fa0e8ef6f688f5bb5838`, the value stored in
`audit/SOURCE_REVISION` and verified as an ancestor of the retirement commit.

Unique scripts, captured outputs, tables, and figures were migrated under
`assets/` when they support a retained theorem, conjecture, or reproducible
calculation.  The completed 77-row disposition ledger retains 39 files---six
programs, 19 CSV/TXT outputs, and 14 vector figures---and retires 38
superseded narratives, duplicate previews, package metadata files, generated
LaTeX fragments, and build products.  It records an immutable source SHA-256
for each of the 73 tracked source files, a canonical destination SHA-256 for
every migration, `NOT_RETAINED` for every retirement, and
`UNTRACKED_TRANSIENT_ABSENT` for the four ignored TeX build paths that did not
exist at the freeze.  All 33 retained non-script payloads match their
historical source bytes.  Exactly five of the six migrated programs carry
distinct destination hashes because their output paths were adapted to the
canonical layout; the forward `q_expansion_experiments.py` stayed
byte-identical because it writes only to standard output and required no path
rewrite.  The programs were rerun serially;
[`assets/VALIDATION.md`](assets/VALIDATION.md) records exact-output parity and
the one disclosed last-digit runtime drift. Canonical destination digests in
`assets/ASSET_DISPOSITION.csv` and repository history preserve the
post-migration byte receipts; no live `SHA256SUMS` file remains, and none
should be recreated.

All six superseded directories were removed from the live tree.
All tracked superseded material remains recoverable from Git history.  The
only untracked files removed with the old directories were four disposable
TeX build intermediates (`.aux`, `.log`, `.out`, and `.toc`) already recorded
as retirements in the asset-disposition audit.

## Scope boundaries with neighboring volumes

This synthesis is canonical both for forward q-algebra, combinatorics,
summation, arithmetic, interpolation, and Fabius--Rvachev product theory and
for branch-specified inverse maps, singular inverse regimes, certification,
and the six-package concordance above. The former historical package at
`q-pochhammer-and-inversion/q_pochhammer_q_binomial_monograph/` is now its
forward backbone rather than a separate neighboring publication.

`Cyclotomic_q_Fabius_Rvachev_Frontier/` remains a separate natural-boundary
and blow-up volume. Its radial root-of-unity layer overlaps
[*Infinite q-Pochhammer inverse geometry*](chapters/03_infinite_q_pochhammer.tex)
and
[*Cyclotomic and Fabius--Rvachev recovery*](chapters/06_cyclotomic_fabius.tex),
but its condensation, Gould--Hopper, polyharmonic, and natural-boundary
programs are broader than inverse-q branch theory. Likewise,
`Exponents_and_q_Series_Frontiers/` owns the geometric-uniform/Fabius
deformation and signed/reciprocal parameter-orbit program, and
`inverse-and-sampling/comb-interpolation/comb_interpolation_synthesis/` owns
the detailed interpolation and stability theory behind the short
geometric-comb application in
[*Cyclotomic and Fabius--Rvachev recovery*](chapters/06_cyclotomic_fabius.tex).
These explicit boundaries prevent the six-source concordance from being
misread as a claim to have absorbed those broader volumes.
