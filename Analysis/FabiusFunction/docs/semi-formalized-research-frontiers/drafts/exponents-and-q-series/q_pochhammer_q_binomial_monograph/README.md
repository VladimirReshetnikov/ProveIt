# q-Series and inverse q-analogs

This directory contains the one canonical document for forward q-series and
branch-aware inverse q-analog theory:
`q_pochhammer_q_binomial_monograph.tex`. Files under `chapters/` are implementation
units included by that master; they are not independent manuscripts.
The reader-facing structure has 28 numbered forward chapters, eight numbered
inverse chapters, and five appendices. The source-only validator's count of 13
chapter files refers to implementation inputs, not to the printed chapter
count.

The consolidation uses the former q-Pochhammer/q-binomial monograph as its
forward backbone and incorporates the former inverse-q synthesis as a
specialist part. The three general q-series guides were donor manuscripts:
their repeated results map to one strongest canonical statement, while only
genuinely stronger or independent material was transplanted. The completed
`source_concordance.csv` assigns every one of the 547 source result
environments a reviewed disposition. All five source-publication trees are
therefore historical inputs preserved by the pinned revision and repository
history, not parallel live packages.

The editorial contract is mathematical rather than mechanical:

- a repeated result is stated once, with the strongest proved hypotheses and
  one complete human-readable proof;
- an erroneous or overbroad assertion is corrected, split, or removed;
- an unproved assertion survives only when it is interesting, precise, and
  plausible, and then only in an explicitly labelled `Conjecture`
  environment;
- numerical and symbolic checks are evidence or regression tests, not
  substitutes for an infinite proof;
- exact Lean counterparts, partial Lean infrastructure, complete human proofs,
  source records, and conjectures are reported as distinct statuses.

## Provenance and reproducibility

`theorem_concordance.csv` and `audit/SOURCE_REVISION` retain the already
reviewed 260-row history of the six precursor inverse-q packages at commit
`6fe9fb8f50e1b8a9a800fa0e8ef6f688f5bb5838`. Those historical source paths
are immutable. `source_concordance.csv` is the completed 547-row disposition
ledger for the five-publication merge surface pinned by
`audit/MERGE_SOURCE_REVISION` at commit
`9560165ae2eb33590404a090ab26bd3ca715f32f`. The ledgers remain separate so
the earlier six-package inverse provenance is not silently reinterpreted.

The migrated `assets/` tree preserves six experiment programs, nineteen
CSV/TXT outputs, and fourteen vector figures selected by the historical
77-row `assets/ASSET_DISPOSITION.csv`. That disposition ledger remains the
authoritative inventory of the 39 retained historical payloads; the pinned
source revisions and repository history preserve their digest receipts. No
live checksum manifest is maintained.

## Validation state

The source-structure gate is:

```text
python audit/validate_canonical.py
```

It checks the complete input graph, balanced environments, unique labels,
resolved references, immediate one-to-one ownership of a nonempty proof by
every proved result, both concordances---the 260-row inverse ledger and the
completed 547-row five-publication ledger---and reproduction of both pinned
source inventories.  Canonical status describes the destination, not the
donor's editorial disposition: a proved row with a live result destination
may never be marked `not applicable`, even when the donor copy was retired.
The larger ledger is reproduced, including all editorial columns, with

```text
python audit/extract_merge_sources.py
```

and may be regenerated explicitly with `--write-reviewed-csv`.  That write is
atomic, is tied to `audit/MERGE_SOURCE_REVISION`, and fails if any editorial
override does not match its pinned source exactly once.

The fifteen status-labelled archival identity records have a separate exact
finite check:

```text
python audit/verify_archival_identity_records.py
```

It compares all coefficients through degree 100 using integer arithmetic:
1,515 equalities in total. This is a transcription-quality gate, explicitly
not an infinite proof of any recorded identity.

Checksum ledgers have been abolished repository-wide; no checksum manifest is
kept for this package or its assets, and no checksum gate is part of its
validation state. Deleted checksum manifests must not be recreated. Historical
SHA-256 values recorded directly in this README and in `PROVENANCE.md` remain
provenance receipts for the named artifacts.

The retained `q_pochhammer_q_binomial_monograph.pdf` is a historical 389-page
A4 artifact of 3,254,138 bytes with SHA-256
`b8add607c85ee35be98dabf36879e1d45fb093c6b453e93679c80295fae715bc`.
It was synchronized to the source checkpoint at commit
`736a241d1a025d64ac73b1573b17a7b3fc02652d`: 16,339 lines and 810,779
bytes, with SHA-256
`14c444feb14c435bc300becd9c8cd2765c1e96f608dd79da462becc41b28ed22`.
The checked working source now contains newer editorial changes, so this is
historical artifact metadata only and no render parity with the current TeX is
claimed. `pdffonts` reports 43 font rows, all embedded and subsetted, with no
Type-3 fonts. The files under `assets/experiments/**/figures/` remain research
figures, not publication manuscripts.

The current source includes exhaustive crosswalks for `QPochhammerEntire`
(zero definitions
and five legacy compatibility theorems), `QPochhammerInfinite` (one definition
and twenty-nine theorems), `QPochhammerDissection` (zero definitions and two
theorems), `QBinomialTheoremInfinite` (one definition and twenty-two
theorems), `GaussianBinomialFixedColumnRate` (zero definitions and ten
theorems), `GaussianBinomialGreaterOneAsymptotics` (zero definitions and two
theorems), `GaussianBinomialPalindromic` (zero definitions and fourteen
theorems), `GaussianBinomialPolynomialStructure` (zero definitions and five
theorems), `GaussianBinomialCumulants` (two definitions and twenty-four
theorems), `GaussianBinomialBounds` (zero definitions and six theorems),
`HalfQBinomialRootSimplicity` (zero definitions and one theorem),
`GeometricPochhammerNormalConvergence` (zero definitions and three theorems),
and `GeometricUniformRealization` (one definition and seventeen theorems).
The wider inventory also includes
`QMultinomial` (one definition and nine theorems),
`QuantumMultinomial` (zero definitions and five theorems),
`QPochhammerInfiniteBounds` (zero definitions and five theorems),
`QPochhammerComplexOrder` (one definition and four theorems),
`BasicHypergeometricSeries` (two definitions and five theorems),
`HeineTransformation` (two definitions and five theorems), and
`QGaussSummation` (zero definitions and two theorems). Recent exact surfaces
add `QExponential` (three definitions and eight theorems), `JacksonIntegral`
(one definition and seven theorems), `ThetaQuasiPeriodicity` (one definition
and six theorems), `QPochhammerLogDerivative` (zero definitions and ten
theorems), `QPochhammerOrderDerivative` (zero definitions and three theorems),
`JacobiCubic` (zero definitions and two theorems),
`CentralQBinomialReduction` (zero definitions and six theorems),
`RegularCentralQBinomialSum` (two definitions and one theorem), and
`CyclotomicFactorization` (zero definitions and seven theorems). The newest
cyclotomic surfaces are `CyclotomicDivisibility` (zero definitions and three
theorems), `PrimitiveRootBlock` (zero definitions and three theorems),
`QCatalan` (one definition and eleven theorems), and `QLucas` (zero
definitions and seven public theorems). Its local `two_mul_choose_two` helper
is private; the unique public declaration of that name belongs to
`QChuVandermonde`. The analytic and interpolation tail adds
`QBetaIntegral` (one definition and eight theorems) and
`NewtonInterpolation` (three definitions and nineteen theorems), covering the
Jackson q-beta product and arbitrary-node/geometric-grid interpolation.
The primary collision-avoiding surface is `nodeNewtonPoly` together with its
six `nodeNewtonPoly`-qualified theorems.  The compatibility surface is
`newtonInterpolant`, `newtonPoly_succ`, `eval_newtonPoly`,
`degree_newtonPoly_lt`, `newtonPoly_eq_interpolate`,
`eq_newtonPoly_of_eval_eq`, and `coeff_newtonPoly_self`; the other eight
declarations supply the recursive coefficients, divided differences, and
geometric-grid specialization.
The newest finite-q surfaces are `GaussianBinomialInteger` (one definition
and ten theorems), `GaussianBinomialComplexOrder` (one definition and five
theorems), `QPfaffSaalschutz` (zero definitions and three theorems),
`TwoPhiOneReversal` (two definitions and twelve theorems),
`QChuVandermonde` (zero definitions and ten theorems),
`QuantumMultinomial` (zero definitions and five theorems), and
`GaussianBinomialBounds` (zero definitions and six theorems), together with
expanded Euler, Jacobi, and Rogers--Szegő material.
The newest combinatorial and certification tranche adds
`BinaryWordInversions` (five definitions and fourteen theorems),
`BoxPartitions` (two definitions and eight theorems), and
`TelescopingCertificate` (zero definitions and five theorems). These give the
binary-word inversion and path-area generating functions, rectangular-box
partition generating functions and counts, finite telescoping certificates,
recurrence uniqueness, and rational-identity specialization. The live facade
audit now contains 921 modules and 11,604 public declarations, with no
documentation gaps. Ten declarations come from the sibling
`FabiusFunction.GeometricRichardsonGenerating` module (three definitions and
seven theorems), whose exact comb-manuscript crosswalk is
`Fabius.geometricLagrangeRichardson_generating`; it does not change this
monograph's forward-status inventory or make its retained PDF current. The
other three are the explicit second-derivative, division-free raw-second-moment,
and division-free variance-numerator theorems in
`GaussianBinomialCumulants`; they strengthen the already-Exact
`thm:qbinom-moments` row without changing its disposition.
The complex leaf itself accounts for the three declarations between the
historical 905-module/11,458-declaration and incoming-branch
906-module/11,461-declaration checkpoints; later merged tranches produce the
live census above.
The subsequent one-module/five-declaration increase is the unrelated sibling
`LambertWBranchGapBernoulli.lean` leaf. Its exhaustive zero-definition public
surface is `summable_norm_bernoulli_mul_pow_div_factorial`,
`summable_bernoulli_mul_pow_div_factorial_iff`,
`hasSum_bernoulli_mul_pow_div_factorial`,
`hasSum_bernoulli_mul_pow_div_factorial_complex_iff`, and
`principalLambertW_lowerLambertW_eq_bernoulliSeries`: real absolute
convergence for `|z| < 2*pi`, complex summability exactly when
`‖z‖ < 2*pi` and hence divergence on and outside the boundary, the nonzero
real Bernoulli-EGF quotient evaluation, the actual complex `HasSum` value
`(complexExpm1Div z)⁻¹` throughout the open disk, and the paired Lambert
formulas on the strict common branch domain with gap below `2*pi`. Together
with the three finite branch-coordinate modules, the exhaustive Lambert union
has 4 definitions + 37 theorems = 41 public declarations. The radius/boundary
clause, Guide label `eq:pair-Bernoulli-general`, and canonical-removable
reading of `eq:bernoulli-gen` are Exact. Here `complexExpm1Div 0 = 1` and it
equals `(exp z - 1) / z` away from zero; this is not the literal totalized
quotient at zero and asserts no holomorphy. Higher/full Puiseux and logarithmic
expansions remain open. That sibling promotion produced the historical
903/11,448 checkpoint and changed none of the q-series forward-status or
source-concordance totals.

The newest q-series tranche starts with
`GeometricUniformMomentPolynomial.lean`, with one definition,
`geometricUniformMomentPolynomial`, and exactly eight theorems:
`geometricUniformMomentPolynomial_zero`,
`geometricUniformMomentPolynomial_succ`,
`geometricUniformMomentPolynomial_natDegree_le`,
`geometricUniformMomentPolynomial_eval_zero`,
`geometricUniformMomentPolynomial_one`,
`geometricUniformMomentPolynomial_two`,
`geometricUniformMomentPolynomial_three`, and
`geometricUniformMomentPolynomial_four`.  It formalizes the recursive
rational polynomial family, the zeroth value and residual-product recurrence,
the triangular degree bound, the specialization at zero, and all displayed
cases through the fourth polynomial.  The downstream
`GeometricUniformMomentPolynomialBridge.lean` leaf has zero definitions and
exactly one public theorem,
`geometricUniformMomentPolynomial_eval₂_eq_mgf_taylorCoefficient`.  For every
real `q` with `|q| < 1`, it identifies evaluation of the recursive polynomial
with the finite-q-Pochhammer normalization of the Taylor coefficient of the
genuine geometric-uniform MGF.  The statement is regular at `q = 0` and also
includes signed negative contractions.  The subsequent
`GeometricUniformComplexMomentProduct.lean` leaf has one definition,
`geometricUniformComplexMomentProduct`, and exactly two public theorems,
`hasProdLocallyUniformly_geometricUniformComplexMomentProduct` and
`geometricUniformMomentPolynomial_eval₂_eq_complexMomentProduct_taylorCoefficient`.
For every complex `q` with `‖q‖ < 1`, including `q = 0`, these declarations
give the manuscript's actual infinite product, its locally uniform convergence
on the whole complex plane, and the exact finite-q-Pochhammer normalization of
its Taylor coefficient.  Thus the inner complex product/coefficient bridge is
exact.  The compound `thm:qF-moment-polynomial` nevertheless remains Partial:
Lean does not yet identify the exterior reciprocal-germ coefficients with the
same rational function `a_n(q) = d_n(q) / n!`, or prove that clearing that
RatFunc's root-of-unity poles gives the same total polynomial at `q = 1`.  The broader
`thm:geometric-uniform-mgf` likewise remains Partial at its unbundled direct
dilation, coefficient-recurrence, formal-uniqueness, and rationality clauses;
`prop:qF-P-degree-sharp` remains None, and `cor:qF-halfbase-dictionary`
remains Partial at its still-missing endpoint formula even though the
half-base polynomial and genuine-MGF normalization are now available.  The
base leaf produced the historical 904/11,457 checkpoint and the exact
None-to-Partial move; the real bridge produced the historical 905/11,458
checkpoint, and the complex leaf produced the historical incoming-branch
906/11,461 checkpoint without another status move. After all merged tranches,
the live census is 921/11,604, the forward ledger is 177 Exact / 81 Partial /
16 None / 8 N/A, and the source concordance is 90 Lean-proved / 388
human-proved frontier / 60 N/A / 9 conjectures.
The same current semantic-union census includes the facade-reachable
zero-definition/two-theorem `GaussianBinomialGreaterOneAsymptotics.lean`
leaf. Its exhaustive surface is
`gaussianBinomial_gt_one_fixedColumn_relativeError_isBigO` and
`gaussianBinomial_gt_one_central_isEquivalent`. For real `q > 1`, the first
controls `(q⁻¹;q⁻¹)_k (q^(k*(n-k)))⁻¹ [n,k]_q - 1` by
`O((q⁻¹)^(n-k+1))`, exactly the printed `O(q^(-n+k-1))` eventually for fixed
`k`; natural subtraction is total, and reciprocity is used only eventually
when `k ≤ n`. The second is exactly
`[2m,m]_q ~ q^(m*m) (q⁻¹;q⁻¹)_∞⁻¹`. Together with
`gaussianBinomial_inv`, whose explicit hypotheses are `q ≠ 0` and `k ≤ n`,
these declarations make `cor:qgreaterone` Exact. No shifted-central or wider
nome-domain statement is claimed. The retained historical PDF renders none of
these q-series leaves or the preceding Lambert tranche, and no source/PDF
parity is claimed.

`GeometricResidualMoments.lean` now has zero definitions and nine public
theorems. Its existing
`sum_geometricLagrangeWeight_mul_scaled_geometric_pow_of_pos` proves the
displayed positive-degree formula, while
`sum_geometricLagrangeWeight_mul_eval_scaled_geometric` proves the polynomial
exactness clause. Both work over an arbitrary field under injectivity of
`k |-> q^k` on `range (n+1)`. The latter permits every scale `c`, including
zero, so it subsumes the manuscript's `c != 0` premise. Together they make
`cor:scaled-geometric-moments` Exact by composition.

The existing `FinitePolynomialFunctional.lean` module now has zero definitions
and sixteen public theorems. Its new
`sum_weight_mul_eval_affine_of_topCoeff_extractor` transports any same-ring
top-coefficient extractor across the affine nodes `a + b * node i` over every
commutative semiring. Composed with
`halfQBinomial_negativeDyadic_polynomial_sum_eq_mersenne`, it makes
`cor:geometric-prouhet-affine` Exact under the established rational-polynomial
convention. Neither a nonzero scale nor distinct transformed nodes are
required, so `b = 0` and `n = 0` are covered.

The zero-definition, one-theorem `HalfQBinomialRootSimplicity.lean` leaf adds
`halfQBinomial_sum_rootMultiplicity_two_pow`, proving multiplicity exactly one
at every displayed dyadic root `2^j`, `j < n`. Composed with
`halfQBinomial_sum_eq_zero_iff` and
`gaussianBinomial_half_eq_halfQBinomial`, it makes
`cor:halfbase-root-locus` Exact under the canonical rational-polynomial and
rational-root convention. Injective coefficient maps preserve those displayed
multiplicities, but the leaf does not separately classify every root over
every scalar extension.

The arbitrary-space realization leaf proves that an `iIndepFun` family of
unit-interval coordinates, each with the uniform marginal law, has full joint
law `uniformProduct`. It transfers the canonical geometric series law to the
actual pointwise series on any measurable probability space, including
absolute convergence, the interval and exact support, mean one half,
reflection, the conditioning/CDF equations, and the two exterior CDF values.
Its affine fixed-point theorem uses a fresh random variable with the canonical
geometric law that is independent of the head coordinate; this is the precise
independent-copy premise used by the manuscript's head--tail argument.

The regular-central leaf defines `qNumberC` and
`regularCentralQBinomialTerm` and proves
`hasSum_regularCentralQBinomial` for `0 < q < 1`. Its sole parameter premise,
`qPochhammerInfIn ((q : ℂ) ^ (alpha + 1)) ((q : ℂ) ^ 2) ≠ 0`, is exactly
nonvanishing of every generalized-q-number denominator, equivalently
`alpha ≠ -1 - 2*j + 2*pi*I*m/log q` for every natural `j` and integer `m`.
For real `alpha` this excludes precisely the negative odd integers. Even
negative integral parameters are admitted: field-totalized `qGammaC` makes
the displayed quotient zero there, matching the product side, without
asserting holomorphy at a pole.

`GaussianBinomialFixedColumnRate.lean` has no definitions and exactly ten
theorems. Its exhaustive public surface is
`norm_finiteQPochhammerIn_pow_sub_one_le_exp`,
`norm_finiteQPochhammerIn_pow_sub_one_le`,
`norm_finiteQPochhammerIn_self_mul_gaussianBinomial_sub_one_le`,
`norm_gaussianBinomial_sub_inv_finiteQPochhammerIn_le`,
`norm_gaussianBinomial_add_sub_inv_finiteQPochhammerIn_le`,
`tendsto_gaussianBinomial_add_atTop`,
`gaussianBinomial_fixedColumn_relativeError_isBigO`,
`gaussianBinomial_shifted_fixedColumn_relativeError_isBigO`,
`gaussianBinomial_fixedColumn_error_isBigO`, and
`gaussianBinomial_shifted_fixedColumn_error_isBigO`. The first two give the
generic finite-product defect, first by `exp (k * ‖q‖^m) - 1` and then by
`k * exp k * ‖q‖^m`, in a normed commutative ring with multiplicative norm.
The third is the denominator-free relative Gaussian estimate; its `n+k`
specialization is the shifted relative estimate. The next two are the fixed
and shifted nonasymptotic additive errors, the sixth is the shifted limit, and
the final four are the fixed/shifted relative and additive Big-O wrappers.
All ten include `q = 0` at their respective `‖q‖ ≤ 1` or `‖q‖ < 1`
boundaries; no nonzero-nome premise is hidden.

The latest `ThueMorseSparseProuhet` partition tranche adds no definitions and
three theorems to that module's prior twelve-theorem surface, for a current
zero-definition/fifteen-theorem total.  The new declarations are
`sum_thueMorseSign_mul_eq_sum_even_binaryWeight_sub_sum_odd_binaryWeight`,
`sum_even_binaryWeight_affine_pow_eq_sum_odd_binaryWeight_affine_pow`, and
`sum_even_binaryWeight_pow_eq_sum_odd_binaryWeight_pow`.  They give the exact
finite-set parity decomposition, the affine dyadic-block partition, and its
raw-power specialization, respectively.

The exact `JacobiTwoSquareCount` tranche adds no definitions and four public
theorems. `sumSqRep_two_eq_four_mul_twoSquareDivisorSum` proves the full signed
ordered count for every nonzero natural input, and
`sumSqRep_two_eq_four_mul_prod` gives its prime-factor product under the
explicit even-valuation condition at primes congruent to 3 modulo 4.
`theta_sq_eq_chi4_lambert` and `theta_sq_eq_odd_lambert` are unconditional over
every complete normed field for `‖q‖ < 1`. The complex arithmetic core
specializes Ramanujan's bilateral `1psi1` identity, proves absolute
summability for the Lambert rearrangement, reduces the product quotient to the
theta square, and applies convergent-power-series coefficient uniqueness. The
existing conditional declarations in `TwoSquareTheorem` remain reusable
analytic kernels.

The two newest generic theorems are
`deriv_qPochhammerInfIn_ne_zero_of_mul_pow_eq_one`, which gives a nonzero
derivative at every raw factor zero `a*q^j = 1` including `q = 0`, and
`analyticOrderAt_qPochhammerInfIn_of_eq_zero`, which gives analytic order
exactly one at every zero. The `QPochhammerEntire` wrappers retain the older
`complexQPochhammerInf` names by transferring the generic local-uniformity,
entireness, zero-locus, reciprocal-power, and analytic-order results rather
than duplicating their analytic proofs. In `QBinomialTheoremInfinite`,
`finiteQPochhammerIn_zero_left` remains the unique declaration owned by
`GaussianBinomialAtOne` and is imported rather than redeclared. The forward
status ledger is 177 Exact, 81 Partial, 16 None, and 8 interface rows; the
original 191-result pre-Fabius core is 36/29/123/3, and the
completed source concordance records 90 Lean-proved rows, 388 human-proved
frontier rows, 60 not-applicable rows, and 9 conjectures.  Its
immutable source inventory and editorial dispositions remain unchanged; the
generator's current-status projection records the q-Chu, terminating-reversal,
q-Pfaff, two retained Jacobi two-square, partition-symmetry,
Prouhet-partition, arbitrary-space geometric-uniform, and regular-central-sum
advances, together with the fixed-column rate, greater-than-one,
scaled-geometric polynomial-exactness, affine geometric-Prouhet, and
half-base root-simplicity closures.
The basic geometric-uniform row is Exact under its arbitrary-space wording.
The generic Banach-valued barycenter is
`integral_id_weightedUniformDistribution`, and its real geometric
specialization is `integral_id_geometricUniformDistribution_eq_one_half`.
`uniformProcess_hasLaw_uniformProduct` supplies the full-coordinate law
identification for arbitrary `Omega`, and the realization theorem suite proves
every displayed clause with the marginal-law, `iIndepFun`, and
fresh-head-independent-copy hypotheses stated above.
The fourteen-theorem `GaussianBinomialPalindromic` API and five-theorem
`GaussianBinomialPolynomialStructure` API give exact degree,
monicity, constant and top coefficients, reflection, coefficient
palindromicity, and the division-free mean identity over generic commutative
semirings. Its new `coeff_gaussianBinomial_one_of_pos_of_lt` and
`coeff_gaussianBinomial_one` theorems prove the strict-interior coefficient
of `q` is one and give the total formula with every boundary zero. Thus
`cor:positivity`, `thm:qbinom-structure`, and the inverse-source proposition
`prop:gq-positive-palindromic` are Exact. The compound
outer spectral-product theorem remains Partial even though the three-theorem
outer-product leaf proves local-uniform (normal) convergence for every complex
strict contraction, including `q = 0`, together with the nome-`1/4` Rvachev
and bounded-Fabius Fourier specializations. Its named centered/MGF packaging,
exterior reciprocal formula, pole divisor, and zero--pole exchange remain
outside Lean.
The two-definition, twenty-four-theorem `GaussianBinomialCumulants` API now
also exports `eval_one_derivative_derivative_gaussianBinomial_X`,
`twelve_mul_secondMoment_gaussianBinomial_eval_one`, and
`twelve_mul_varianceNumerator_gaussianBinomial_eval_one`. The first isolates
the second falling-factorial moment over a characteristic-zero field for
`k ≤ n`; the latter two clear all divisions and hold over every commutative
semiring, including zero, diagonal, above-row, and positive-characteristic
cases. They concern the universal generating polynomial and do not construct
a probability space.
The six-theorem `GaussianBinomialBounds` surface reuses the stronger
`finiteQPochhammerIn_self_pos` from `GeneralQConditionNumber` and supplies
evaluated reciprocity and the exact finite growth bounds on both sides of `q = 1`; the
two-theorem greater-than-one asymptotic leaf now closes the compound row with
the exact printed fixed-column normalization and the central equivalence.
The new tranche makes `thm:binary-inversions`,
`thm:rectangle-partitions`, `cor:path-area`,
`thm:telescoping-certificate`, `cor:identity-certification`,
`lem:polynomial-identity-principle`, and `cor:safe-specialization` Exact.
`cor:qbinom-inversion-law` becomes Partial because its word count and inversion
distribution are formalized while its identification with the separately
defined random variable is not.
The new status changes record the exact q-exponential eigenfunction and
Jackson integration-by-parts subclaims, and Partial formalizations of the
q-exponential factorization, Jackson fundamental theorem, and theta
quasi-periodicity; the remaining clauses named in their rows stay explicit.
The incoming tail further makes the full elementary Gaussian-polynomial
structure, Jacobi's cubic identity, Jacobi's two-square theorem, and both
two-square Lambert forms Exact, while adding Partial order derivative and
Gaussian-moment rows; the Lambert logarithm row remains Partial with both
displayed derivative formulas now formalized.
The central-reduction row is now Exact through a division-free commutative-ring
identity and its field quotient wrapper; the cyclotomic-factorization row is
Exact over every commutative ring for the factorial form and every integral
domain for the Gaussian form, with the exponent bounds stated explicitly. The
half-base Gaussian valuation row remains Partial: Lean proves the reciprocal
identity and symmetry used in the argument, while the concluding odd-integer
valuation statement is still outside the formal surface.
The Jackson q-beta evaluation and both recurrences are Exact over the stated
real domain `0 < q < 1`, `0 < x`, `0 < y`.  The geometric Newton formula and
its triangular-coefficient corollary are Exact via the generic field-valued
interpolation API and its geometric-grid specialization.
The terminating q-Pfaff--Saalschütz row is Exact under its explicit field and
nonvanishing hypotheses.  The integer-index Gaussian definition, reflection,
two Pascal laws, and reciprocal series are Exact; so are the upper-parameter
and generalized complex-order series on their stated norm domains.  The
separate complex-parameter property and classical-specialization rows remain
None and are not inferred from those series identities.
The two q-Chu--Vandermonde evaluations are Exact for the actual `twoPhiOne`
tsum on their full displayed domain: the second no longer requires `C ≠ 0` or
`(A;q)_n ≠ 0`.  The terminating reversal lemma is also Exact, including the
finite-to-tsum bridge, involutivity of the reflected parameters, and double
application.  The separate proposition deriving the full second evaluation
by reversal remains Partial: its compiled reversal route retains those two
auxiliary hypotheses, while the full-domain proof uses direct finite q-Cauchy;
the manuscript's rational-continuation and commutative-ring extensions remain
unformalized.
The quantum-multinomial row is Exact over every semiring under the stated
pairwise q-commutation laws and commutation of q with each variable; neither
centrality of q nor commutativity of the ambient semiring is claimed.
`GaussianBinomialBounds` owns six theorems. Its finite-product positivity
input `finiteQPochhammerIn_self_pos` is the pre-existing generic declaration
from `GeneralQConditionNumber`, reused through an import and therefore not
counted as a seventh theorem of the bounds leaf.

The complete root block, evaluated q-Lucas theorem, square-free cyclotomic
criterion, and q-Catalan row are Exact. The primitive-root value in the
Babbage corollary is formalized over every integral domain, while its
derivative clause keeps that compound row Partial.

The geometric Newton interpolation and divided-difference rows are Exact. The
Jackson q-beta product/q-gamma evaluation and its two recurrence formulas are
also Exact. The terminating q-Pfaff--Saalschütz sum and quantum multinomial
are Exact, as are the integer-index Gaussian definition and Pascal laws, both
reciprocal-product expansions, the complex upper-parameter series, and the
generalized q-binomial theorem. The remaining complex-Gaussian property and
classical-limit rows stay unformalized.

The retained PDF and the source at commit
`736a241d1a025d64ac73b1573b17a7b3fc02652d` were synchronized at the
historical checkpoint recorded above. The checked working source is newer;
these edits are source-only and make no current source/PDF parity claim.
