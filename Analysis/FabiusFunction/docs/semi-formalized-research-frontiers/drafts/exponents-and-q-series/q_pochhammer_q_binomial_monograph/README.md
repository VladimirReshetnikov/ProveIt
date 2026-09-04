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
environments a reviewed disposition. This immutable merger ledger's current
canonical-status projection is 103 Lean-proved rows, 375 human-proved frontier
result rows, 60 not-applicable rows, and 9 conjecture rows. All five
source-publication trees are
therefore historical inputs preserved by the pinned revision and repository
history, not parallel live packages.

Relative to the two merge sides, that projection unions thirteen incoming
human-to-Lean advances---`cor:geometric-prouhet-affine`,
`cor:halfbase-root-locus`, `cor:partition-symmetries`, `cor:qgreaterone`,
`cor:scaled-geometric-moments`, `cor:thue-morse-prouhet-partition`, the
redirected `prop:fixed-k-limit`, `prop:qF-P-degree-sharp`,
`thm:fixed-column-limit`, `thm:geometric-uniform-basic`,
`thm:regular-central-sum`, `qg:thm-two-square`, and
`qg:cor-two-square-lambert`---with eight local advances:
`cor:qbinom-classical`, `cor:qgamma-theta`, `prop:logder-finite`,
`prop:qbinom-products`, `prop:qderivative-rules`, `prop:qgamma-reflection`,
`thm:q-leibniz`, and `thm:quantum-binomial`. The immutable source fields do
not change. `thm:q-lucas` is deliberately absent from this promotion set and
remains Partial for the polynomial-congruence gap described below.

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
source revisions and repository history preserve their digest receipts.
Checksum manifests have been abolished and must not be recreated.

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

Checksum ledgers have been abolished repository-wide: no `SHA256SUMS*` file
exists or participates in validation for this package or its assets. Deleted
checksum manifests must not be recreated. Historical SHA-256 values recorded
directly in this README and in `PROVENANCE.md` remain provenance receipts for
the named artifacts.

The immediately preceding publication checkpoint was rebuilt on 2026-09-03
from a clean auxiliary state. Exactly three successful
serial `pdflatex -interaction=nonstopmode -halt-on-error` passes produced 386,
395, and 395 pages. During each pass `imakeidx` ran `makeindex` successfully:
164 entries were accepted, none rejected, and the 254-line index was generated
without a warning. The 16,834-line, 837,715-byte source has SHA-256
`4785625c1399558f3ca59481888fc76514e0a327a1faa16945c61851f874f3d5`;
the resulting 2,494,961-byte PDF has SHA-256
`89159b2635f489a42d4c972fac95332808b1d637dee7921085db1ed7d6e055af`.

All 395 pages are A4 at rotation zero, rendered successfully at 24 dpi, and
are nonblank. Title, author, subject, and keyword metadata are present. All 43
font rows are embedded and subset Type 1 fonts; five rows are Libertinus and
none is Type 3. The final log has no TeX or package warning, undefined
reference or citation, duplicate destination, or rerun request. Its sole box
diagnostic is one 32.5659 pt overfull paragraph at source lines 590--598;
physical page 17 was inspected and is readable and unclipped. Physical pages
1, 5, 17, 101, 113, 278, 332, 393, and 395 were visually inspected at 120 dpi,
covering the title, contents, the overfull paragraph, theta and Bailey
material, Gaussian inversion, the formalization appendix, and both ends of
the index. All blocking compilation, index, reference, font, page-render, and
visual gates passed; the one harmless, readable 32.5659 pt overfull paragraph
is the only disclosed exception to otherwise clean diagnostics. This receipt
validates only its named source checkpoint: it predates the `9135` final source
union, so the 395-page PDF is historical and is superseded by the later
historical receipt below. The rigorous current formalization ledger closes at
177 Exact, 82 Partial, 15 None, and 8 interface rows. Files under
`assets/experiments/**/figures/`
remain research figures, not publication manuscripts.

The latest retained publication receipt (2026-09-04) records a historical
16,910-line, 842,514-byte TeX source at SHA-256
`196f219d5e1efba463ebabb69659697b1afb28989ef1a8da6219226d3262ad32`.
Exactly three successful serial halt-on-error passes from absent sidecars ran
390 pages / 2,386,364 bytes → 398 / 2,501,624 → 398 / 2,501,638. During every
pass `makeindex` accepted 164 entries, rejected none, produced 254 lines, and
emitted no warning. The final 398-page, 2,501,638-byte A4 PDF has SHA-256
`e8094b054f52b1fb71c7540f0834155fae0eac17887cb7cac1567848bd65d3b3`.
All 43 font rows are embedded and subset, five are Libertinus, and none is Type
3. Final-log reference/rerun/error checks, metadata, every-page render and
nonblank-text checks, and representative visuals passed; generated sidecars
and forbidden checksum basenames both close at zero. The sole retained
32.5659 pt overfull paragraph at source lines 590--598 is readable and
unclipped; the final log has zero underfull diagnostics. The merged source has
advanced beyond that receipt, so the PDF is historical; a rebuild was then
pending. It is superseded by the current receipt below.

The current synchronized `b899` driver has 17,265 lines and 864,659 bytes, with
SHA-256
`4dd3f7fb22387d8e3d039e8d49cd870a63ebe0881f7f215c7074854825a27bb9`.
Its 14-file recursive TeX closure has 26,762 lines and 1,210,902 bytes, with
digest `b567430fdd64f6d50bd24fcb070216c27f7e3e81e8b0c76c3228767ebdf980c6`.
Exactly three serial halt-on-error passes from absent sidecars ran 397 pages /
2,417,476 bytes → 405 / 2,533,717 → 405 / 2,533,715. During every pass,
`makeindex` accepted 164 entries, rejected none, produced 254 lines, and emitted
no warning. The final 405-page, 2,533,715-byte PDF has SHA-256
`055eb1fc26467857394a5b3bd8cd327f6985ea5d2f966ab5f099ac20bb2b8fb2`.
All 405 pages are A4 at rotation zero, render successfully, and contain
nonblank text. All 43 font rows are embedded and subset, five are Libertinus,
and none is Type 3. Required log, reference/rerun, metadata, visual, cleanup,
and forbidden-basename gates passed. The final log has no vertical box and five
minor horizontal boxes, none above 10.14 pt.

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
The collision-free polynomial API is `nodeNewtonPoly`,
`nodeNewtonPoly_succ`, `eval_nodeNewtonPoly`,
`degree_nodeNewtonPoly_lt`, `nodeNewtonPoly_eq_interpolate`,
`eq_nodeNewtonPoly_of_eval_eq`, and `coeff_nodeNewtonPoly_self`.
`newtonInterpolant` and the six `newtonPoly_*` theorem aliases preserve the
incoming compatibility surface; the coefficient and geometric-grid results
retain their established names.
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
recurrence uniqueness, and rational-identity specialization. The historical
dyadic/finite-prefix facade audit contains 933 modules and 11,695 public
declarations, with no documentation gaps. The merged upstream
`DyadicBoundaryIdentity.lean` and
`FinitePrefixThueMorseCollapse.lean` modules add two modules and ten public
declarations beyond the historical reciprocity checkpoint 931/11,685. The
incoming union adds one module and fourteen public declarations: the new
zero-definition/six-theorem `ProuhetBaseTwoBridge.lean` module, one theorem
added to `DyadicBoundaryIdentity.lean`, and seven theorems added to
`ThueMorseNewmanSelfSimilarity.lean`. This made 934 modules and 11,709 public
declarations an explicitly historical post-Prouhet checkpoint. Subsequent
source-only transseries/Catalan and Thue--Morse additions made 943/11,791 the
next historical checkpoint. The finalized one-definition/eleven-theorem
`TransseriesFlat.lean` module and three integer-zpow theorems in
`TransseriesDifferentialBlock.lean` gave the historical facade audit 944 modules and
11,806 public declarations; the merged live census is 970/12,056. Ten declarations come from the sibling
`FabiusFunction.GeometricRichardsonGenerating` module (three definitions and
seven theorems), whose exact comb-manuscript crosswalk is
`Fabius.geometricLagrangeRichardson_generating`; it does not change this
monograph's forward-status inventory or make its retained PDF current.
The other three new declarations are the explicit second-derivative,
division-free raw-second-moment, and division-free variance-numerator theorems
in `GaussianBinomialCumulants`; they strengthen the already-Exact
`thm:qbinom-moments` row without changing its disposition.
The three declarations beyond the historical 905-module/11,458-declaration
checkpoint form the one-definition, two-theorem inner complex moment-product
leaf described below.  After the merged-main pre-local checkpoint of 919
modules and 11,569 declarations, the exterior reciprocal-germ companion
produces the historical 920/11,572 checkpoint, and the sharp-degree 0+3 leaf
produces the historical 921/11,575 checkpoint.
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
expansions remain open. That sibling promotion produced the 903/11,448
checkpoint and changed none of the q-series forward-status or source-
concordance totals. The five fixed-column declarations later produced local
checkpoint `581bf` at 903/11,453. The Lambert crosswalk is outside the q-series
publication and is not rendered by its exact `581bf` receipt.

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
`geometricUniformComplexMomentProduct`, and exactly three public theorems,
`hasProdLocallyUniformly_geometricUniformComplexMomentProduct`,
`differentiable_geometricUniformComplexMomentProduct`, and
`geometricUniformMomentPolynomial_eval₂_eq_complexMomentProduct_taylorCoefficient`.
For every complex `q` with `‖q‖ < 1`, including `q = 0`, these declarations
give the manuscript's actual infinite product, its locally uniform convergence
and complex differentiability on the whole plane, and the exact
finite-q-Pochhammer normalization of its Taylor coefficient.  Thus the inner
complex product/coefficient bridge is exact.  The subsequent
`GeometricUniformExteriorComplexMomentGerm.lean` leaf
has one definition, `geometricUniformExteriorComplexMomentGerm`, and exactly
two public theorems, `analyticAt_geometricUniformExteriorComplexMomentGerm`
and
`geometricUniformMomentPolynomial_eval₂_eq_exteriorComplexMomentGerm_taylorCoefficient`.
For every complex `1 < ‖q‖`, it constructs the manuscript's actual reciprocal
germ, proves analyticity at zero, and identifies the same normalized Taylor
coefficient.  The final `GeometricUniformMomentRatFunc.lean` leaf has one
definition, `geometricUniformMomentRatFunc`, and exactly four theorems:
`qFactorial_mul_geometricUniformMomentRatFunc`,
`eval_geometricUniformMomentRatFunc_eq_complexMomentProduct_taylorCoefficient`,
`eval_geometricUniformMomentRatFunc_eq_exteriorComplexMomentGerm_taylorCoefficient`,
and `eval_geometricUniformMomentRatFunc_one`.  It packages the inner and
exterior coefficients as the single rational function
`a_n(q) = P_n(q) / [n]_q!`, proves the global q-factorial clearing identity,
specializes safely to both analytic regimes, and treats `q = 1` through
`[n]_1! = n!` rather than totalized `0 / 0`.  It makes no `RatFunc.eval` claim
at a genuine reduced-denominator zero.  Consequently the compound
`thm:qF-moment-polynomial` is Exact.  The subsequent
`GeometricUniformMomentReciprocity.lean` leaf has one definition,
`geometricUniformComplexMomentGerm`, and exactly five theorems:
`geometricUniformComplexMomentGerm_of_norm_lt_one`,
`geometricUniformComplexMomentGerm_of_one_lt_norm`,
`analyticAt_geometricUniformComplexMomentGerm`,
`geometricUniformComplexMomentGerm_reciprocity`, and
`geometricUniformComplexMomentGerm_moment_convolution`.  It identifies the
inner and exterior branches of the combined germ, proves analyticity at zero
off the unit circle, and, when `q != 0` and `‖q‖ != 1`, proves
`M_q(z) * M_(q⁻¹)(-z) = 1` locally as an `EventuallyEq` and proves the
equivalent exact binomial convolution of every iterated derivative.  Hence
`thm:qF-reciprocity` is Exact.  No global pointwise identity across genuine
zeros of the inner product is claimed.  The broader
`thm:geometric-uniform-mgf` remains Partial at its unbundled public direct
dilation and coefficient recurrence, formal-power-series uniqueness, bundled
genuine-MGF/characteristic-function identification, and root-of-unity pole
classification;
`cor:qF-halfbase-dictionary` remains Partial at its still-missing endpoint
formula even though the half-base polynomial and genuine-MGF normalization are
now available.  The exhaustive zero-definition/three-theorem
`GeometricUniformMomentPolynomialDegree.lean` leaf consists of
`coeff_geometricUniformMomentPolynomial_choose_two`,
`coeff_geometricUniformMomentPolynomial_choose_two_sub_one`, and
`geometricUniformMomentPolynomial_natDegree_eq`.  It proves
`[q^(n.choose 2)] P_n = bernoulli' n/n! = (-1)^n B_n/n!`, for `n >= 2` the coefficient
`[q^(n.choose 2-1)] P_n = -bernoulli' n/n! + bernoulli' (n-1)/(2*(n-1)!)`,
and exact degree `n.choose 2` when `n=1` or `n` is even and
`n.choose 2-1` otherwise.  Therefore `prop:qF-P-degree-sharp` is Exact; these
are algebraic polynomial statements with no analytic or root-of-unity
hypothesis.

The base 904/11,457, real-bridge 905/11,458, inner-complex 906/11,461, and
pre-merge exterior-branch 907/11,464 counts remain historical checkpoints.
The actual merged-main pre-local checkpoint is 919/11,569; the exterior leaf
gives the next historical checkpoint 920/11,572 without a status move; and the
sharp-degree leaf gives the historical 921/11,575 checkpoint. Subsequent
Laurent and finite-prefix tranches give the historical 922/11,582 and
923/11,610 checkpoints, respectively.  The RatFunc leaf gives the historical
924/11,615 checkpoint.  After the unrelated one-definition/one-theorem
`RvachevLegendreBiorthogonality.lean` leaf and the following two declarations
in the existing `ProbabilityLaplaceMoments.lean` module are adjoined, the
historical facade census reached 925/11,619.  Subsequent source-only tranches,
including `GeometricUniformMomentReciprocity.lean`, give the historical
reciprocity checkpoint 931/11,685.  The subsequently merged upstream
`DyadicBoundaryIdentity.lean` and `FinitePrefixThueMorseCollapse.lean` modules
add two modules and ten public declarations, making the historical
dyadic/finite-prefix census 933/11,695.  The incoming union adds one module and
fourteen public declarations: the new zero-definition/six-theorem
`ProuhetBaseTwoBridge.lean` module, one theorem added to
`DyadicBoundaryIdentity.lean`, and seven theorems added to
`ThueMorseNewmanSelfSimilarity.lean`.  This made 934/11,709 an explicitly
historical post-Prouhet checkpoint.  Subsequent source-only
transseries/Catalan and Thue--Morse additions made 943/11,791 the next
historical checkpoint.  The finalized one-definition/eleven-theorem
`TransseriesFlat.lean` module and three integer-zpow theorems in
`TransseriesDifferentialBlock.lean` gave the historical census 944/11,806; the merged live census is 970/12,056.
The existing `ProbabilityLaplaceMoments.lean` module now adds exactly the two
theorems
`weightedSumDistribution_real_Ici_eq_rvachevUp_of_nonneg` and
`integral_pow_weightedSumDistribution_eq_mul_intervalIntegral_rvachevUp`.
The first combines the strict-Ioi survival law with atomlessness to identify
the manuscript's closed tail `P(X >= t)` on the full nonnegative ray; the
second gives `E[X^n] = n * integral_0^1 t^(n-1) up(t) dt` for every natural
`n >= 1`, with the expectation taken over the full weighted-sum law. Together
with `rvachevUp_eq_fabiusReal_one_sub_abs` and
`rvachevUp_eq_one_sub_fabiusReal_of_nonneg`, these declarations make
`prop:up-tail` and `cor:up-moments` Exact without changing any broader row.
The forward ledger is 181 Exact / 79 Partial / 14 None / 8 N/A, the relevant
Dyadic Gaussian--Thue--Morse chapter is 13/43/0/0, and the source concordance
is 103 Lean-proved / 375 human-proved frontier / 60 N/A / 9 conjectures.
The zero-definition/one-theorem `HalfQBinomialRootSimplicity.lean` leaf exports
`halfQBinomial_sum_rootMultiplicity_two_pow`; composed with
`halfQBinomial_sum_eq_zero_iff` and
`gaussianBinomial_half_eq_halfQBinomial`, it makes
`cor:halfbase-root-locus` Exact under the canonical rational-polynomial and
rational-root convention: all rational roots are the displayed `2^j`, and
each has multiplicity one. Injective scalar extension preserves those
displayed multiplicities, but the leaf does not package an all-roots
classification over every extension field. `cor:qbinom-inversion-law`
remains Partial.
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

The one-definition/seventeen-theorem arbitrary-space realization leaf has the
exhaustive public surface `geometricUniformRealization`,
`geometricUniformRealization_eq_tsum`, `geometricUniformRealization_split`,
`uniformProcess_hasLaw_uniformProduct`,
`weightedUniformSeries_hasLaw_of_iIndep_uniform`,
`geometricUniformRealization_hasLaw`,
`summable_norm_geometricUniformRealization_terms`,
`geometricUniformRealization_mem_Icc`,
`map_geometricUniformRealization_support_eq_Icc`,
`integral_geometricUniformRealization_eq_one_half`,
`one_sub_geometricUniformRealization_hasLaw`,
`geometricUniformRealization_identDistrib_one_sub`,
`affine_uniform_geometric_hasLaw`,
`geometricUniformRealization_identDistrib_affine`,
`measureReal_geometricUniformRealization_le_eq_cdf`,
`measureReal_geometricUniformRealization_le_eq_integral`,
`measureReal_geometricUniformRealization_le_eq_zero_of_nonpos`, and
`measureReal_geometricUniformRealization_le_eq_one_of_one_le`. It proves that
an `iIndepFun` family of unit-interval coordinates, each with the uniform
marginal law, has full joint law `uniformProduct`, and transfers the canonical
geometric series law to the actual pointwise series on any measurable
probability space. The definition and literal tsum identity are unconditional;
the coordinate-process law needs only the stated marginal laws and `iIndepFun`,
and the Banach-valued weighted transfer uses summability of the weight norms.
Pointwise splitting, geometric law transfer, absolute convergence, mean, and
reflection require `|q| < 1`; interval membership, exact support, and the two
exterior CDF values use `0 <= q < 1`; the conditioning integral uses the strict
probability range `0 < q < 1`. Its affine fixed-point theorems also require a
probability measure and a fresh canonical-law copy independent of the head
coordinate. No conclusion is promoted to the boundary `|q| = 1`.

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
than duplicating their analytic proofs. The public
`complexQPochhammerInf_eq_qPochhammerInfIn` bridge is unconditional for every
complex parameter and nome; it is a definitional equality, not a convergence
claim. In `QBinomialTheoremInfinite`,
`finiteQPochhammerIn_zero_left` remains the unique declaration owned by
`GaussianBinomialAtOne` and is imported rather than redeclared. The forward
status ledger is 181 Exact, 79 Partial, 14 None, and 8 interface rows; the
original 191-result pre-Fabius core is 36/29/123/3, and the
completed source concordance records 103 Lean-proved rows, 375 human-proved
frontier rows, 60 not-applicable rows, and 9 conjectures.  Its
immutable source inventory and editorial dispositions remain unchanged; the
generator's current-status projection records the q-Chu, terminating-reversal,
q-Pfaff, two retained Jacobi two-square, partition-symmetry,
Prouhet-partition, arbitrary-space geometric-uniform, and regular-central-sum
advances, together with the fixed-column rate, greater-than-one,
scaled-geometric polynomial-exactness, affine geometric-Prouhet, and
half-base root-simplicity closures, together with the common rational
moment-coefficient closure.
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

The complete root block, square-free cyclotomic criterion, and q-Catalan row
are Exact. The evaluated primitive-root q-Lucas identity is formalized over
every integral domain, but `thm:q-lucas` remains Partial because no Lean
declaration lifts it to the manuscript's polynomial congruence modulo
`Φ_d(q)`. The primitive-root value in the Babbage corollary is formalized over
every integral domain, while its derivative clause keeps that compound row
Partial.

The geometric Newton interpolation and divided-difference rows are Exact. The
Jackson q-beta product/q-gamma evaluation and its two recurrence formulas are
also Exact. The terminating q-Pfaff--Saalschütz sum and quantum multinomial
are Exact, as are the integer-index Gaussian definition and Pascal laws, both
reciprocal-product expansions, the complex upper-parameter series, and the
generalized q-binomial theorem. The remaining complex-Gaussian property and
classical-limit rows stay unformalized.

The retained 395-page PDF and source SHA-256
`4785625c1399558f3ca59481888fc76514e0a327a1faa16945c61851f874f3d5`
remain synchronized historical evidence for the checkpoint recorded above.
The retained 398-page PDF is likewise a historical 2026-09-04 receipt. The
current merged source and 405-page PDF are synchronized by the `b899` receipt
above.
