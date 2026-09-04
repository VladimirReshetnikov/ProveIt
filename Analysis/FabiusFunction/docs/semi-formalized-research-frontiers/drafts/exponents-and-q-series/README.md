# Exponents and q-series

There are two live document packages:

- [`q_pochhammer_q_binomial_monograph/`](q_pochhammer_q_binomial_monograph/)
  is the single canonical synthesis of forward q-series and branch-aware
  inverse-q theory.
- [`geometric_q_fabius_frontiers/`](geometric_q_fabius_frontiers/) is the
  single consolidated frontier volume for the geometric q-deformation of the
  Fabius–Rvachev system: exponent sequences, sinc products, atomic splines,
  and parameter deformations.

## The 2026-09-02 consolidation

The two former subgroups `q-fabius-parameter-deformations/` and
`geometric-sinc-and-exponent-families/` no longer exist. Their six standalone
documents were merged into `geometric_q_fabius_frontiers/` and deleted from the
working tree; git history is the archive, and the volume's own provenance
section pins every absorbed snapshot by SHA-256.

| Former package | Now |
| --- | --- |
| `geometric-sinc-and-exponent-families/Exponents_and_q_Series_Frontiers/` | Parts I–VII (the volume's spine; renamed in place, assets retained) |
| `geometric-sinc-and-exponent-families/Fabius_Rvachev_Frontier_Report/` | Part VIII |
| `geometric-sinc-and-exponent-families/Cyclotomic_q_Fabius_Rvachev_Frontier/` | Part IX |
| `q-fabius-parameter-deformations/fabius_q_frontiers_report/` | Part X |
| `q-fabius-parameter-deformations/Continuous_Parameter_Edgeworth_and_q_Gevrey_Frontier/` | Part XI |
| `q-fabius-parameter-deformations/Fabius_Flat_Parameter_Response_Dynamics/` | Part XII |

The consolidation added a new **Part 0, Common Framework**, written for the
merge rather than absorbed from any source. The six reports had fixed the same
objects independently and inconsistently — three affine normalizations of one
random variable, two sinc arguments, and the letters `X_q` and `Y_q` denoting
different objects in different reports — so Part 0 states the shared
definitions, transforms, and cumulant identities once with complete proofs and
tabulates the exact dictionary from each part's local convention to the
canonical one. Each absorbed part keeps its own mathematics; what it no longer
carries is its own re-derivation of the shared layer.

Every absorbed report's verification material — scripts, data tables, and
figures — is preserved under `geometric_q_fabius_frontiers/assets/`.

The accepted first-merge receipt for `geometric_q_fabius_frontiers/`, now
retained as historical provenance, is root
`27624L/1273010B/0839b42a3fb055d860b8e8a3d1ff5e84c2f4addce314d04707c5a067e81553d9`,
exact seven-file aggregate
`27997L/1288647B/18c4c6607e9b7564909ca7e647152a26e517f54d5007e157265b3f61adf8e4f0`,
passes `387/404/404`, PDF
`404pp/8341830B/a083b130a1568dc37af824294b033485f82c97dbeb30a4c4de4d463d04e99530`,
and final log
`2557L/114343B/4de474675a2dcde519c36ff1ac7067717c64b60b92bd40b999d0d117ba1f8df6`.
All prohibited-log and visual gates were clean at that checkpoint; all 404 pages are A4 at
rotation zero; the PDF is unencrypted PDF 1.5; all 43 font rows are embedded
and subset, including 11 Libertinus rows; Type-3 has zero rows; and checksum
basenames and PDF/source references are absent.
The later d130 geometric-q receipt in the authoritative register is also now\nhistorical because the merged source changed; a fresh render is pending.\n\nThe historical `2d434eec` whole-root receipt for
`geometric_q_fabius_frontiers/` is a 27,520-line, 1,266,515-byte source with
SHA-256 `8292f10862334cb809139259eeb4906bb14f517d41b9600c9b7ad53bb21525b1`.
Three passes at 385/402/402 pages produced the 402-page, 8,332,886-byte A4 PDF
with SHA-256
`d47431e4d3e721fccf12f90226db77f1898e44b477878954acca3a6e90127cf4`;
the final 2,557-line, 114,331-byte log has SHA-256
`4d6f8c7974def4a3f9e6bc8ccdffefc3eef7ca8cb7c2f0145a075f95b82ff45e`.
All documented log, page, font, Type-3, extraction, and visual gates passed
at that revision. This tuple, the first-merge receipt above, and the later d130
and incoming receipts remain explicit history; none renders the merged source.

The detailed package record below still describes the six absorbed documents
individually; those entries are retained as provenance, and their directory
paths are dead. Resolve any path through the table above or through the
[draft manifest](../MANIFEST.md).

The former `q-pochhammer-and-inversion/` locations are recorded in pinned
history; no live index or package remains at that path. Every live package
appears exactly once. The former three
general-q-series guides, forward q-Pochhammer/q-binomial monograph, and
inverse-q synthesis have been dispositioned into
[`q_pochhammer_q_binomial_monograph/`](q_pochhammer_q_binomial_monograph/).
Their earlier names, arrival hashes, and publication facts remain provenance,
not parallel live documents. The most recent pre-`d8b` canonical publication
receipt names a
16,834-line, 837,715-byte TeX source (SHA-256
`d8f730b8eb6602d4d16112aea77a3e67dfbeadf46bcd28c1cdf3b12450b7d4fb`)
and its 395-page, 2,494,949-byte PDF (SHA-256
`5d25df07e6df1cd32118ee87e64c1cc54ad32da7c578a182231f98dd9fee9d5c`).
Its exact final three-pass cycle and publication gates were clean for that
named source. That artifact remains a historical receipt. Package-local checksum ledgers have been
abolished and must not be regenerated.

The latest retained q-series receipt (2026-09-04) records a historical 16,910-line,
842,514-byte TeX source at SHA-256
`196f219d5e1efba463ebabb69659697b1afb28989ef1a8da6219226d3262ad32`.
Exactly three successful serial halt-on-error passes from absent sidecars ran
390 pages / 2,386,364 bytes → 398 / 2,501,624 → 398 / 2,501,638; every pass's
index run accepted 164 entries, rejected none, produced 254 lines, and emitted
no warning. The final 398-page, 2,501,638-byte A4 PDF has SHA-256
`e8094b054f52b1fb71c7540f0834155fae0eac17887cb7cac1567848bd65d3b3`.
All 43 font rows are embedded and subset, five are Libertinus, and none is Type
3. Final-log reference/rerun/error checks, metadata, every-page render and
nonblank-text checks, and representative visuals passed; generated sidecars
and forbidden checksum basenames both close at zero. The sole retained
32.5659 pt overfull paragraph at source lines 590–598 is readable and
unclipped; the final log has zero underfull diagnostics. The merged source has
advanced beyond this receipt, so the retained PDF is historical and a rebuild
was then pending; the historical `b899` receipt below is the retained historical
build receipt.

The historical synchronized `b899` q-series driver has 17,265 lines and
864,659 bytes (SHA-256
`4dd3f7fb22387d8e3d039e8d49cd870a63ebe0881f7f215c7074854825a27bb9`),
and its 14-file recursive TeX closure has 26,762 lines and 1,210,902 bytes
(digest `b567430fdd64f6d50bd24fcb070216c27f7e3e81e8b0c76c3228767ebdf980c6`).
Three passes ran 397 pages / 2,417,476 bytes → 405 / 2,533,717 → 405 /
2,533,715; every pass's index run accepted 164 entries, rejected none, produced
254 lines, and emitted no warning. The final 405-page PDF has SHA-256
`055eb1fc26467857394a5b3bd8cd327f6985ea5d2f966ab5f099ac20bb2b8fb2`.
All 405 pages are A4 at rotation zero, render with nonblank text, and use 43
embedded/subset font rows (five Libertinus, no Type 3). Metadata, log,
representative-visual, cleanup, and forbidden-basename gates passed; the final
log has five minor horizontal boxes, none above 10.14 pt, and no vertical box.

The merged source incorporates the later five-theorem

The local first-merge 401-page and d130 402-page receipts remain additional
historical checkpoints; their exact tuples are retained in the canonical
package README and provenance record. The merged q-series source is newer than
all of these artifacts, so a synchronized render is pending.
`QPochhammerEntire.lean`, `QPochhammerInfinite.lean`, and
`QPochhammerDissection.lean` surfaces, together with the subsequent q-series
module tranches and the zero-definition, three-theorem
`GeometricPochhammerNormalConvergence.lean` leaf, in its formalization
crosswalk. That source is a source-only successor to the fresh artifact receipt
and requires a later synchronized three-pass build. Retained PDFs under its `assets/` tree are
research figures, not alternate manuscript renderings. The Lean audit at the
historical dyadic/finite-prefix checkpoint contains 933 facade-reachable
modules and 11,695 public declarations, with no missing module headers or
declaration documentation.  The merged upstream
`DyadicBoundaryIdentity.lean` and `FinitePrefixThueMorseCollapse.lean` modules
account for the two-module/ten-declaration increase beyond the historical
reciprocity checkpoint 931/11,685.  The incoming union adds one module and
fourteen public declarations: the new zero-definition/six-theorem
`ProuhetBaseTwoBridge.lean` module, one theorem added to
`DyadicBoundaryIdentity.lean`, and seven theorems added to
`ThueMorseNewmanSelfSimilarity.lean`.  This made 934 modules and 11,709
public declarations an explicitly historical post-Prouhet checkpoint.
Subsequent source-only transseries/Catalan and Thue--Morse additions made
943/11,791 the next historical checkpoint.  The finalized one-definition/
eleven-theorem `TransseriesFlat.lean` module and three integer-zpow theorems
in `TransseriesDifferentialBlock.lean` gave the historical Lean audit 944 modules
and 11,806 public declarations; the merged live census is 988/12,257.

The sibling source-only `FabiusFunction.GeometricRichardsonGenerating` module
(three definitions and seven theorems) does not change this q-series package's
forward-status totals.
Its exact comb crosswalk is
`Fabius.geometricLagrangeRichardson_generating`, with
`Fabius.hasSum_geometricLagrangeRichardson_mul_pow` as the analytic companion.
No retained PDF in this group rendered that unrelated promotion at its initial
source-only checkpoint. The historical q-series and standalone geometric-q
renders include the post-union crosswalk. Their 401/402/405-page q-series and
402/403/404/405/406-page geometric-q receipts remain history; both merged
sources now require fresh synchronized renders.
The additional three declarations are the second-derivative, raw-second-moment,
and variance-numerator identities in `GaussianBinomialCumulants`; they
strengthen the existing q-series moment crosswalk without changing its status.
That module's exhaustive public surface is two definitions and twenty-four
theorems. The next five declarations belong to the one-definition,
twenty-seven-theorem `QBinomialTheoremInfinite` surface and prove the effective
fixed-column limits and geometric rates; they are the only part of this recent
repository-wide sequence that changes this package's forward-status totals.

That repository-wide census includes a sibling, source-only Lambert-W
promotion rather than a new q-series result. Its exhaustive module counts are
`LambertWBranchPairing.lean` (0 definitions + 7 theorems),
`LambertWGapBijection.lean` (4 + 16), and
`LambertWBranchSymmetry.lean` (0 + 9), followed by
`LambertWBranchGapBernoulli.lean` (0 + 5). Their exhaustive four-module union
is 4 definitions + 37 theorems, 41 public declarations. The first three prove,
only for the
open two-branch domain `(-exp(-1), 0)`, the exact gap parametrization and its
inverse bijection, the `t = exp(delta) > 1` formulas, and the exact
ratio/sum/product laws with strict sum and product bounds. The last module's
exhaustive public surface is
`summable_norm_bernoulli_mul_pow_div_factorial`,
`summable_bernoulli_mul_pow_div_factorial_iff`,
`hasSum_bernoulli_mul_pow_div_factorial`,
`hasSum_bernoulli_mul_pow_div_factorial_complex_iff`, and
`principalLambertW_lowerLambertW_eq_bernoulliSeries`: real absolute
convergence for `|z| < 2*pi`, complex summability exactly when
`‖z‖ < 2*pi` (hence divergence on and outside the boundary), the real quotient
sum for nonzero `z`, the actual complex `HasSum` value
`(complexExpm1Div z)⁻¹` throughout the open disk, and the paired branch series
on the same strict x-domain when the positive gap is below `2*pi`. Thus the
radius/boundary clause, Guide label `eq:pair-Bernoulli-general`, and the
canonical-removable reading of `eq:bernoulli-gen` are Exact. Here
`complexExpm1Div 0 = 1` and it equals `(exp z - 1) / z` away from zero; this
does not assert the literal totalized quotient at zero or holomorphy of a named
sum function. Higher or full Puiseux/logarithmic branch expansions remain open.
No retained PDF in this group rendered this unrelated promotion at its original
source-only checkpoint. The accepted first-merge Lambert receipt, now
historical, is root
`4961L/183269B/83301b4c66660713a70974263b6f191ea01f9ed8f5ae228495f644887b616568`,
two-file aggregate
`5245L/195104B/25141b9ee818b20ddf8349d88ec4f2dc977ff0ab35ca34e62cd62da64c2cf06a`,
passes `68/70/70`, PDF
`70pp/966637B/6c150ff18889030345de3e1a8581d5ea0ac75789a9720c1d5164ed4e7ec4b7fb`,
and log
`1574L/57800B/9f995a50e3ab25256083edee745a1889027787194e3b3c6d1f12f60bf687145c`;
all recorded gates passed at that checkpoint. The later d130 Lambert receipt in the authoritative register and the incoming\n`b899` receipt are also historical after the merged Guide source changed; a\nfresh synchronized render is pending. The
historical `2d434eec` Lambert Guide receipt is preserved as history. Its
completed checkpoint is `217a6b9` at
903/11,448; the later local fixed-column commit `581bf` is 903/11,453.

The current q-series tranche starts with `GeometricUniformMomentPolynomial.lean`, with the one
definition `geometricUniformMomentPolynomial` and the eight theorems
`geometricUniformMomentPolynomial_zero`,
`geometricUniformMomentPolynomial_succ`,
`geometricUniformMomentPolynomial_natDegree_le`,
`geometricUniformMomentPolynomial_eval_zero`,
`geometricUniformMomentPolynomial_one`,
`geometricUniformMomentPolynomial_two`,
`geometricUniformMomentPolynomial_three`, and
`geometricUniformMomentPolynomial_four`.  This exhaustive API proves the
recursive rational polynomial, zeroth value, residual-product recurrence,
triangular degree bound, specialization at zero, and the first four
nonconstant examples.  The downstream
`GeometricUniformMomentPolynomialBridge.lean` leaf has zero definitions and
the single public theorem
`geometricUniformMomentPolynomial_eval₂_eq_mgf_taylorCoefficient`: for every
real `|q| < 1`, including `q = 0` and negative `q`, it proves the exact
finite-q-Pochhammer normalization by the Taylor coefficient of the genuine
geometric-uniform MGF.  The subsequent
`GeometricUniformComplexMomentProduct.lean` leaf has the one definition
`geometricUniformComplexMomentProduct` and exactly three theorems,
`hasProdLocallyUniformly_geometricUniformComplexMomentProduct`,
`differentiable_geometricUniformComplexMomentProduct`, and
`geometricUniformMomentPolynomial_eval₂_eq_complexMomentProduct_taylorCoefficient`.
For every complex strict contraction, including `q = 0`, this exhaustive 1+3
surface gives the actual manuscript product, locally uniform convergence and
complex differentiability on the whole plane, and the exact normalized
Taylor-coefficient bridge.
The inner complex product/coefficient claim is therefore exact.  The following
`GeometricUniformExteriorComplexMomentGerm.lean` leaf has the one definition
`geometricUniformExteriorComplexMomentGerm` and exactly two theorems,
`analyticAt_geometricUniformExteriorComplexMomentGerm` and
`geometricUniformMomentPolynomial_eval₂_eq_exteriorComplexMomentGerm_taylorCoefficient`.
For every complex `1 < ‖q‖`, it constructs the actual reciprocal product germ,
proves its analyticity at zero, and gives the same normalized Taylor-coefficient
identity.  The final `GeometricUniformMomentRatFunc.lean` leaf has one
definition, `geometricUniformMomentRatFunc`, and exactly four theorems:
`qFactorial_mul_geometricUniformMomentRatFunc`,
`eval_geometricUniformMomentRatFunc_eq_complexMomentProduct_taylorCoefficient`,
`eval_geometricUniformMomentRatFunc_eq_exteriorComplexMomentGerm_taylorCoefficient`,
and `eval_geometricUniformMomentRatFunc_one`.  It packages the common
coefficient as `P_n/[n]_q!` in `RatFunc ℚ`, proves the global q-factorial
clearing identity, safely specializes to both analytic regimes, and treats
`q = 1` via `[n]_1! = n!`, without evaluating at genuine reduced-denominator
zeros.  Under the strict whole-label policy, this makes
`thm:qF-moment-polynomial` Exact.
The subsequent `GeometricUniformMomentReciprocity.lean` leaf has one
definition, `geometricUniformComplexMomentGerm`, and exactly five theorems:
`geometricUniformComplexMomentGerm_of_norm_lt_one`,
`geometricUniformComplexMomentGerm_of_one_lt_norm`,
`analyticAt_geometricUniformComplexMomentGerm`,
`geometricUniformComplexMomentGerm_reciprocity`, and
`geometricUniformComplexMomentGerm_moment_convolution`.  It joins the inner
product and exterior reciprocal into one germ, proves analyticity at zero off
the unit circle, and, for `q != 0` and `‖q‖ != 1`, proves
`M_q(z) * M_(q⁻¹)(-z) = 1` as a local `EventuallyEq` together with its exact
all-order binomial derivative convolution.  Thus `thm:qF-reciprocity` is
Exact.  The pointwise equality is intentionally local because Lean's total
inverse cannot turn a genuine zero of the inner product into a global
reciprocal identity.
`thm:geometric-uniform-mgf` remains Partial at its public direct dilation and
coefficient recurrence, formal-power-series uniqueness, bundled genuine-MGF/
characteristic-function identification, and root-of-unity pole classification.
The exhaustive 0+3
`GeometricUniformMomentPolynomialDegree.lean` leaf consists of
`coeff_geometricUniformMomentPolynomial_choose_two`,
`coeff_geometricUniformMomentPolynomial_choose_two_sub_one`, and
`geometricUniformMomentPolynomial_natDegree_eq`.  It proves the leading
coefficient `bernoulli' n/n! = (-1)^n B_n/n!`, for `n >= 2` the subleading coefficient
`-bernoulli' n/n! + bernoulli' (n-1)/(2*(n-1)!)`, and exact degree
`n.choose 2` for `n=1` or even `n` and `n.choose 2-1` otherwise.  Hence
`prop:qF-P-degree-sharp` is Exact, with no analytic or root-of-unity
hypothesis.

The base 904/11,457, real-bridge 905/11,458, inner-complex 906/11,461, and
pre-merge exterior-branch 907/11,464 counts remain historical checkpoints.
The actual merged-main pre-local checkpoint is 919/11,569; the exterior leaf
gives the next historical 920/11,572 checkpoint; and the sharp-degree leaf
gives the historical 921/11,575 checkpoint.  The sibling
`RvachevLaurentLeading.lean` leaf (one definition and six theorems) then gives
922/11,582 and makes `is:p2:thm:Laurent-leading` Exact with the manuscript's
centered-MGF normalization and a punctured Laurent limit.  The sibling
`FinitePrefixAppellRecovery.lean` leaf (eleven definitions and seventeen
theorems) gives the historical 923/11,610 checkpoint and makes
`is:p2:thm:finite-prefix-expansion` and `is:p2:thm:exact-recovery` Exact as
finite rational identities; it adds no analytic-MGF convergence or universal
fixed-evaluation-point degree claim.  The RatFunc leaf gives the historical
924/11,615 checkpoint.  After adjoining the unrelated one-definition/
one-theorem `RvachevLegendreBiorthogonality.lean` leaf and the following two
declarations in the existing `ProbabilityLaplaceMoments.lean` module, the
historical census reached 925/11,619.  Subsequent source-only tranches,
including the reciprocity leaf above, give the historical reciprocity
checkpoint 931/11,685.  The subsequently merged upstream
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
`TransseriesDifferentialBlock.lean` gave the historical census 944/11,806; the merged live census is 988/12,257.
That existing module adds
`weightedSumDistribution_real_Ici_eq_rvachevUp_of_nonneg` and
`integral_pow_weightedSumDistribution_eq_mul_intervalIntegral_rvachevUp`.
Atomlessness identifies the strict and closed tails, and the second theorem
is the exact full-law moment formula for every natural `n >= 1`; together
with the existing global up/Fabius identities, these promote `prop:up-tail`
and `cor:up-moments` to Exact.  The q ledger is 181/79/14/8, its relevant
Dyadic Gaussian--Thue--Morse chapter is 13/43/0/0, and the source projection
is 103/375/60/9. `thm:q-lucas` remains Partial because Lean proves only its
evaluated primitive-root identity, not the polynomial congruence modulo
`Phi_d(q)` or its minimal-polynomial lift. The zero-definition/one-theorem
`HalfQBinomialRootSimplicity.lean` leaf exports
`halfQBinomial_sum_rootMultiplicity_two_pow`; with the complete rational
root classification `halfQBinomial_sum_eq_zero_iff`, it makes
`cor:halfbase-root-locus` Exact under the canonical rational-polynomial
convention. `cor:qbinom-inversion-law` remains Partial. The facade-reachable
zero-definition/two-theorem
`GaussianBinomialGreaterOneAsymptotics.lean` leaf has the declarations
`gaussianBinomial_gt_one_fixedColumn_relativeError_isBigO` and
`gaussianBinomial_gt_one_central_isEquivalent`. Together with
`gaussianBinomial_inv`, they make `cor:qgreaterone` Exact. For real `q > 1`, they
use exactly the normalized fixed-column error
`(q⁻¹;q⁻¹)_k (q^(k*(n-k)))⁻¹ [n,k]_q - 1` with
`O((q⁻¹)^(n-k+1))`, and the central scale
`q^(m*m) (q⁻¹;q⁻¹)_∞⁻¹`. Natural subtraction is total, reciprocity is used
only eventually when `k ≤ n`, and no shifted-central or wider nome-domain
claim is made. The `b899` q-series and geometric-q PDFs are now historical
checkpoints; PDF regeneration for both changed roots is deferred by user approval.

The sibling `DyadicDerivativeFiltration.lean` module has zero definitions and
exactly six theorems. Its exhaustive surface consists of
`rvachevUp_eq_zero_of_one_le_abs`,
`iteratedDeriv_rvachevUp_dyadic_eq_zero`,
`iteratedDeriv_rvachevUp_dyadic_critical`,
`dyadic_depth_eq_max_nonzero_iteratedDeriv`,
`iteratedDeriv_rvachevUp_eq_extendedFabius`, and
`iteratedDeriv_rvachevUp_dyadic_below`. The final pair completes the
below-depth derivative formula through the rescaled global Fabius value.

## Detailed package record

Current packages and retained intake records:

- **Absorbed 2026-09-02 as Part~X of
  [`geometric_q_fabius_frontiers/`](geometric_q_fabius_frontiers/);
  the directory `q-fabius-parameter-deformations/fabius_q_frontiers_report/` no longer exists.**
  Formerly `fabius_q_frontiers_report/`,
  *Parameter-Flow, Gaussian, and Large-Deviation Frontiers for the
  q-Fabius--Rvachev Family* (23 A4 pp and 1,506 source lines at arrival;
  current main artifact: 22 A4 pp from 1,492 source lines; with two scripts,
  four CSV tables, two captured outputs, and four PDF/PNG figure pairs),
  arrived as a bare directory in direct-arrival commit
  `8a184546747082cbd92ad4675fb61981c6b8c3b6`; no archive or outer hash was
  supplied. Its arrival receipt covered all 20 payloads; four CSV entries later
  received CRLF-to-LF normalization. The later strict rebuild replaced the
  main TeX/PDF pair. All five current PDFs
  are readable and unencrypted (26 pages total). The main report has 33
  embedded/subset font rows, including five Libertinus rows and eight Type-3
  rows inherited from the four included vector figures; the standalone figure
  PDFs contain the same eight Type-3 rows. Figure-font normalization remains
  deferred.

- **Absorbed 2026-09-02 as Part~XI of
  [`geometric_q_fabius_frontiers/`](geometric_q_fabius_frontiers/);
  the directory `q-fabius-parameter-deformations/Continuous_Parameter_Edgeworth_and_q_Gevrey_Frontier/` no longer exists.**
  Formerly `Continuous_Parameter_Edgeworth_and_q_Gevrey_Frontier/`,
  *Continuous-Parameter Edgeworth Theory, Large Deviations, and Quadratic
  q-Gevrey Regularity at the Fabius--Rvachev Frontier* (29 A4 pp and 1,387
  main-source lines at arrival; current main artifact: 29 A4 pp from 1,372
  source lines, SHA-256
  `e9d99619992f78050326249272b18f5941f659dea0f022522b23ec218953d5bf`),
  arrived on 2026-08-30 in direct-arrival commit
  `52179f63fe955a64508915eedaa560de9f3056da` under the bare generic wrapper
  `Fabius_Rvachev_Frontier_Report_2026-08-30-G/` and was filed under this
  title-derived collision-safe name. Its manifest covers the full delivery.
  The current PDF was rebuilt from the final source in three strict passes.
  The main PDF
  has 33 embedded/subset font rows, including six Libertinus rows and six
  Type-3 rows inherited from the three included vector figures; the standalone
  figure PDFs contain the same six Type-3 rows. Its title and abstract concern
  continuous-parameter Edgeworth and deviation regimes, Lambert endpoint
  asymptotics, and quadratic-exponential Denjoy--Carleman regularity.

- [`q_pochhammer_q_binomial_monograph/`](q_pochhammer_q_binomial_monograph/),
  *q-Series and Inverse q-Analogs: A Proof-Oriented Synthesis*, is the one
  canonical source publication for this subgroup. The merged master has 28
  numbered forward chapters, including four chapters distilled from the three
  general guides; the former inverse-q synthesis contributes eight numbered
  branch-aware chapters and one inverse-source provenance appendix. Repeated
  results are stated once in their strongest proved form, while independent or
  genuinely stronger results are retained with complete human-readable proofs.
  Its
  [`PROVENANCE.md`](q_pochhammer_q_binomial_monograph/PROVENANCE.md) records
  the five-publication merge surface, the earlier six-package inverse lineage,
  and the historical artifact lineage. The completed
  [`source_concordance.csv`](q_pochhammer_q_binomial_monograph/source_concordance.csv)
  gives a reviewed disposition for all 547 source result environments from the
  five merged publications. Its canonical destinations comprise 103 Lean-proved
  rows, 375 human-proved
  frontier results, 60 not-applicable rows, and 9 conjectures. The historical
  [`theorem_concordance.csv`](q_pochhammer_q_binomial_monograph/theorem_concordance.csv)
  continues to account for all 260 inverse-source result environments, and
  [`assets/ASSET_DISPOSITION.csv`](q_pochhammer_q_binomial_monograph/assets/ASSET_DISPOSITION.csv)
  preserves the 77-row decision record for unique scripts, data, outputs, and
  figures. Pinned source revisions and Git history preserve every superseded
  layout and arrival fact.

  An upstream publication receipt before the present source union
  records a historical 378-page A4 artifact of 3,175,603 bytes, with SHA-256
  `5d0dac5a8d1cba7bedab9055a51f59478054de22969dcf75b0f58ce3f3c265bc`.
  It was built in exactly three guarded serial passes (378, 378, and 378 pages)
  from a 15,630-line, 764,952-byte source with SHA-256
  `403a25dccadc15e7a34bedd8d28a2dc3369cb6e6a046cd199a30ed178742a32d`.
  Its A4 and embedded/subset-font checks passed, with five Libertinus rows and
  no Type-3 fonts. Those fingerprints remain historical receipts for that
  source state. The next retained historical checkpoint was built in
  exactly three guarded serial passes (386, 395, and 395 pages) from a
  16,834-line, 837,715-byte source with SHA-256
  `4785625c1399558f3ca59481888fc76514e0a327a1faa16945c61851f874f3d5`.
  Its 395-page, 2,494,961-byte A4 PDF has SHA-256
  `89159b2635f489a42d4c972fac95332808b1d637dee7921085db1ed7d6e055af`;
  its compilation, index, reference, font, page-render, and visual gates
  passed. That receipt predates the `9135` final source union and is historical;
  the later 398-page historical receipt above supersedes it.

  The 389- and 391-page predecessor receipts, 401-page first-merge receipt, and
  402-page d130 receipt are retained in the canonical package record as
  additional history. No retained q-series PDF renders the merged source.
  It carries the five-theorem `QPochhammerEntire.lean`, the generic
  `QPochhammerInfinite.lean` and `QPochhammerDissection.lean` APIs, both
  Gaussian structure modules, `GaussianBinomialFixedColumnRate.lean`,
  `CentralQBinomialReduction.lean`,
  `CyclotomicFactorization.lean`, `PrimitiveRootBlock.lean`, `QLucas.lean`,
  `QCatalan.lean`, `CyclotomicDivisibility.lean`, the subsequent q-series
  module tranches including `TwoPhiOneReversal.lean`,
  `QChuVandermonde.lean`, `JacobiTwoSquareCount.lean`, the q-beta, collision-free Newton,
  integer/complex-order Gaussian, q-Pfaff--Saalschuetz, quantum-multinomial,
  and Gaussian reciprocity/growth APIs, the three-theorem
  `GeometricPochhammerNormalConvergence.lean` outer-product API,
  `GeometricUniformRealization.lean` (one definition and seventeen theorems),
  `RegularCentralQBinomialSum.lean` (two definitions and one theorem),
  `GeometricUniformMomentPolynomial.lean` (one definition and eight theorems),
  `HalfQBinomialRootSimplicity.lean` (zero definitions and one theorem),
  `GaussianBinomialGreaterOneAsymptotics.lean` (zero definitions and two
  theorems), `GeometricResidualMoments.lean` (zero definitions and nine
  theorems), and `HalfQBinomialRootSimplicity.lean` (zero definitions and one
  theorem), `GeometricUniformMomentRatFunc.lean` (one definition and four
  theorems), and `GeometricUniformMomentReciprocity.lean` (one definition and
  five theorems). The existing `FinitePolynomialFunctional.lean` module now has
  zero definitions and sixteen public theorems. The forward crosswalk is now
  181 Exact, 79 Partial, 14 None, and 8 interface rows; the source ledger is
  103 Lean-proved, 375 human-proved
  frontier, 60 not
  applicable, and 9 conjectures. The `b899` 405-page monograph PDF and the
  former 398-page PDF are historical artifacts; a synchronized rebuild of the
  changed monograph root is deferred by user approval.
  PDF files retained
  beneath `assets/` are vector research figures, not manuscript builds.
  Manuscript result labels and numerical checks remain
  distinct from Lean verification.

- **Absorbed 2026-09-02 as Part~IX of
  [`geometric_q_fabius_frontiers/`](geometric_q_fabius_frontiers/);
  the directory `geometric-sinc-and-exponent-families/Cyclotomic_q_Fabius_Rvachev_Frontier/` no longer exists.**
  Formerly `Cyclotomic_q_Fabius_Rvachev_Frontier/`,
  *Cyclotomic Blow-Ups and Natural Boundaries for the q-Fabius--Rvachev Sinc
  Product* (25 pp at arrival; currently 28 A4 pp and 1,875 source lines),
  arrived on 2026-08-30 from
  `Cyclotomic_q_Fabius_Rvachev_Frontier.zip` (outer SHA-256
  `029da7d9ec96a0b2e5c4164c37f2b361dd015112bd0c6237263e3c538c5b0f64`).
  All 22 submitted payload hashes verified; five CSV entries were refreshed
  after CRLF-to-LF repository normalization. Its title and abstract place its
  radial root-of-unity expansions, claimed natural-boundary theorem,
  cyclotomic blow-ups, Bell/moment condensation, and inverse branches beside
  the consolidated q-series frontier. A post-publication revision crosswalks
  the global geometric-sinc q-Pochhammer factorization while leaving the
  cyclotomic asymptotic and natural-boundary layers manuscript-only. The
  retained main PDF has 28 A4 pages, so the five PDFs have 32 pages in total
  (28 main plus four one-page figures). Its current 1,875-line source postdates
  that rendering; a fresh strict three-pass build remains pending. The
  retained main PDF uses
  embedded/subset Type-1 Libertinus fonts with no Type 3 font; the unchanged
  standalone vector figures retain nine embedded/subset Type-3 rows as
  disclosed archival debt.

- **Absorbed 2026-09-02 as Part~VIII of
  [`geometric_q_fabius_frontiers/`](geometric_q_fabius_frontiers/);
  the directory `geometric-sinc-and-exponent-families/Fabius_Rvachev_Frontier_Report/` no longer exists.**
  Formerly `Fabius_Rvachev_Frontier_Report/`,
*Negative Parameters, Reciprocal Bases, and the Gaussian Boundary* (current
1,475-line source and matching 26-page A4 PDF), arrived on 2026-08-30 with all
13 payload checksums verified. Its current PDF was rebuilt from the final
source. It develops
negative-parameter affine transport, reciprocal-base digit reversal,
multisection, shape theory, and the Gaussian boundary for geometric-uniform
laws.  Because much of that subject already appears in Part VII of the
consolidated volume, the report remains standalone until its genuinely new
claims are isolated and the overlap is deliberately deduplicated.  Paper
theorem labels do not by themselves assert Lean formalization.

- **Absorbed 2026-09-02 as Part~XII of
  [`geometric_q_fabius_frontiers/`](geometric_q_fabius_frontiers/);
  the directory `q-fabius-parameter-deformations/Fabius_Flat_Parameter_Response_Dynamics/` no longer exists.**
  Formerly `Fabius_Flat_Parameter_Response_Dynamics/`,
  *Flat Parameter Fronts, q-Susceptibility, and Smooth Dynamics* (26 A4 pp;
  current 1,890-line TeX and 519-line deterministic exact/Monte-Carlo program),
  was filed on 2026-08-30 from `fabius_frontier_report_2026.zip` (803,598 bytes;
  SHA-256
  `afdcf522589a7baad82c81a527c02dcc09e58455ab14c57a9c492e65563c647e`).
  Its immutable 13-entry arrival digest receipt records 13/13. The current PDF was
  rebuilt from the final source. The pinned replay reproduced the two exact
  algebra tables, common-random-number table, and two figures byte-for-byte;
  the two Monte-Carlo tables differed only at documented last-bit levels far
  below their sampling errors. A hostile review repaired the conditional-law
  quantifier in the velocity theorem, the KR basepoint argument, endpoint and
  orbit hypotheses, and the false small-divisor expression. Higher-response
  resolvents now require a finite zero-mass representing measure, while the
  all-orders Koenigs/dynamical layer is explicitly conditional on hypothesis
  (K); none of the new parameter-response claims is asserted as an exact Lean
  theorem. The canonical A4/27 mm/Libertinus PDF was rebuilt in exactly three
  strict passes with every font embedded/subset and no Type 3 fonts.

Generalizations of the dyadic construction to arbitrary exponent
sequences and the q-series calculus that organizes them: the
exponent-sequence convolution monoid with its Newton-basis frontiers, and
q-binomial Richardson acceleration of geometric sinc products. The
denominator-free Gaussian/q-binomial core used by both is formalized at arbitrary
ratio. `QBinomialCauchy.lean` exhaustively supplies one definition and five
theorems: the finite q-Cauchy identity and its compatibility spelling, its reflected strengthening, the
denominator-free q-Bernstein basis and its partition of unity, and the second
finite Cauchy identity. They hold for arbitrary parameters and degrees over
every commutative ring, including `q = 0`, roots of unity, and zero divisors.
`SymmetricFunctionOrthogonality.lean` exhaustively supplies one definition and
six theorems: evaluated elementary symmetric functions, their Mathlib bridge,
zero-degree and reindexing laws, `Option` and `Fin` weighted-Pascal recurrences,
and the total elementary--complete orthogonality convolution. The structural
API is valid over commutative semirings; orthogonality is valid over every
commutative ring, including the empty family and degree zero. Together with the
existing `completeHomogeneousEval_option_succ`, the elementary `Option`
recurrence gives both weighted-Pascal laws exactly.

`FiniteTriangularTransform.lean` has the exhaustive one-definition,
one-theorem surface `lowerTriangularTransform` and
`lowerTriangularTransform_comp`. For `[Semiring R] [AddCommMonoid M]
[Module R M]`, a total ordered kernel convolution on `Icc j n` yields an
equality of whole sequence functions; no commutativity of `R`, subtraction,
topology, or infinite summability is used.

`SymmetricFunctionTransform.lean` has the exhaustive four-definition,
five-theorem surface `completeHomogeneousKernel`, `signedElementaryKernel`,
`completeHomogeneousKernel_left_orthogonality`,
`completeHomogeneousKernel_right_orthogonality`,
`completeHomogeneousTransform`, `signedElementaryTransform`,
`signedElementaryTransform_completeHomogeneousTransform`,
`completeHomogeneousTransform_signedElementaryTransform`, and
`weightedSymmetricFunction_inversion`. The complete-homogeneous kernel and
transform need only a commutative semiring. The signed declarations and all
inverse results use a commutative ring; transform targets need only an
additive commutative monoid with its module structure. Both kernels are
zero-extended above the diagonal, and both whole-function compositions reuse
the generic triangular theorem. Thus weighted inversion is exact, with a
module-valued strengthening.

`SymmetricFunctionGenerating.lean` has the exhaustive two-definition,
six-theorem surface `elementarySymmetricGeneratingSeries`,
`completeHomogeneousGeneratingSeries`,
`coeff_elementarySymmetricGeneratingSeries`,
`coeff_completeHomogeneousGeneratingSeries`,
`elementarySymmetricGeneratingSeries_eq_prod`,
`elementarySymmetricGeneratingSeries_neg_mul_completeHomogeneousGeneratingSeries`,
`completeHomogeneousGeneratingSeries_eq_invOfUnit_elementarySymmetricGeneratingSeries_neg`,
and `prod_one_sub_qPow_X_mul_gaussianBinomialGeneratingSeries`. The
definitions, coefficient results, and finite elementary product hold over a
commutative semiring; reciprocity, canonical inversion, and the finite
Gaussian reciprocal identity require a commutative ring. These close only
the formal-power-series halves of the weighted-generating and reciprocal
finite claims. Analytic evaluation and convergence under `|w_i z| < 1` or
`|z| < 1` remain open.

The complementary finite-index API in `CompleteHomogeneousGenerating.lean`
has one definition and six theorems:
`completeHomogeneousGeneratingSeriesOn`,
`coeff_completeHomogeneousGeneratingSeriesOn`,
`completeHomogeneousGeneratingSeriesOn_empty`,
`completeHomogeneousGeneratingSeriesOn_insert`,
`one_sub_mul_completeHomogeneousGeneratingSeriesOn_insert`,
`prod_one_sub_mul_completeHomogeneousGeneratingSeriesOn`, and
`completeHomogeneousGeneratingSeriesOn_eq_invOfUnit_prod`. Its coefficient,
empty-family, and adjoining-variable results hold over commutative semirings;
its denominator-clearing and canonical-inverse results hold over arbitrary
commutative rings, including rings with zero divisors. Together, this API and
`SymmetricFunctionGenerating.lean` prove both formal algebraic halves of the
weighted generating-product theorem, but neither proves its analytic clause.
Separately, the sole public theorem
`completeHomogeneousEvalOn_isBigO_pow` in
`CompleteHomogeneousAsymptotics.lean` transfers coordinatewise `O(g)` bounds
through every fixed complete homogeneous degree to `O(g^n)`, including degree
zero and without a nonvanishing hypothesis on `g`; it does not evaluate or
prove convergence of either formal series.

`BitPositionQBinomial.lean` gives both the zero-based and literal
one-based weighted-subset enumerations. `QBinomialInversion.lean` proves the
Gaussian chain law, general alternating rows, and both finite convolution
orders for unscaled and independently scaled kernels; the scale is arbitrary
and need not be invertible. In `QBinomialTransform.lean`, the two forward
definitions require `[Semiring R] [AddCommMonoid M] [Module R M]`, the two
signed inverse definitions require `[Ring R]` with the same target
assumptions, and all four theorems require `[CommRing R]` with that additive
commutative monoid target. Both compositions are whole-function equalities,
the inversion statements are exact iff results, and the refactored proofs
reuse `lowerTriangularTransform_comp`; Gaussian kernels are zero-extended
above the row. Its exhaustive four-definition, four-theorem surface is
`scaledGaussianBinomialTransform`, `scaledGaussianBinomialInverseTransform`,
`scaledGaussianBinomialInverseTransform_transform`,
`scaledGaussianBinomialTransform_inverseTransform`,
`scaledGaussianBinomial_inversion`, `gaussianBinomialTransform`,
`gaussianBinomialInverseTransform`, and `gaussianBinomial_inversion`.

`QDifferenceAnnihilation.lean` has the exhaustive four-theorem surface
`sum_scaledGaussianBinomialInverseKernel_mul_pow`,
`sum_gaussianBinomialInverseKernel_mul_geometric_pow`,
`qDifference_sum_eval₂_eq_map_coeff_mul`, and
`qDifference_sum_eval₂_eq_zero_of_degree_lt`. Over every commutative ring,
the scaled signed row has characteristic polynomial
`sum_(k=0)^n (-s)^(n-k) q^(choose (n-k) 2) [n choose k]_q z^k = prod_(j<n) (z-s q^j)`.
With `s = 1` and `z = q^d`, its exact monomial moment
is `prod_(j<n) (q^d-q^j)`, hence is zero whenever `d < n`. More generally,
for a polynomial over any semiring and any scalar-extension homomorphism into
a commutative ring, the row in degree at most `n` extracts the mapped
coefficient of degree `n` times `prod_(j<n) (q^n-q^j)`; it annihilates every
polynomial of degree strictly below `n`. These results include `n = 0` and the
zero polynomial, allow repeated nodes and a zero surviving product, and use no
division, nonzero or invertible base, domain, characteristic, topology, or
convergence hypothesis.

The global identity
`geometricQBinomialWeightNumerator_eq_scaledGaussianBinomialInverseKernel`
is now owned by `GeometricQBinomialLagrange.lean`: it identifies the
denominator-free geometric numerator with the scaled inverse kernel at base
and scale `q` for all natural indices, including above the diagonal. It is
the `s = q` specialization of the preceding characteristic polynomial.
`QBinomialInversionSpecializations.lean` now has exactly two definitions and
four theorems: `qGaussianResidualCoeff`,
`qGaussianReconstructionCoeff`, `qGaussianResidualCoeff_eq`,
`qGaussianReconstructionCoeff_eq`,
`qGaussianReconstructionCoeff_residualCoeff_delta`, and
`qGaussianResidualCoeff_reconstructionCoeff_delta`. These prove both
q-Gaussian coefficient inversions at base `q^2`, scale `-q`. The two
definitions and their pointwise closed-form theorems require only `[Ring R]`;
exactly the two convolution-delta theorems require `[CommRing R]`.

The current geometric q-layer has the following exhaustive public surfaces:

- `GeometricCompleteHomogeneous.lean` has six theorems:
  `completeHomogeneousEval_geometric`,
  `completeHomogeneousEval_scaled_geometric`,
  `completeHomogeneousEvalOn_range_pow_eq_gaussianBinomial`,
  `completeHomogeneousEvalOn_range_pow_eq_gaussianBinomial_degree`,
  `gaussianBinomial_add_symm`, and
  `gaussianBinomial_symm_via_completeHomogeneous`. They prove both orientations
  of the denominator-free principal specialization, its range and common-scale
  forms, and two Gaussian symmetry laws over every commutative semiring.

- `GeometricLagrangeCompleteHomogeneous.lean` has five theorems:
  `completeHomogeneousEvalOn_geometric_range`,
  `sum_geometricLagrangeWeight_mul_pow_succ_add_eq_gaussianBinomial`,
  `geometricLagrangeQMoment_eq_residual_gaussianBinomial`,
  `completeHomogeneousEvalOn_geometric_range_eq_qBinomial`, and
  `geometricLagrangeQMoment_eq_residual_qBinomial_via_completeHomogeneous`.
  The first is a commutative-semiring alias; the field residual uses finite-node
  injectivity; the rational quotient bridges keep their explicit
  nonzero-Pochhammer or `0 < q < 1` assumptions.

- `GeometricLagrangeQMoments.lean` has one definition,
  `geometricLagrangeQMoment`, and 37 theorems:
  `geometricLagrangeQMoment_eq_weightPolynomial_eval`,
  `geometricLagrangeQMoment_eq_forwardRichardson_eval`,
  `geometricRootPolynomial_inv_eval_pow_mul_signedPowers`,
  `geometricRootPolynomial_inv_eval_pow_mul_triangular`,
  `geometricRootPolynomial_inv_eval_one_mul_triangular`,
  `geometricLagrangeQMoment_eq_qPochhammer`,
  `geometricLagrangeQMoment_zero`, `geometricLagrangeQMoment_eq_zero`,
  `geometricRootPolynomial_inv_eval_pow_eq_qPochhammer_of_le`,
  `geometricLagrangeQMoment_eq_residual_qPochhammer`,
  `qPochhammer_self_add`, `qPochhammer_self_pos_of_pos_of_lt_one`,
  `qBinomial_pos_of_pos_of_lt_one`,
  `gaussianBinomial_eq_qBinomial_of_pos_of_lt_one`,
  `qPochhammer_pow_pos_of_pos_of_lt_one`,
  `qPochhammer_tail_div_self_eq_qBinomial`,
  `geometricLagrangeQMoment_eq_residual_qBinomial`,
  `geometricLagrangeQMoment_firstUncancelled`,
  `negOnePow_mul_geometricLagrangeQMoment_eq_positiveResidual`,
  `negOnePow_mul_geometricLagrangeQMoment_pos`, `qPochhammer_self_succ`,
  `qBinomial_succ_succ_of_pos_of_lt_one'`,
  `qBinomial_succ_succ_of_pos_of_lt_one`,
  `qBinomial_theorem_of_pos_of_lt_one`,
  `sum_qBinomial_triangular_succ_eq_neg_qPochhammer`,
  `abs_geometricLagrangeWeight_eq_qBinomial`,
  `abs_geometricLagrangeWeight_eq_sign_mul`,
  `abs_geometricLagrangeWeight_complement_eq_qBinomial`,
  `sum_abs_geometricLagrangeWeight_eq_qPochhammer_ratio`,
  `neg_qPochhammer_div_self_eq_prod`,
  `sum_abs_geometricLagrangeWeight_eq_prod`,
  `quarterGeometricLagrangeQMoment_eq_qPochhammer`,
  `quarterGeometricLagrangeQMoment_eq_zero`,
  `quarterGeometricLagrangeQMoment_eq_residual_qPochhammer`,
  `quarterGeometricLagrangeQMoment_eq_residual_qBinomial`,
  `quarterGeometricLagrangeQMoment_firstUncancelled`, and
  `sum_abs_quarterGeometricLagrangeWeight_eq_qPochhammer_ratio`. These are
  finite rational identities. Quotient results retain their stated nonzero
  denominators; positivity, sign, and absolute-value formulas retain
  `0 < q < 1`; no analytic convergence or error estimate is claimed.

- `FinitePolynomialFilterExactness.lean` has five theorems:
  `polynomialFilter_response_eq`, `polynomialFilter_exact`,
  `normalizedGeometricRootPolynomial_filter_exact`,
  `forwardGeometricRichardsonPolynomial_filter_exact`, and
  `forwardGeometricRichardsonPolynomial_filter_firstUncancelled`. The generic
  response and mass-one/root laws hold over commutative semirings. The
  geometric field forms retain their nonzero-base and normalization-denominator
  assumptions, cancel the prescribed modes, and expose the first survivor.

- `QuarterCatalanGerm.lean` has two definitions,
  `quarterCatalanCoefficient` and `quarterCatalanGermSeries`, and thirteen
  theorems: `quarterCatalanCoefficient_zero`,
  `quarterCatalanCoefficient_succ_eq_report`,
  `quarterCatalanGermSeries_coeff`, `quarterCatalanGermSeries_coeff_succ`,
  `quarterCatalanGermSeries_constantCoeff`,
  `quarterCatalanGermSeries_equation`,
  `powerSeries_quadratic_injectiveOn_zeroConstant`,
  `eq_quarterCatalanGermSeries_of_equation`,
  `existsUnique_quarterCatalanGermSeries`,
  `dyadicGermTwo_functionalEquation`,
  `rescale_dyadicGermTwo_eq_quadraticInverse`,
  `dyadicGermTwo_eq_rescale_quadraticInverse`, and
  `coeff_dyadicGermTwo_succ`. They give the unique zero-constant solution of
  `D + 4D^2 = (4/9)X` in `ℚ[[X]]`, all of its report coefficients, and the
  exact rescaling bridge to the distinguished dyadic germ and the inverse of
  `X + 4X^2`.

- `FabiusInverseQuarterJet.lean` has exactly two public theorems,
  `iteratedDeriv_centeredFabiusInv_quarter_eq_quadraticInverse` and
  `iteratedDeriv_fabiusInv_five_seventy_two_succ`. They identify the complete
  smooth derivative jet of the actual inverse at `5/72 = F(1/4)` with the
  factorial-scaled quadratic-inverse coefficients and prove
  `G^(m+1)(5/72) = (m+1)! (-4)^m C_m`. This is equality of jets only, not
  convergence of the formal germ, equality on a neighborhood, or analyticity
  at the quarter anchor.

- `QuarterCatalanRichardson.lean` has three definitions,
  `finiteRescaleFilter`, `geometricRichardsonPowerSeriesFilter`, and
  `quarterCatalanRichardsonFilter`, and 15 theorems:
  `finiteRescaleFilter_coeff`,
  `geometricRichardsonPowerSeriesFilter_coeff`,
  `geometricRichardsonPowerSeriesFilter_coeff_zero`,
  `geometricRichardsonPowerSeriesFilter_coeff_eq_zero`,
  `geometricRichardsonPowerSeriesFilter_coeff_eq_qPochhammer`,
  `geometricRichardsonPowerSeriesFilter_coeff_eq_qBinomial`,
  `geometricRichardsonPowerSeriesFilter_firstUncancelled_coeff_of_nonzero`,
  `geometricRichardsonPowerSeriesFilter_firstUncancelled_coeff`,
  `quarterCatalanRichardsonFilter_coeff`,
  `quarterCatalanRichardsonFilter_coeff_zero`,
  `quarterCatalanRichardsonFilter_coeff_eq_zero`,
  `quarterCatalanRichardsonFilter_coeff_eq_zero_of_le`,
  `quarterCatalanRichardsonFilter_coeff_eq_qBinomial`,
  `quarterCatalanRichardsonFilter_coeff_succ_eq_qBinomial`, and
  `quarterCatalanRichardsonFilter_firstUncancelled_coeff`. These are strictly
  coefficientwise formal-power-series results: they preserve degree zero,
  cancel the prescribed low degrees, and identify all residual coefficients
  and the first survivor, without a convergence, real error-sign, remainder,
  or analytic-acceleration claim.

Finally, `sum_lagrangeEvalWeight_mul_pow_card_add_zero` in
`LagrangeResidualMoments.lean` gives every higher evaluation-at-zero moment
for a nonempty distinct field-valued node family as the negative signed nodal
product times the complete homogeneous function. The nonempty premise is
exactly what excludes the exceptional empty-row `0^0` term.

The normalized geometric-Lagrange and analytic Lagrange layers additionally
assume injectivity of `j |-> q^j` on the finite node set (see the status boxes and
crosswalk paragraphs inside the documents).
`sum_geometricLagrangeWeight_mul_scaled_geometric_pow_of_pos` and
`sum_geometricLagrangeWeight_mul_eval_scaled_geometric` in
`GeometricResidualMoments.lean` now prove both clauses of
`cor:scaled-geometric-moments` over an arbitrary field under precisely that
injectivity hypothesis. The polynomial theorem permits arbitrary scale `c`,
including zero, and thus subsumes the manuscript's nonzero-scale case.
The new generic theorem
`sum_weight_mul_eval_affine_of_topCoeff_extractor` in
`FinitePolynomialFunctional.lean` transports any same-ring top-coefficient
extractor across `x |-> a + b*x` over every commutative semiring. Composed
with `halfQBinomial_negativeDyadic_polynomial_sum_eq_mersenne`, it proves
`cor:geometric-prouhet-affine` exactly under the established rational-polynomial
convention. It requires neither a nonzero scale nor distinct transformed
nodes, so `b = 0` and `n = 0` are included.
The zero-definition, one-theorem `HalfQBinomialRootSimplicity.lean` leaf proves
`halfQBinomial_sum_rootMultiplicity_two_pow`. Combined with
`halfQBinomial_sum_eq_zero_iff` and
`gaussianBinomial_half_eq_halfQBinomial`, it makes
`cor:halfbase-root-locus` Exact under the rational-polynomial/rational-root
convention: the rational roots are precisely `2^j`, `j < n`, and each is
simple. Injective scalar extension preserves the displayed multiplicities,
but no public theorem in the leaf classifies all roots over every extension
field.
`AnalyticSeriesFilter.lean` carries the core to exact
diagonal and Gaussian-tail identities for unconditionally summable sampled
series. Its hypotheses are sharp at zero-weight nodes. The current
`AnalyticMoments.lean` and `RvachevQBinomialFilter.lean` close the actual
infinite Rvachev-product specialization: for complex `c,z`, natural order `p`,
and Gaussian base `q = c^2`, only injectivity of `j |-> q^j` on
`range (p+1)` is assumed; `c = 1/2`, `q = 1/4` is assumption-free.
This does not formalize the reports' finite prefixes `P_(b,n)`, their
quotient or Bell coefficients, conditionally convergent boundary series, or
the analytic signs, error bounds, uniform/derivative convergence, and
asymptotics. `FiniteQBinomialCore.lean` zero-extends Gaussian lower indices
to all integers and proves total row reflection. `QBinomialVandermonde.lean`
separately proves both q-Vandermonde orientations, both central supports, the
three natural shifted forms, and the canonical forward backbone's single
shifted-central identity for every integer shift, all over arbitrary
commutative semirings.
`QPochhammerElementaryIdentities.lean` adds exactly 13 public theorems:
`finiteQPochhammerIn_base_reversal_units`,
`finiteQPochhammerIn_inv_base_reversal_units`,
`finiteQPochhammerIn_base_reversal`,
`finiteQPochhammerIn_inv_base_reversal`,
`prod_pow_sub_pow_eq_finiteQPochhammerIn`,
`pow_mul_finiteQPochhammerIn_inv_pow_eq`,
`finiteQPochhammerIn_inv_pow_eq_self_div`,
`finiteQPochhammerIn_inv_pow_eq_zero_of_lt`,
`one_sub_mul_gaussianBinomial_one`,
`gaussianBinomial_adjacent_mul`,
`gaussianBinomial_row_adjacent_mul`,
`gaussianBinomial_adjacent_div`, and
`gaussianBinomial_row_adjacent_div`. The two unit reversals, the root-safe
terminating numerator, the first-column clearer, and the two adjacent cross
identities hold over commutative rings. The two cross identities are total in
all `n,k`, including on and above the row boundary by zero extension. The
field reversal wrappers assume
exactly `a != 0` and `q != 0`; the cleared terminating formula and its
above-range zero theorem assume `q != 0`, while the displayed terminating
quotient also assumes `(q;q)_(N-k) != 0`. The adjacent quotient corollaries
remain restricted to `k < n` and instead assume exactly their displayed Gaussian and linear-factor
denominators are nonzero and do not require `q != 0`.

`QBinomialReciprocity.lean` adds exactly four public theorems:
`gaussianBinomial_reciprocity_units`, `gaussianBinomial_reciprocity`,
`gaussianBinomial_neg_one_eq_zero_of_odd_degree`, and
`gaussianBinomial_neg_one_even_odd_eq_zero`.  Unit reciprocity is total over
every commutative semiring; its semifield wrapper assumes only `q != 0`.
The two `q = -1` theorems hold over every commutative ring, including
characteristic two and above-diagonal zero-extension cases.  This proves the
reciprocity clause of the canonical forward backbone's compound structure
theorem, while its separate degree and coefficient-polynomial clauses keep
that full row partial.

`GaussianBinomialAtNegOne.lean` adds exactly five public theorems:
`gaussianBinomial_neg_one_even_even`,
`gaussianBinomial_neg_one_odd_even`,
`gaussianBinomial_neg_one_odd_odd`,
`finiteQPochhammerIn_neg_one_even`, and
`finiteQPochhammerIn_neg_one_odd`.  Together with
`gaussianBinomial_neg_one_even_odd_eq_zero` from the reciprocity module, these
give all four Gaussian parity values and both paired finite-product identities
over arbitrary commutative rings, without division or characteristic
restrictions.  `GaussianBinomialAtNegOneDerivative.lean` closes the companion
first-jet layer with exactly four public theorems: the even-degree derivative
law and total even-row/odd-column slope over every commutative ring, plus
root-multiplicity one first over `ℤ` and then over every characteristic-zero
commutative ring when `b<a`.  It does not assert simplicity in arbitrary
characteristic or at every cyclotomic zero.

The documents also cross-reference the independent real fractional-Volterra
layer. `FractionalVolterraCalculus.lean` proves positive affine covariance on
ordered intervals for arbitrary real order. For `alpha <= 0`, this covariance is
an identity for the totalized Lean interval-integral definition; a classical
Riemann--Liouville/integrability interpretation is asserted only for positive
order. Gamma-normalized order raising holds for real `alpha > 0` from a continuous Banach-valued primitive with an
interval-integrable right derivative. `FabiusFractionalVolterra.lean`
defines the total causal Rvachev fractional primitive, proves its support cutoff,
positive-natural bridge, and positive-order semigroup on `x >= -1`, and
specializes order raising to the signed Fabius extension for `x >= 0`, the
bounded Fabius function for `0 <= x <= 1`, and the Up-to-Fabius bridge for
`x >= -1`.
Complex orders, Caputo/Riemann--Liouville derivatives, weighted-monomial or iterated
shifts, negative-branch, shifted-lattice, endpoint-moment, transform/tail,
piecewise/refinement, and inverse/quantile formulas
remain research frontiers. These fractional-Volterra API claims were checked at source checkpoint
`149332f9d`.

Geometric-sinc subgroup member:
[`geometric_q_fabius_frontiers/`](geometric_q_fabius_frontiers/). Its accepted
first-merge receipt, now historical, is root
`27624L/1273010B/0839b42a3fb055d860b8e8a3d1ff5e84c2f4addce314d04707c5a067e81553d9`,
exact seven-file aggregate
`27997L/1288647B/18c4c6607e9b7564909ca7e647152a26e517f54d5007e157265b3f61adf8e4f0`,
passes `387/404/404`, PDF
`404pp/8341830B/a083b130a1568dc37af824294b033485f82c97dbeb30a4c4de4d463d04e99530`,
and final log
`2557L/114343B/4de474675a2dcde519c36ff1ac7067717c64b60b92bd40b999d0d117ba1f8df6`;
all recorded gates passed at that checkpoint. Its
historical `2d434eec` whole-root source had 27,520 lines and 1,266,515 bytes,
with
SHA-256 `8292f10862334cb809139259eeb4906bb14f517d41b9600c9b7ad53bb21525b1`.
Three passes at 385/402/402 pages produced the then-accepted 402-page,
8,332,886-byte A4 PDF with SHA-256
`d47431e4d3e721fccf12f90226db77f1898e44b477878954acca3a6e90127cf4`.
Its final 2,557-line, 114,331-byte log has SHA-256
`4d6f8c7974def4a3f9e6bc8ccdffefc3eef7ca8cb7c2f0145a075f95b82ff45e`;
all documented gates passed at that revision. This receipt and the later
first-merge receipt above are explicit history. The later d130 receipt in the authoritative register is also historical after\nthe merged source changed. Its
Parts~I--VII are the former
`Exponents_and_q_Series_Frontiers/` (historical semantic-union TeX: 16,369
lines and 737,912 bytes, SHA-256
`a4aecd625f7eb405de866e2b368bbdc648fb0f9e11b423cb936a2f319d195f02`;
retained historical PDF: 238 A4 pages and 6,953,898 bytes, SHA-256
`fa719a8ea68d3c474928b9fae7449f827eb35a5452613f2b660d8e88ba27267e`;
across seven parts). Exactly three serial passes from the preceding 16,274-line,
731,692-byte source SHA-256
`4be184dc95f7c9d7665e5edf56cd22dc66bdacbc2f113b03b700468836018f8b`
produced 228, 238, and 238 pages. Basic A4, text-extraction, embedded-font, and
no-Type-3 checks passed, but the containing multi-document batch stopped before
the historical subvolume's fresh full log, page-box, and visual audit. That
source/PDF pair remains a historical Parts-I--VII receipt and makes no parity
claim about the current whole-root artifact. The historical semantic-union
source added the upstream q-API crosswalk
material and the exact `GeneralizedRvachevIdentifiability.lean`
zero-order/exponent crosswalk after the PDF's source checkpoint. The latter
gives constructive dyadic-order first differences and full-product rigidity;
zeta-quotient, cumulant/analytic-sample, and probability-law identifiability
remain Partial in Lean. It also replaces raw dyadic-valuation spellings by the
shared `\TwoAdicValuation` command. The preceding 238-page PDF and its
16,274-line build source, together with the intermediate 16,369-line source,
remain historical receipts only.

The synchronized geometric q-frontier receipt (2026-09-04) records a historical
source checkpoint superseded by the later historical `b899` receipt below. The merged
source later added the geometric moment, exterior-germ, degree, and related
proof crosswalks. The historical checkpoint comprised the
27,598-line, 1,270,870-byte TeX source at SHA-256
`6db4e211b0588ed75a0e89e13d97306f1d5d38b42a2bf941914ea16b9ca93dae`.
Exactly three successful serial halt-on-error passes from absent sidecars ran
386 pages / 8,157,293 bytes → 403 / 8,339,780 → 403 / 8,339,736. The final
403-page, 8,339,736-byte A4 PDF has SHA-256
`4d909b5e228e2053d473dc75da502382c7a4fe2b096f798e124e6530d3a15027`.
All 43 font rows are embedded and subset, eleven are Libertinus, and none is
Type 3. Final-log reference/rerun/error checks, metadata, every-page render and
nonblank-text checks, and representative visuals passed; generated sidecars
and forbidden checksum basenames both close at zero. The final log has zero
overfull and 37 underfull diagnostics.

The historical synchronized `b899` geometric-q driver has 27,671 lines and
1,275,367 bytes
(SHA-256 `d47c0ad93eb359d13e7e9772668f16dbc98bcb4d880f3679366e1d461451bbcd`),
and its 8-file recursive TeX closure has 27,777 lines and 1,281,413 bytes
(digest `39f7cd41e706314f2cafb903c2da2e6e83d2b17f5bb0612492204d15c1a28d91`).
Three passes ran 388 pages / 8,163,847 bytes → 405 / 8,346,265 → 405 /
8,346,247; the final 405-page PDF has SHA-256
`fef7d8260543ad1d20d69e9e41fa0cfc31603de7961f6aeb97a50740aecd596c`.
All 405 pages are A4 at rotation zero, render with nonblank text, and use 43
embedded/subset font rows (eleven Libertinus, no Type 3). The final log has no
horizontal or vertical box; metadata, visual, cleanup, and forbidden-basename
gates passed.
The merged driver has advanced beyond this receipt, so the retained PDF is
historical and PDF regeneration of the changed geometric-q root is
deferred by user approval.

This is the 2026-08-28 consolidation of the two former drafts (Part I:

The incoming pre-`d8b` 260-page checkpoint remains additional history.
The d130 campaign checkpoint is root
`27698L/1277747B/e2858f1f3595a7d7401c5da6b5f84015c1c4027d36a923f118c988c8ea062c9e`,
seven-file closure
`28071L/1293384B/aa809fbd88b75412ffcd1fe510adf06d3f3a80b5d649fcadc562c955cefafc96`,
passes `389/406/406`, PDF
`406pp/8349052B/605b9fc75d50e776ebae4494828470528be56a92751a4075ea57686cf9ce44c7`,
and log
`2557L/114355B/2888d79bf198e77effca0579426d4b6759b6249e23da95da58601a68de32423e`.
It passed its recorded gates but is historical after this merge.

A fresh synchronized geometric-q render is pending.
Newton-basis frontiers; Part II: q-binomial Richardson), joined the
same day by the eighth-wave report as **Part III** — *Finite Dyadic
Sinc Products and Piecewise-Polynomial Approximants to Rvachev's
Up-Function* (formerly `finite_sinc_products_report/`): the exact
truncated-power formula for the prefix densities `p_n` with signed
Thue–Morse top-derivative jumps on a uniform dyadic knot grid, sharp
derivative plateaux, the exact error law
`||p_n^(r) − up^(r)||_∞ = 2^(C(r+3,2)−1)/(9·4^n)` with exact
Kolmogorov distance `1/(9·4^n)`, the Bell–Bernoulli all-orders
expansion, stable `q = 1/4` Richardson weights in closed q-binomial
form (extending Part II), a uniform scale-mixture representation
`X = R·U` of the up law, and a positive Gauss/Radau/Lobatto tail
quadrature hierarchy with exact constants — including the
variance-matched positive `16^{-n}` scheme that the frontier corpus
had proposed without construction, and a sixth-order exact-support
Radau rule — and by the two ninth-wave same-topic reports, **merged
editorially** (shared core stated once, constants cross-checked,
unique layers of each kept) as **Part IV** — *Fourier Images of the
Repeated-Integration Approximants* (formerly
`Rvachev_Piecewise_Approximation_Fourier_Images/` and
`rvachev_fourier_frontier_report/`): the master factorization
`f̂_n = Φ · A(2^{-n} t)` with the universal tail-transfer function
`A = sinc z / Φ(z)`, its cotangent and valuation-weighted canonical
products with signed divisor `1 − v₂(m)`, digit-sum zero counts and
the Thue–Morse sign law, exact Taylor radius `4π` with dominant-pole
coefficient asymptotics and an arithmetic Darboux hierarchy, the
complete finite/limit zero-multiplicity filtration, the sharp
`o(2^n)` relative-convergence window with forward/inverse
conditioning thresholds at `4π·2^n` and `π·2^n`, the impossibility of
globally stable convolutional deconvolution, weighted-`L^p` and
Sobolev all-orders norm laws with explicit leading constants, exact
algebraic mean-square Fourier tails with the sharp threshold
`f_n ∈ H^s ⟺ s < n + 1/2`, and positive moment-matched atomic,
dyadic-atomic, and polynomial-density closure menus at rates
`16^{-n}`–`256^{-n}`, compared as a family against Part III's box
mixtures.  A fifth part arrived with the tenth wave (formerly
`fabius_finite_products_frontier/`) — **Part V**, *Finite Dyadic Sinc
Products and Exact Transport Geometry of Rvachev Spline Approximants*:
convex-order and peakedness chains for the prefix laws, the exact
absolute moment `E|X_N| = 5/18 - 4^{-N}/9`, the fixed single crossing
of the density error at `x = +-1/2` for every stage, the exact metric
collapse `W_1 = d_K = 4^{-N}/9`, `TV = 2*4^{-N}/9`, stop-loss =
second-order Zolotarev = `4^{-N}/18`, `W_inf = 2^{-N}` with the
synchronous coupling optimal only at `p = inf`, the exact Thue-Morse
call-potential spline, the positive-mixture no-go theorem (no convex
combination of stages can cancel the leading error in any of these
metrics — signed Richardson weights are structurally necessary),
entropy/Fisher monotonicity with the exact criterion
`I(u_N) < inf iff N >= 3` and `KL(u || u_N) = inf`, and carefully
flagged conjectural weighted expansions (entropy, forward KL, Fisher,
fixed-p Wasserstein, and the `p ~ 2N` transport crossover with its
lower-Lambert phase).  The thirteenth wave added **Part VI** —
*Atomic Sinc-Product Splines Beyond the Binary Point* (formerly
`atomic_sinc_splines_report_package/`): an English translation and
frontier expansion of Rvachev's Chapter 3, treating the geometric
family `h_a` as a genuine deformation of `up = h_2` — the general
atomic-equation zero-matching criterion, closed Bernoulli cumulants
`κ_2m = 2^2m B_2m/(2m(a^2m − 1))` with Bell/Lambert moment calculus,
weighted Prouhet identities, exact derivative norms for `a ≥ 2`, the
fractal polynomial-gap atlas for `a > 2` with the complete
Taylor-germ trichotomy, the rational-power Strang–Fix reproduction
theorem, the all-orders prefix expansion with leading profile
`−h_a''/(6(a²−1))` (specializing at `a = 2` to the binary
constants of Parts III–V), the critical `a ↓ 2` collapse, the
reconstructed uniqueness theorem, and a conjecture register
(periodic-Lambert endpoint expansion, critical double scaling,
lattice obstruction without rational powers, strict log-concavity for
`1 < a < 2`).  The fourteenth wave brought a twin — *Atomic Functions
Beyond the Critical Dyadic Case* (formerly
`Atomic_Functions_Beyond_Dyadic_Report/`), a second independent
reconstruction of the same chapter — which was **merged editorially
into Part VI** (2026-08-28): the shared translation and `h_a` core are
stated once (both editions agreed on every commonly transcribed
equation), and its distinctive layers became dedicated sections — the
fractal-string geometry of `K_a` (geometric zeta
`ℓ₀^s/(1 − 2a^{−s})`, complex dimensions `D_a + 2πik/log a`, an exact
tube formula with continuous nonconstant one-periodic profile, hence
Minkowski non-measurability, with explicit logarithmic average), the
geometric local-degree law `P(N_a = r) = ((a−2)/a)(2/a)^r` with
`(a−2)/2 · N_a → Exp(1)` as `a ↓ 2` (the first marginal of the
critical double-scaling program), quantitative Gaussian (`a ↓ 1`) and
uniform (`a → ∞`) parameter limits with exact rates and an exactly
uniform expanding core, the exact general-base negative-Laplace
decomposition with real-analytic one-periodic correction whose
Fourier modes are `−Γ(−χ_k)ζ(1−χ_k)/log a` (settling the
transform-level half of the periodic-Lambert conjecture and pinning
the Lambert normalization `c_a = √a·log a/2`), the divisor-polynomial
form of `log M_a`, the canonical Fup ladder `G_n → 2·up(2x)`, and
three new register entries (overlap-regime nowhere analyticity,
algebraic-breakpoint arithmetic, a bridge between the two periodic
profiles).  The fifteenth wave brought a third reconstruction of the
same chapter — *Atomic Functions, Rvachev's up-Function, and Smooth
Cantor Splines* (formerly `Rvachev_Atomic_Functions_Report/`) — which
was likewise **merged editorially into Part VI** (2026-08-28),
contributing the signed leading coefficient
`L_ω = (−1)^{N₊(ω)} a^{(r+1)(r+2)/2}/(2^{r+1} r!)` on every gap, the
derivative equimeasurability theorem with the full `L^p` ladder
`‖h_a^{(n)}‖_p = (a^{n(n+3)/2}/2^n)(2/a)^{n/p} ‖h_a‖_p` and the exact
derivative-value mixture law, the endpoint jet-reduction form of the
one-branch formula (the exact
Bernoulli→cumulants→moments→jets→gap-polynomials engine), the
classical `Fup_n` hierarchy with its exact triangular reconstruction
of `up` by `n(n+1)/2` dyadic averaging steps, closed cumulants
(`σ_n² = 4^{−n}(3n+4)/36`), and quantitative central-limit regime
(Berry–Esseen `O(n^{−1/2})`), the edge pantograph equations
generalizing `F′ = 2F(2·)` to every base, and further register
entries (`Fup_n` Edgeworth, graph-directed atomic splines,
pressure-function Taylor multifractal).  The sixteenth and seventeenth
waves arrived as same-topic twins on the signed and reciprocal
parameter orbit `{q, −q, 1/q, −1/q}` of the geometric-uniform family
and were **merged editorially as Part VII** — *Signed and Reciprocal
q-Fabius Frontiers* (formerly `Fabius_Q_Connections_Report/`, *Beyond
the Dyadic Fabius Web*, and `Signed_Reciprocal_q_Fabius_Frontiers/`):
affine sign conjugacy (negative q creates no new normalized shapes),
the reciprocal moment germ with `M_q(t)·M_{1/q}(−t) = 1` and finite
digit-reversal duality giving `q = ±2, ±4` exact meaning, geometric
multisection (whose fixed normalized half--quarter series, product-law,
and scaled-measure convolution are now formal, while the general `q,m`, MGF,
cumulant, centered-density, and spectral forms remain frontier), the spectral
q²-Pochhammer factorization, the
Bernoulli cumulant dictionary with closed spectral zeta, log-concavity
with the exact plateau phase `|q| ≤ 1/2`, the positive Laplace
representation of reciprocal germs (vertical-line moments, Hankel
signature `(−1)^C(n,2)`, orthogonal polynomials on `Re z = 1/2`), the
q-Fabius–Bernoulli Appell deconvolution family, the moment polynomial
`𝒫_n(q)` with its odd-q-integer divisor conjecture, the two-nome
Pochhammer–Prouhet partition function and digit-position master
product, the exact q-Prouhet moment transfer, the
Grassmannian/Hermitian finite-geometry square, box-spline derivative
combs with the dimension-1/2 quartic Cantor skeleton, reciprocal
q-Lagrange row reversal, the exact inverse-geometric endpoint lattice
`G_q(qⁿ) = q^C(n+1,2)·𝒫_n/(q;q)_n` with all jets and new
inverse-quartic values, the uniform two-term endpoint asymptotic with
its square-root/log-log inversion, and the resolution of the
sixteenth wave's periodic-cocycle conjecture by Part VI's exact
Gamma–zeta Laplace decomposition.  The eighth-wave fold also
repaired the volume's part-boundary section numbering (Part II had
rendered with `\appendix` letters G–N).  Supporting files under
`assets/`, provenance with SHA-256 in the document itself.  For the spectral
q²-Pochhammer theorem, the current Lean crosswalk proves the general inside
product but remains partial at the surrounding wrappers.  The sinc-product
API proves, for real `|q| < 1`, the uncentered real-frequency identity
`φ_q(t) = exp(i t/2)·S_q((1-q)t/(2π))` and, for complex `‖q‖ < 1`, locally
uniform convergence and entire-ness of `S_q(z) = ∏ sinc(πqⁿz)`.  The
Pochhammer module now proves absolute summability of the paired Euler
perturbations and the global rearrangement
`S_q(z) = ∏_k (z²/(k+1)²;q²)_∞` for every strict complex contraction,
including `q = 0` and individual zero factors.  What remains outside Lean is
the named centered/MGF packaging, the reciprocal outside-disk formula,
zero–pole exchange, and a packaged compact-uniform theorem for the full
phase-bearing characteristic prefixes.

See [`../MANIFEST.md`](../MANIFEST.md) for titles and the previous paths.

The two revised fourteenth-wave editions
(`Atomic_Functions_Beyond_Dyadic_Report-2/`, `-3/`) were merged into Part VI
(2026-08-28): the Orlicz/rearrangement form of derivative equimeasurability,
the spectral Stieltjes–Wigert bridge (squared-frequency moments
`a^{n(n+2)}/2^n`, an explicit non-lognormal representing measure with closed
Hankel determinants and orthogonal polynomials), the Mellin law of the
distance to `K_a` (complex dimensions shifted by −1; distribution function =
the exact tube formula), and — for provenance — the eleven-page Russian
source scan itself, against which the translation layers were checked (the
scan and the raw OCR were both deleted once their recoverable content was
merged and verified; SHA-256 hashes stay in the volume's provenance list,
the repair ledger lives in Part VI's concordance appendix, and git history
archives the files).  The revised fifteenth-wave
edition (`Atomic_Functions_Rvachev_Report_Package/`) followed: the
q-Gaussian derivative Gram kernel `q^{(j−k)²}` with Pochhammer determinants
and sharp Jacobi-theta Riesz bounds, the log-Weibull jet-intermittency law,
and the proof of the uniform all-orders `Fup_n` Edgeworth expansion
(resolving that register conjecture).  An expanded fifteenth-wave edition
(`Atomic_Functions_Rvachev_Expanded_Report/`, audit-aware — it marks the
previously merged layers as inherited baseline) closed the Gram geometry:
the Gaussian-binomial Gram–Schmidt theorem
`ψ*_n = Σ_j q^{n−j}·[n,j]_{q²}·e_j` with norms `(q²;q²)_n`, explicit
Cholesky and inverse Gram, the Rogers–Szegő identification of the
orthogonalizers, the uniform-innovation corollary (each new derivative
keeps an innovation of norm at least `(q²;q²)_∞^{1/2}`), the
wrapped-heat-kernel circle model (each parity tower is unitarily the
monomial sequence against `ϑ₄(θ/2, 1/a)` — heat time `log a`), the
MacMahon determinant constant `𝔐(a⁻²)` with parity-factored full-sequence
determinants and triple-product Riesz forms with a verified numeric table,
and the overlap-regime theta conjecture for `1 < a < 2`; its figures and
data live under `assets/Atomic_Functions_Rvachev_Expanded_Report/`.  Two
expanded fourteenth-wave editions
(`Atomic_Functions_Beyond_Dyadic_Expanded/`,
`Atomic_Functions_Beyond_Dyadic_Frontiers/`; both audit-aware, both
re-shipping byte-identical copies of the source scan/OCR, again not
retained) closed the round with disjoint layers: the physical-space
Stieltjes–Wigert differential ladder `Υ_{a,n} = P_{a,n}(−d²/dx²) h_a`
(compactly supported orthogonal system, closed norms, q-binomial
derivative expansion, three-term operator recurrence) — identified during
the merge with the fifteenth wave's Gram–Schmidt vectors,
`Υ_{a,n} = (−1)^n ‖h^{(2n)}‖₂ ψ*_n`, a check that also caught and repaired
a sign-convention slip in the closed Gram–Schmidt theorem's first
printing — plus both parity derivative-jet Gram determinants, the
autocorrelation germ `a^{n(n+2)}/2^n` with zero Taylor radius and provable
ladder incompleteness, and the explicit-null-modes conjecture; and the
exact derivative-energy factorization
`μ_{a,n,p} = Law(S_{a,n} + a^{−n} Y_{a,p})` with `W∞ ≤ 2a^{−n}/(a−1)`
convergence to the symmetric Bernoulli convolution (Cantor measure on
`K_a` for `a > 2`, uniform at `a = 2`), exact Hausdorff support rate, the
Rényi/Shannon entropy laws `H_β(n) = H_β(0) + n log(2/a)` with the
information-dimension reading, and the overlap-regime energy conjecture;
their figures and data live under the matching `assets/` directories.
Two expanded fifteenth-wave editions
(`Atomic_Functions_Rvachev_Report_Expanded/`,
`Atomic_Functions_Rvachev_qBinomial_Frontiers/`; both audit-aware; the
first also re-shipped the two previous editions of its lineage alongside
the scan/OCR — all byte-identical to recorded files, none retained)
completed the orthogonalization and jet theory: the nodal-polynomial
reading of the Gram–Schmidt residuals (interpolation at geometric nodes;
pivot = value at the next node), the exact inverse transform with the
entrywise-positive Cholesky factorization, the minimum-phase theta
whitening filter `A_q(z) = 1/(−qz;q²)_∞` with
`|A_q|²·ϑ₃ = (q²;q²)_∞` (the Szegő factor of the q-Gaussian covariance),
Schur-minor strict total positivity of the kernel with
oscillation/checkerboard consequences, the two-term jet tail with the
sharp exponential-Orlicz threshold, and the highest-jet partial-theta law
with the joint jet–distance transform (the distance-Mellin pole lattice
deforms into an entire partial theta series for `s > 0`); five register
conjectures were added and the algebraic-breakpoint conjecture gained its
transcendental-dichotomy sharpening; figures and data live under the
matching `assets/` directories.
(The q-orbit reports `Fabius_Q_Connections_Report/` and
`Signed_Reciprocal_q_Fabius_Frontiers/` were merged editorially as the
volume's Part VII; their figures/data are likewise under `assets/`.)

Canonical forward/inverse publication:
[`q_pochhammer_q_binomial_monograph/`](q_pochhammer_q_binomial_monograph/)
(historical synchronized `b899` TeX/PDF checkpoint with a 405-page A4 PDF;
the changed canonical source is PDF-regeneration-deferred by user approval, and exact current and
historical details appear above) — *q-Series and Inverse q-Analogs:
A Proof-Oriented Synthesis*. Its forward backbone proves from first principles
the shifted-factorial, Gaussian, hypergeometric, theta, partition, Bailey,
cyclotomic, interpolation, and Fabius--Rvachev machinery consumed by Parts II,
VI, and VII of the frontier volume and by the repository's formalized
Gaussian-binomial core. It retains the former monograph's formula atlas, limit
dictionary, proof-dependency guide, and formalization architecture, and now
places that material in the same master as the branch-aware inverse theory.
The forward backbone was audited on arrival: ten core theorems were
re-verified symbolically; the Chern--Dilcher--Jiu deleted-singularity identity
and Ramanujan's ₁ψ₁ were verified numerically to 30 digits; and one
dominated-convergence majorant was repaired with an `% ed.:` note. Its last
pre-consolidation rendered checkpoint had 13,117 source lines (SHA-256
`29d7b1d4bd2e5601f4eee63acc1ff7ef3f5f904e0f5f3b8474ce6c51a2129cca`)
and a 1,582,997-byte, 213-page PDF (SHA-256
`7ee6f8f6d8e72228a5b20daa119caa4d834b11063f910b526897b2677a2ede7b`).
Those figures identify a retired historical artifact; they are not build
claims about the current canonical source. Historical pre-`d8b`,
2026-09-04, first-merge, d130, and incoming `b899` receipts are retained in
the detailed package record; none claims parity with the merged source.

The latest validated forward formalization ledger has 282 rows: 181 Exact, 79
Partial, 14 with no counterpart, and 8 interface-only. The basic
geometric-uniform row is Exact: `GeometricUniformRealization.lean` proves that
an `iIndepFun` process of unit-interval coordinates with uniform marginal laws
has joint law `uniformProduct`, then transfers the canonical law to the actual
pointwise series on an arbitrary probability space. Its one definition and
seventeen theorems cover absolute convergence, the interval and exact support,
mean one half, reflection, the conditioning/CDF equation and exterior values;
the affine fixed-point theorem uses a fresh canonical-law copy independent of
the head coordinate. The fixed-column row is likewise Exact: the new
zero-definition/nine-theorem rate leaf adds explicit nonasymptotic estimates
and all four relative/additive Big-O forms, including `q = 0`, while reusing the
exponential product bound and shifted limit from the one-definition,
twenty-nine-theorem `QBinomialTheoremInfinite` surface. Both the retained
source theorem and its older redirected fixed-`k`
donor row are therefore Lean-proved in the current source projection. The original
191-result pre-Fabius core had 36 exact, 29 partial, 123 with no counterpart,
and 3 interface-only entries. The four integrated-guide chapters add 31
human-proved but not Lean-formalized assertions and five labelled definitions;
the later Fabius bridge contributes the remaining rows. Its pointwise
inside-`q^2` Pochhammer factorization and the outer product's locally uniform
(normal) convergence are now formal for every complex strict contraction,
including `q = 0`. The compound spectral theorem remains partial at its named
centered/MGF wrappers and exterior reciprocal clauses. The algebra of
q-shifted factorials now accounts for 13 exact, 1 partial, and 1
unformalized result; the q-integer and Gaussian-coefficient chapter for
9 exact, 0 partial, and 0 unformalized results. The finite
q-binomial/inversion chapter now accounts for 10 exact, 0 partial, and 0
unformalized results; the weighted chapter for 5 exact, 3 partial, and 0
unformalized results; and the basic-hypergeometric chapter for 6 exact, 3
partial, and 0 unformalized results. The cyclotomic chapter now has 8 exact,
1 partial, and 0 unformalized results; q-gamma/q-beta has 7 exact, 1 partial,
and 0 unformalized results; and negative upper indices/geometric Newton has 9
exact, 0 partial, and 0 unformalized results. The exact rows include the primary and
second q-Cauchy identities, both weighted-Pascal recurrences,
elementary--complete orthogonality, and weighted symmetric-function inversion.
Their adjacent strengthenings are recorded human-readably in the canonical
forward backbone:
reflected q-Cauchy and the q-Bernstein partition of unity, plus total
empty-family and degree-zero boundaries. Weighted generating products and the
reciprocal finite theorem are partial because their formal power-series
identities are exact while their analytic evaluation and convergence clauses
remain open. The terminating q-Pfaff--Saalschütz summation is Exact as finite
field algebra under its explicit nonzero-factor hypotheses; it makes no
convergence claim. These counts and boundaries were
statically cross-checked against the exhaustive public surfaces of
`QBinomialCauchy.lean` (one definition and five theorems, including the
compatibility spelling of its primary identity),
`SymmetricFunctionOrthogonality.lean` (one definition and six theorems),
`FiniteTriangularTransform.lean` (one definition and one theorem),
`SymmetricFunctionTransform.lean` (four definitions and five theorems), and
`SymmetricFunctionGenerating.lean` (two definitions and six theorems),
`QDifferenceAnnihilation.lean` (four theorems),
`QBinomialInversionSpecializations.lean` (two definitions, four theorems),
`QPochhammerElementaryIdentities.lean` (13 theorems),
`QPochhammerDissection.lean` (two theorems),
`QPochhammerInfinite.lean` (one definition, 29 theorems),
`QBinomialReciprocity.lean` (four theorems),
`GaussianBinomialBounds.lean` (zero definitions, six theorems),
`GaussianBinomialFixedColumnRate.lean` (zero definitions, nine theorems),
`GaussianBinomialPalindromic.lean` (zero definitions, fourteen theorems),
`GaussianBinomialPolynomialStructure.lean` (zero definitions, five theorems),
`GaussianBinomialCumulants.lean` (two definitions, twenty-four theorems),
`CentralQBinomialReduction.lean` (zero definitions, six theorems),
`RegularCentralQBinomialSum.lean` (two definitions, one theorem),
`CyclotomicFactorization.lean` (zero definitions, seven theorems),
`PrimitiveRootBlock.lean` (zero definitions, three theorems),
`QLucas.lean` (zero definitions, seven public theorems),
`CyclotomicDivisibility.lean` (zero definitions, three theorems),
`QCatalan.lean` (one definition, eleven theorems),
`NewtonInterpolation.lean` (three definitions, nineteen theorems),
`TwoPhiOneReversal.lean` (two definitions, twelve theorems),
`QChuVandermonde.lean` (zero definitions, ten theorems, including the public
`two_mul_choose_two`),
`JacobiTwoSquareCount.lean` (zero definitions, four theorems),
`QBetaIntegral.lean` (one definition, eight theorems),
`NewtonInterpolation.lean` (three definitions, nineteen theorems),
`GaussianBinomialInteger.lean` (one definition, ten theorems),
`GaussianBinomialComplexOrder.lean` (one definition, five theorems),
`QPfaffSaalschutz.lean` (zero definitions, three theorems),
`QuantumMultinomial.lean` (zero definitions, five theorems),
`GaussianBinomialBounds.lean` (zero definitions, six theorems),
`GaussianBinomialAtNegOne.lean` (five theorems),
`RvachevPochhammerFactorization.lean` (one definition, ten theorems), and
`QPochhammerEntire.lean` (zero definitions; four legacy compatibility
wrappers plus one analytic-order compatibility theorem),
`GeometricPochhammerNormalConvergence.lean` (zero definitions, three
theorems), `GeometricUniformRealization.lean` (one definition, seventeen
theorems), `QPochhammerLogDerivative.lean` (zero definitions, ten theorems),
`QPochhammerOrderDerivative.lean` (zero definitions, three theorems), and
`JacobiCubic.lean` (zero definitions, two theorems).
The direct structure theorems in `GaussianBinomialPalindromic` are
`gaussianBinomial_natDegree`, `gaussianBinomial_monic`,
`coeff_gaussianBinomial_zero`, `reflect_gaussianBinomial`, and
`coeff_gaussianBinomial_reflect`. The same generic commutative-semiring API
exports the top coefficient, degree bound, boundary evaluations, and the
division-free mean identity
`two_mul_derivative_gaussianBinomial_eval_one`. The new
`coeff_gaussianBinomial_one_of_pos_of_lt` and
`coeff_gaussianBinomial_one` theorems give coefficient one in every strict
interior column and zero on every boundary. The `cor:positivity`,
`thm:qbinom-structure`, and inverse-source
`prop:gq-positive-palindromic` rows are therefore Exact.
The `GaussianBinomialCumulants` surface includes
`eval_one_derivative_derivative_gaussianBinomial_X`,
`twelve_mul_secondMoment_gaussianBinomial_eval_one`, and
`twelve_mul_varianceNumerator_gaussianBinomial_eval_one`. The divided
second-derivative formula assumes `k ≤ n` over a characteristic-zero field;
the two cleared coefficient-moment identities are total over every
commutative semiring, including above-row and positive-characteristic cases.
They formalize the universal generating polynomial, not a separate
probability-space object.
The five `GaussianBinomialAtNegOne` theorems are
`gaussianBinomial_neg_one_even_even`,
`gaussianBinomial_neg_one_odd_even`,
`gaussianBinomial_neg_one_odd_odd`,
`finiteQPochhammerIn_neg_one_even`, and
`finiteQPochhammerIn_neg_one_odd`. The first three together with the reused
`gaussianBinomial_neg_one_even_odd_eq_zero` theorem from
`QBinomialReciprocity` prove the forward backbone's complete `q = -1` value
formula over every commutative ring, for all natural parameters including
above-row zero extension. The evaluated `q`-Lucas identity is now formalized at
every primitive root of unity of every integral domain. The manuscript's
polynomial congruence modulo `Φ_d(q)` remains outside Lean, so `thm:q-lucas`
is Partial.
The q-difference annihilation row is exact through
`qDifference_sum_eval₂_eq_zero_of_degree_lt`, with the stronger
characteristic-polynomial, all-moment, and scalar-extension top-coefficient
results recorded alongside it. The chapter's alternating sums, both
weighted-subset conventions,
named module-valued inversion iff, and both kernel orthogonalities are exact.
Both orientations
of q-Vandermonde and both central-support presentations are exact in
`QBinomialVandermonde.lean`; the canonical forward backbone's single signed
shifted-central formula is now exact for every integer shift through the zero-extended
`gaussianBinomialInt`, both as a finite natural-range sum and literally as a
finite-support `finsum` over all integers. The ledger also now records the
genuine real infinite product `qPochhammerInf` and its contractive-base
convergence/positivity layer, replacing the stale claim that every infinite
q-Pochhammer in the development was merely a finite `Finset.range` product.
For every fixed complex strict contraction, the separate complex symbol now
has locally uniform convergence on the whole parameter plane, is entire in
that parameter, has exactly its displayed factor zeros (including at the
degenerate nome zero), and every zero has analytic order one. The geometric
sinc product has a global spectral factorization for every complex strict
contraction with nome `q^2`; only the two final Rvachev wrappers specialize to
nome `1/4`. The compound spectral theorem in the Fabius bridge remains
partial because its named centered/MGF wrapper, outside-disk reciprocal
formula, pole divisor, and zero--pole exchange are not formalized. Its outer
local-uniform/normal-convergence clause is exact.
The complementary formal surfaces of
`CompleteHomogeneousGenerating.lean` and
`SymmetricFunctionGenerating.lean` prove both the finite elementary product
and complete-homogeneous reciprocal product; the labelled weighted theorem
remains partial only because its analytic evaluation and convergence clause
is open. `CompleteHomogeneousAsymptotics.lean` adds the fixed-degree
coordinatewise-Big-O transfer, but does not close that analytic boundary.
Separately,
`SymmetricFunctionOrthogonality.lean` proves the displayed
elementary--complete coefficient convolution exactly over every commutative
ring, including the empty family and degree zero.

`QBinomialCauchy.lean` gives the exact primary convolution under the canonical
name `Fabius.finite_qCauchy_identity` and the compatibility spelling
`Fabius.finiteQPochhammerIn_mul_eq_sum_gaussianBinomial`, together with its
reflected orientation, the denominator-free q-Bernstein partition of unity,
and the exact finite Cauchy convolution II. All parameters and degrees are
arbitrary over every commutative ring, so no cancellation, nonvanishing,
injectivity, topology, or convergence hypothesis is needed. The later
q-Pfaff–Saalschütz summation is formalized under its explicit denominator
hypotheses; unrelated infinite-product consequences remain open.

`RegularCentralQBinomialSum.lean` has two definitions and one theorem.
`Fabius.hasSum_regularCentralQBinomial` proves the displayed regular central
sum for `0 < q < 1` under exactly
`qPochhammerInfIn ((q : ℂ) ^ (alpha + 1)) ((q : ℂ) ^ 2) ≠ 0`. The infinite
product zero theorem makes this equivalent to excluding the full complex
denominator lattice `alpha = -1 - 2*j + 2*pi*I*m/log q`; on the real line this
is precisely the negative odd integers. Even negative integral parameters are
allowed, with the field-totalized `qGammaC` quotient zero in agreement with
the product side; this is not a holomorphy claim at a pole.

The wave volumes' central probabilistic object — the normalized
geometric-uniform law `Y_q = (1-q)·∑ qʲU_j`, with `q = 1/2` the
Fabius case and `q = 1/a` the atomic family `h_a` — now carries the
kernel-verified four-face geometric-tail dictionary at every ratio
`|q| < 1`: `GeometricUniformDictionary.lean` converts the corpus's
product-form self-similarity into convolution form and instantiates
`geometric_tail_dictionary` — the measure, characteristic-product,
moment, and cumulant faces of the `m`-digit tail in one statement.
The separate fixed two-section layer in
`GeometricUniformMultisection.lean` has exactly two public definitions,
`Fabius.ProbabilityRepresentation.evenCoordinates` and
`Fabius.ProbabilityRepresentation.oddCoordinates`, and three public theorems:
`Fabius.ProbabilityRepresentation.geometricUniformSeries_one_half_multisection`,
`Fabius.ProbabilityRepresentation.geometricUniformDistribution_one_half_multisection`,
and
`Fabius.ProbabilityRepresentation.geometricUniformDistribution_one_half_conv_one_quarter`.
They prove, without user hypotheses, the pointwise normalized identity
`Y_(1/2)(ω) = (2/3)Y_(1/4)(ω_even) + (1/3)Y_(1/4)(ω_odd)`, the independence and
product-map law of the two parity processes, and the equivalent convolution of
the `2/3`- and `1/3`-scaled quarter laws.  This does not by itself prove a
general multisection theorem, the centered-density formula, or the MGF,
cumulant, Fourier, Pochhammer, `Z`, and comb identities in Part VII.
The characteristic-product face is now closed in elementary terms:
`GeometricSincFactorization.lean` computes the digit,
`φ_digit(t) = e^{i(1-q)t/2}·sinc((1-q)t/2)`
(`Fabius.charFun_geometricUniformDigit`), and proves the **finite sinc
factorization at every ratio**
`φ_q(t) = e^{i(1-q^m)t/2}·∏_{k<m} sinc((1-q)q^k t/2)·φ_q(q^m t)`
(`Fabius.charFun_geometricUniformDistribution_prefix_sinc`, with the
raw closed-factor form `_prefix`) — the finite half of Part IV's master
factorization `F̂ₙ = Φ·A(2⁻ⁿs)` at `q = 1/2` and of Part VI's `ĥ_a`
sinc products at `q = 1/a`, kernel-verified.

The final analytic bridge consists of exactly eight public theorems. For
complex `q,z` with `‖q‖ < 1`, writing
`S_q(z) = geometricSincProduct q z = ∏_{n≥0} sinc(πqⁿz)`, the four theorems
`Fabius.hasProdLocallyUniformly_geometricSincProduct`,
`Fabius.geometricSincProductFactors_multipliable`,
`Fabius.hasProd_geometricSincProduct`, and
`Fabius.geometricSincProduct_differentiable` give locally uniform product
convergence, genuine pointwise `Multipliable` and `HasProd` witnesses with
that exact value, and entire-ness. For real `|q| < 1`, `t ∈ ℝ`, and
`z_q(t) = (1-q)t/(2π)`, including `q = 0` and negative contractions,
`Fabius.charFun_geometricUniformDistribution_eq_phase_mul_geometricSincProduct`
and
`Fabius.charFun_geometricUniformDistribution_eq_phase_mul_geometricReciprocalGamma`
give
`φ_q(t) = exp(i t/2)·S_q(z_q(t)) = exp(i t/2)·G_q(z_q(t))·G_q(-z_q(t))`,
where `G_q(z) = geometricReciprocalGamma q z`. The further theorems
`Fabius.tendstoLocallyUniformly_prefix_sinc_charFun` and
`Fabius.tendstoUniformlyOn_prefix_sinc_charFun` prove that the full
phase-bearing finite prefixes converge locally uniformly on the real
frequency line, and uniformly on every compact real frequency set, to
`φ_q`. These statements still use only `|q| < 1`, so they include `q = 0`
and negative contractions.

`RvachevPochhammerFactorization.lean` adds the exhaustive complex
Pochhammer surface: the one definition `Fabius.complexQPochhammerInf` and
the ten theorems `Fabius.complexQPochhammerInf_eq_tprod`,
`Fabius.complexQPochhammerInf_eq_qPochhammerInfIn`,
`Fabius.multipliable_one_sub_mul_pow_complex`,
`Fabius.hasProd_complexQPochhammerInf`,
`Fabius.tendsto_finiteQPochhammerIn_complex`,
`Fabius.summable_norm_sineTerm_qpow_pair`,
`Fabius.geometricSincProduct_eq_tprod_pair`,
`Fabius.geometricSincProduct_eq_tprod_complexQPochhammerInf`,
`Fabius.rvachevFourierProduct_eq_tprod_complexQPochhammerInf`, and
`Fabius.rvachevFourier_eq_tprod_complexQPochhammerInf`. The new equality to
`Fabius.qPochhammerInfIn` is an unconditional definitional bridge and needs no
contraction hypothesis. The symbol is total; the named multipliability,
product, and finite-prefix convergence theorems require exactly `‖q‖ < 1` and
allow arbitrary complex `a`. The two dyadic
spectral theorems are the last two: they fix the scale and nome `1/4`, hold for
every complex `z` including at zero factors, and the Fourier form assumes
exactly a bounded Fabius witness satisfying `IsFabius`.  Before those
specializations, `geometricSincProduct_eq_tprod_complexQPochhammerInf` proves
globally for every complex `q,z` with `‖q‖ < 1` that
`S_q(z) = ∏'_k (z^2/(k+1)^2;q^2)_∞`; the paired-index and absolute-summability
theorems justify the exchange of scale and spectral-zero indices, including
`q = 0`, negative and nonreal contractions, and zero factors.

`QPochhammerDissection.lean` proves
`Fabius.finiteQPochhammerIn_dissection` and
`Fabius.finiteQPochhammerIn_dissection_remainder` over every commutative ring;
the latter allows the stronger boundary `u <= r`. `QPochhammerInfinite.lean`
adds the generic definition `Fabius.qPochhammerInfIn` and 29 theorems. For a
fixed contracting nome they include finite-prefix convergence, natural-number
finite shifts, factor removal, infinite dissection, and the exact zero locus;
over the complex numbers they include local uniformity in `a`, entire-ness,
and an explicit nonzero derivative at every zero `q^(-j)`. The new
`Fabius.deriv_qPochhammerInfIn_ne_zero_of_mul_pow_eq_one` is the division-free
derivative-nonvanishing statement at every raw factor zero `a*q^j = 1`, so it
also covers `q = 0`; `Fabius.analyticOrderAt_qPochhammerInfIn_of_eq_zero`
then states that every zero has analytic order exactly one, again including
`q = 0`. Thus the finite
dissection and remainder rows are exact, while the arbitrary-complex-order
concatenation row is only partial. Infinite dissection assumes a positive
modulus, while the two finite dissection theorems require no contraction or
nonvanishing. These free-parameter regularity results prove neither joint
`(a,q)` holomorphy nor continuation in the nome, and they do not supply the canonical chapter's
explicit uniform-in-`q` tails and derivative kernels.

`QPochhammerEntire.lean` retains the four earlier compatibility theorems and
adds the analytic-order compatibility theorem, for exactly five public theorems:
`Fabius.hasProdLocallyUniformly_complexQPochhammerInf`,
`Fabius.complexQPochhammerInf_differentiable`,
`Fabius.complexQPochhammerInf_eq_zero_iff`,
`Fabius.complexQPochhammerInf_eq_zero_iff_eq_inv_pow`, and
`Fabius.analyticOrderAt_complexQPochhammerInf_of_eq_zero`. For each fixed
complex `q` with `‖q‖ < 1`, these transfer the generic `qPochhammerInfIn`
results to the older `complexQPochhammerInf` names rather than duplicating
their analytic proofs. They expose local uniform convergence of the
defining factors on the whole complex `a`-plane, entire-ness in `a`, the raw
factor-zero locus `∃ j, 1 - a*q^j = 0`, and analytic order one at every zero.
The division-free zero statement includes `q = 0`; for `q ≠ 0`, the additional
compatibility theorem gives the reciprocal-power zero lattice. The module
asserts neither joint holomorphy in `q` nor local uniformity of the outer
spectral product; the latter is supplied separately by
`GeometricPochhammerNormalConvergence.lean` below.

The
eight-theorem sinc-product tranche above
supplies the general-`q` uncentered real-frequency bridge, locally uniform
entire `S_q`, and real-frequency local and compact uniform convergence of the
full phase-bearing prefixes.  There is still no named centered or MGF wrapper
or outside-disk reciprocal formula. The later entire and generic
infinite-product leaves supply the parameter-local-uniform and normal-
convergence layer described below.

`QPochhammerEntire.lean` retains exactly five compatibility theorems for the
older complex-symbol names:
`Fabius.hasProdLocallyUniformly_complexQPochhammerInf`,
`Fabius.complexQPochhammerInf_differentiable`,
`Fabius.complexQPochhammerInf_eq_zero_iff`,
`Fabius.complexQPochhammerInf_eq_zero_iff_eq_inv_pow`, and
`Fabius.analyticOrderAt_complexQPochhammerInf_of_eq_zero`. For every complex
strict contraction, they prove locally uniform convergence in the parameter
`a`, entire-ness of `a ↦ (a;q)_∞`, the exact factor-zero locus, and analytic
order one at every zero. The division-free factor formulation includes the
degenerate nome `q = 0`; under `q ≠ 0`, the additional theorem rewrites that
locus as the literal reciprocal-power lattice. These facade-reachable wrappers
transfer the generic results without duplicating their analytic proofs. Their
exact human-readable counterparts and refreshed crosswalk rows are present in
the `581bf` source/PDF receipt; the parallel upstream moment-polynomial
crosswalk postdates that historical receipt and is included in the historical
`2d434eec` q-series and standalone geometric-q renders. The later 401-page
q-series and 404-page geometric-q first-merge builds are also historical; all later receipts are historical after the merged sources changed; fresh\nrenders are pending.

Parameter-local statements in the generic leaves alone do not imply joint nome analyticity.

`GeometricPochhammerNormalConvergence.lean` adds zero definitions and exactly
three public theorems. The general theorem
`Fabius.hasProdLocallyUniformly_geometricSincProduct_complexQPochhammerInf`
proves local-uniform convergence on the whole complex plane of the outer
nome-`q^2` Pochhammer product to `S_q` for every complex strict contraction,
including `q = 0`. The other two declarations specialize to the nome-`1/4`
Rvachev product and then to the Fourier transform of every bounded Fabius
witness satisfying `IsFabius`:
`Fabius.hasProdLocallyUniformly_rvachevFourierProduct_complexQPochhammerInf`
and `Fabius.hasProdLocallyUniformly_rvachevFourier_complexQPochhammerInf`.
This closes the outer normal-convergence
subclaim only; the named centered/MGF and exterior reciprocal/pole packaging
of the compound manuscript theorem remains Partial.

`GeometricUniformRealization.lean` adds one definition and exactly seventeen
theorems. It applies `iIndepFun.hasLaw_infinitePi` to independent
unit-interval-valued coordinates with uniform marginal laws, identifies their
full process law with `uniformProduct`, and transfers the canonical geometric
law to the actual pointwise series on an arbitrary probability space. The
surface covers absolute convergence, the interval and exact support, mean one
half, reflection, the conditioning/CDF equation, and exterior CDF values. Its
fixed-point theorem uses a fresh canonical-law copy independent of the head
coordinate, matching the manuscript's head--tail independence premise.

`QPochhammerDissection.lean` adds the two denominator-free finite residue-class
factorizations over arbitrary commutative rings. `QPochhammerInfinite.lean`
adds the generic infinite symbol `Fabius.qPochhammerInfIn` and 29 theorems:
strict-contraction summability and convergence, finite-prefix and residue-class
factorizations, exact zero criteria, locally uniform parameter convergence,
continuity and complex differentiability, nonzero derivatives at every raw
factor zero including `q = 0`, and analytic order one at every zero. Its
infinite dissection assumes a positive modulus, while the two finite dissection
theorems require no contraction or nonvanishing. These APIs are regularity
statements in the free parameter, not joint analyticity or continuation in the
nome.

The latest finite and infinite q-series tranche adds six further
facade-reachable modules. `GaussianBinomialContinuity.lean` has three theorems
for continuity, the classical `q → 1` limit, and the finite-Pochhammer
quotient formula. `JacobiTripleProduct.lean` has 27 declarations covering its
integer exponents, finite and infinite triple products, and Euler's pentagonal
sum. `QBinomialTheoremInfinite.lean` has 28 declarations, including the
dominated-limit engine, Gaussian majorant, Euler product/reciprocal expansions,
the infinite q-binomial theorem, and the five new declarations
`norm_finiteQPochhammerIn_pow_sub_one_le_exp`,
`isBigO_finiteQPochhammerIn_pow_sub_one`,
`tendsto_gaussianBinomial_add_atTop`,
`isBigO_gaussianBinomial_sub_inv`, and
`isBigO_gaussianBinomial_add_sub_inv`. The last two state additive `IsBigO`
errors, equivalent to the manuscript's multiplicative relative errors because
the fixed factor `(q;q)_k` is nonzero for `‖q‖ < 1`.
`QPascalSummation.lean` has four theorems,
`QuantumBinomial.lean` has two noncommutative q-binomial theorems, and
`RogersSzegoPolynomial.lean` has ten declarations for the polynomial,
recurrences, and generating function. Together they contribute 74 public
declarations without weakening the strict-contraction or noncommutative
hypotheses recorded in their source modules.


`GeometricPochhammerNormalConvergence.lean` closes the former outer-product
boundary with exactly three public theorems.  They give locally uniform
convergence of the complex q-Pochhammer product over the spectral index to the
general geometric sinc product for every strict complex contraction, specialize
it to the dyadic standalone Rvachev Fourier product with nome `1/4`, and
transport it to the Fourier transform of every bounded Fabius witness.  The
general statement includes `q = 0`; it is not a joint-holomorphy theorem in the
nome.

The next six-module inventory adds `QMultinomial.lean` (one definition, nine
theorems), `QPochhammerInfiniteBounds.lean` (five theorems),
`QPochhammerComplexOrder.lean` (one definition, four theorems),
`BasicHypergeometricSeries.lean` (two definitions, five theorems),
`HeineTransformation.lean` (two definitions, five theorems), and
`QGaussSummation.lean` (two theorems). Together these 36 declarations cover
q-multinomial algebra, quantitative infinite-product bounds, principal-branch
complex order, basic-hypergeometric convergence, Heine transformation, and the
q-Gauss specialization, with each analytic-continuation boundary retained at
its audited status.

The newest four-module inventory adds `GaussianBinomialPalindromic.lean`
(14 theorems), `JacksonIntegral.lean` (one definition, seven theorems),
`QExponential.lean` (three definitions, eight theorems), and
`ThetaQuasiPeriodicity.lean` (one definition, six theorems). The resulting
status changes make the q-exponential eigenfunction and Jackson
integration-by-parts subclaims Exact; q-exponential factorization, the Jackson
fundamental theorem, and theta quasi-periodicity remain Partial at the
unformalized clauses stated in their rows.

The subsequent tail adds `QPochhammerLogDerivative.lean` (ten theorems),
`QPochhammerOrderDerivative.lean` (three theorems), `JacobiCubic.lean` (two
theorems), `CentralQBinomialReduction.lean` (six theorems),
`RegularCentralQBinomialSum.lean` (two definitions and one theorem), and
`CyclotomicFactorization.lean` (seven theorems). These last three modules make
the central-reduction, regular-central-sum, and cyclotomic-Pochhammer rows
Exact: the central identity is division-free over every commutative ring with
a field/nonzero-denominator quotient wrapper, the analytic sum retains its
exact infinite-product nonvanishing premise, and the factorial cyclotomic
factorization holds over every commutative ring while the Gaussian
factorization holds over every integral domain, with the exponent bounded in
`{0,1}` by the proved divisibility inequalities.
The root-of-unity tail adds `CyclotomicDivisibility.lean` (three theorems),
`PrimitiveRootBlock.lean` (three theorems), `QCatalan.lean` (one definition
and eleven theorems), and `QLucas.lean` (seven public theorems). These
twenty-five declarations prove the carry criterion, complete primitive-root
block, evaluated q-Lucas identity, and integral q-Catalan polynomial at their
stated ring and primitive-root hypotheses. The polynomial q-Lucas congruence
remains outside Lean.
The terminating reversal tail adds `TwoPhiOneReversal.lean` (one definition
and six theorems) and `QChuVandermonde.lean` (five theorems), which owns the
public `two_mul_choose_two`.  Its generic-field nonvanishing hypotheses remain
explicit, and rational-extension removal of the auxiliary hypotheses in the
second q-Chu evaluation is not separately formalized.  The subsequent
`JacobiTwoSquareCount.lean` leaf has four theorems and no definitions: it
closes the nonzero two-square count and both Lambert forms, retaining the
prime-product valuation condition and requiring only `‖q‖ < 1` for the two
complete-normed-field analytic identities.
The newest analytic/algebraic tail adds `QBetaIntegral.lean` (one definition,
eight theorems) and `NewtonInterpolation.lean` (three definitions, nineteen
theorems). It formalizes the Jackson q-beta product and q-gamma evaluation,
symmetry, positivity, and recurrences, together with generic Newton
interpolation and its geometric-grid specialization; the interpolation
polynomial is named `nodeNewtonPoly`, with the definitionally identical
`newtonInterpolant` compatibility surface, and remains distinct from the older
Newton-basis generating-function `newtonPoly`.
The final three-module tail adds integer and principal-complex upper-index
Gaussian coefficients and the terminating balanced q-Pfaff--Saalschütz sum:
`GaussianBinomialInteger.lean` is 1+10,
`GaussianBinomialComplexOrder.lean` is 1+5, and
`QPfaffSaalschutz.lean` is 0+3. Their nonzero-nome,
strict-contraction, and denominator hypotheses remain explicit.
`QuantumMultinomial.lean` adds five theorems for antidiagonal tuple recursion,
noncommutative Gaussian symmetry, and the ordered q-multinomial expansion for
pairwise q-commuting variables.
`GaussianBinomialBounds.lean` adds six theorems and reuses the stronger
`finiteQPochhammerIn_self_pos` from `GeneralQConditionNumber`: evaluated
reciprocity, the finite bounds for `0 <= q < 1`, and the dimension-dominant
lower and upper bounds for `q > 1`. The imported positivity theorem is not
counted as a declaration of the bounds leaf. The exact finite-growth row is
closed, and `GaussianBinomialGreaterOneAsymptotics.lean` closes the compound
greater-than-one row at its exact fixed-column and central normalizations. The
primitive-root value in the Babbage corollary is exact, while its derivative
clause keeps that compound row Partial.
`GaussianBinomialFixedColumnRate.lean` adds no definitions and exactly nine
theorems: `norm_finiteQPochhammerIn_pow_sub_one_le_exp'`,
`norm_finiteQPochhammerIn_pow_sub_one_le`,
`norm_finiteQPochhammerIn_self_mul_gaussianBinomial_sub_one_le`,
`norm_gaussianBinomial_sub_inv_finiteQPochhammerIn_le`,
`norm_gaussianBinomial_add_sub_inv_finiteQPochhammerIn_le`,
`gaussianBinomial_fixedColumn_relativeError_isBigO`,
`gaussianBinomial_shifted_fixedColumn_relativeError_isBigO`,
`gaussianBinomial_fixedColumn_error_isBigO`, and
`gaussianBinomial_shifted_fixedColumn_error_isBigO`. The closure reuses
`norm_finiteQPochhammerIn_pow_sub_one_le_exp_of_norm_le_one` and
`tendsto_gaussianBinomial_add_const_atTop` from the one-definition,
twenty-seven-theorem `QBinomialTheoremInfinite.lean` module. Together they give
the generic product defect, denominator-free relative estimate, explicit
fixed/shifted additive errors, shifted limit, and all four relative/additive
Big-O forms. Their generic multiplicative-norm-ring and normed-field hypotheses
are preserved, and every statement includes `q = 0`.
The terminating basic-hypergeometric closure consists of
`TwoPhiOneReversal.lean` (two definitions and twelve theorems) and
`QChuVandermonde.lean` (ten theorems). It makes both q-Chu evaluations and the
terminating reversal lemma exact for the actual `twoPhiOne` tsum. The separate
full-domain-by-reversal proposition remains Partial: the provenance theorem
needs `C ≠ 0` and `(A;q)_n ≠ 0`, while the full-domain result is proved by
finite q-Cauchy; rational continuation and the cleared commutative-ring
extension remain outside Lean.
