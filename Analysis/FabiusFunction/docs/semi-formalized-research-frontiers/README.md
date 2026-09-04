# Semi-formalized Fabius research frontiers

This directory is the boundary layer between the prose mathematics of the
Fabius function and Rvachev's up-function and the Lean corpus that verifies
it.  It was originally a pure quarantine: everything here lacked an exact,
audited Lean theorem covering its full hypotheses and conclusions.  That is
no longer the shape of the collection.  Much of it has since been
formalized, in some cases more generally than stated here, and each volume
carries a crosswalk naming the declarations that discharge its claims.

So the contents are *mixed*, and the point of the directory is now to keep
the two sides in correspondence rather than to hold one side apart: every
claim should either name the Lean theorem that proves it or say precisely
what is still missing.  `scripts/audit_all.sh` enforces the mechanical half of that:
facade reachability, exact crosswalk names, declaration-name uniqueness, and
the names advertised by module docstrings.  `scripts/audit_stale_claims.py` reports the
half that needs reading.

The canonical frontier artifacts are:

- [`semi-formalized-research-frontiers.tex`](semi-formalized-research-frontiers.tex)
- [`semi-formalized-research-frontiers.pdf`](semi-formalized-research-frontiers.pdf)

> **Source/PDF synchronization.** The retained 257-page, 2,438,299-byte A4 PDF
> includes the 31 August 2026 Legendre Gaunt--Wigner-square closed-form overlay.
> Its PDF (SHA-256
> `3766761aac90247061f5c955dc84a0feb8567454e10839f1508b9431797ee980`)
> source predates the later q-Pochhammer overlay and expanded ledger, so it is
> a historical render and must not be cited as displaying the final source union.

The current source-only superconvergence overlay is also newer than every
retained frontier PDF. `RvachevSuperconvergentSynthesis.lean` contributes one
definition and eight theorems for arbitrary nonzero natural meshes: it
packages the parity-selected phases, exactness through degree `v₂(M)+1`,
physical-coordinate quadrature, deconvolved-polynomial synthesis, and the
explicit Rvachev--Appell specialization. In the canonical inverse synthesis
this promotes exactly `is:p3:cor:forced-superconvergence` and
`is:p3:thm:Appell-lattice-reproduction`, bringing its 194 immutable rows to
49 Lean-proved / 96 human-proved / 10 conjectural / 15 open / 24
nonassertoric. At that superconvergence checkpoint the documentation census
was 671 modules and 8,858 public declarations; no PDF was rebuilt for that
source-only update.

The newest source-only Lambert branch-coordinate overlay formalizes the exact
pairing theorem, its symmetric corollary, the compact Bernoulli-series identity,
and the complex Bernoulli generating function with its standard removable
value and exact convergence radius from `Lambert_W_Guide/`.
`LambertWBranchPairing.lean` has 0 definitions + 7 theorems,
`LambertWGapBijection.lean` has 4 definitions + 16 theorems, and
`LambertWBranchSymmetry.lean` has 0 definitions + 9 theorems. For
`x in (-exp(-1), 0)` and `delta = W_0(x) - W_{-1}(x) > 0`, they prove the two
exact branch formulas, the explicit inverse and gap bijection, the equivalent
`t = exp(delta) > 1` coordinate, the ratio/sum/product identities, and the
strict bounds `W_0 + W_{-1} < -2` and `0 < W_0 W_{-1} < 1`. The proof divides
the two equations `W_j exp(W_j) = x`, then uses branch-range uniqueness for
the converse; `sinh(y) > y` and `y coth(y) > 1` give the strict bounds.
The interval is deliberately open: at the branch point the rational formulas
have zero denominator and their limiting sum/product are `-2` and `1`, while
zero is the singular classical lower endpoint.

The companion `LambertWBranchGapBernoulli.lean` has the exhaustive surface
0 definitions + 5 theorems. Alongside the real open-disk absolute-summability
theorem, `summable_bernoulli_mul_pow_div_factorial_iff` proves for complex `z`
that the Bernoulli exponential generating series is summable exactly when
`‖z‖ < 2*pi`; in particular, it diverges on `‖z‖ = 2*pi` and throughout the
exterior. The new theorem
`hasSum_bernoulli_mul_pow_div_factorial_complex_iff` gives the complex value
as `(complexExpm1Div z)⁻¹` exactly on that disk. This target is `1` at `z = 0`
and rewrites to `z / (exp z - 1)` when `z != 0`; it does not identify the
series with Lean's literal totalized quotient, which is `0` at the origin.
The other theorems give the all-index real quotient value away from zero and
the two paired branch sums when `x in (-exp(-1), 0)` and the positive branch
gap is below `2*pi`. Thus `eq:pair-Bernoulli-general` is Exact, and
`eq:bernoulli-gen` is wholly Exact under the explicit standard
removable-origin convention. The Guide's nearest-nonzero-zero explanation is
not the formal proof route. With the three finite branch-coordinate modules,
the four-module union is 4 definitions + 37 theorems = 41 declarations.
Higher or convergent Puiseux/logarithmic
expansions remain open. The affected retained frontier, primary, walkthrough,
and Lambert-Guide PDFs are historical artifacts and do not render this
source-only overlay; no render parity is claimed. The live documentation
census on the incoming Lambert branch at the exact-radius four-theorem
checkpoint was 903 modules and 11,447 public declarations; the value-completion
theorem gave that branch's historical 903/11,448 checkpoint.

The source-only `FabiusFunction.LagrangeRvachevMatrix` module adds three
definitions, one abbreviation, and six theorems. It promotes
`gq:thm:gaussian-Appell-biorthogonality` and the representation proposition
`prop:lag-markov`; the larger `thm:lag-right-inverse` remains partial because
only its `UB = I` clause is formalized. Its negative-decoder theorem retains
strictly positive row overlap as an explicit hypothesis. No retained frontier,
primary, walkthrough, comb, or representation PDF renders this addition.

The subsequent source-only algebraic addition is
`FabiusFunction.GeometricUniformMomentPolynomial`, with one definition and
eight theorems. It defines the recursive rational polynomial family and proves
its base case, residual-product recurrence, triangular degree bound,
reciprocal-factorial value at zero, and the explicit cases `P1` through `P4`.
Together with the zero theorem this is the complete displayed `P0`--`P4`
algebraic surface. That one-module/nine-declaration increment produced the
historical checkpoint 904 modules and 11,457 public declarations.

The subsequent companion
`FabiusFunction.GeometricUniformMomentPolynomialBridge` has no public
definitions and exactly one public theorem,
`Fabius.geometricUniformMomentPolynomial_eval₂_eq_mgf_taylorCoefficient`.
For every real `q` with `|q| < 1` and every `n`, it identifies the recursive
polynomial with the finite-q-Pochhammer normalization of the `n`th Taylor
coefficient of the actual geometric-uniform moment generating function.
Thus `p7:eq:Pn-def` is **Exact** in this real contraction regime, including
signed `q` and `q = 0`. The exhaustive zero-definition/one-theorem bridge
produced the historical checkpoint 905 modules and 11,458 public
declarations.

The next source-only leaf is
`FabiusFunction.GeometricUniformComplexMomentProduct`, with one public
definition and exactly three public theorems. The definition
`Fabius.geometricUniformComplexMomentProduct` is the actual infinite product;
`Fabius.hasProdLocallyUniformly_geometricUniformComplexMomentProduct` proves
its locally uniform convergence on the complex plane for `‖q‖ < 1`,
`Fabius.differentiable_geometricUniformComplexMomentProduct` proves complex
differentiability on the whole plane, and
`Fabius.geometricUniformMomentPolynomial_eval₂_eq_complexMomentProduct_taylorCoefficient`
identifies its normalized Taylor coefficient with the recursive polynomial.
This is the complex analytic analogue of the real moment identity, not a
complex probability-moment interpretation of `p7:eq:Pn-def`, whose Exact
status remains restricted to real `|q| < 1`. The canonical q-monograph
compound label is not promoted by this inner-disc analogue.

The merged-main pre-local addition
`FabiusFunction.HalfQBinomialRootSimplicity` has no public definitions and
exactly one public theorem,
`Fabius.halfQBinomial_sum_rootMultiplicity_two_pow`. For every `j < n`, it
proves over `ℚ` that the exact half-base q-binomial coefficient polynomial has
root multiplicity one at `2^j`. Together with the existing complete rational
root classification, all roots in that locus are simple. It makes no
arbitrary-base, arbitrary-field, or general cyclotomic simplicity claim. This
leaf raised the historical complex-product 918/11,568 checkpoint to the actual
merged-main pre-local checkpoint 919 modules and 11,569 public declarations.

The next source-only leaf is
`FabiusFunction.GeometricUniformExteriorComplexMomentGerm`, also with one
public definition and exactly two public theorems. The definition
`Fabius.geometricUniformExteriorComplexMomentGerm` is the actual reciprocal
germ `(A_{q⁻¹}(-z))⁻¹` for complex `1 < ‖q‖`;
`Fabius.analyticAt_geometricUniformExteriorComplexMomentGerm` proves genuine
analyticity at the origin, and
`Fabius.geometricUniformMomentPolynomial_eval₂_eq_exteriorComplexMomentGerm_taylorCoefficient`
identifies its normalized Taylor coefficient with the recursive polynomial.
No boundary claim at `‖q‖ = 1` is made by this analytic leaf. The then-public
inner complex `1+2` surface produced the historical
checkpoint 906 modules and 11,461 public declarations; the exterior `1+2`
leaf formed its earlier branch-local historical checkpoint at 907 modules and
11,464 public declarations. In the merged chronology, the exterior leaf adds
its three declarations to 919/11,569 and gives checkpoint 920/11,572.

The latest sharp-degree leaf
`FabiusFunction.GeometricUniformMomentPolynomialDegree` has no public
definitions and exactly three public theorems:
`Fabius.coeff_geometricUniformMomentPolynomial_choose_two`,
`Fabius.coeff_geometricUniformMomentPolynomial_choose_two_sub_one`, and
`Fabius.geometricUniformMomentPolynomial_natDegree_eq`. The coefficient at
`n.choose 2` is `bernoulli' n/n!`, equivalently `(-1)^n B_n/n!`, for every
`n`; for `n ≥ 2`, the coefficient one below it is
`-bernoulli' n/n! + bernoulli' (n-1)/(2*(n-1)!)`. Consequently the exact
natural degree is `n.choose 2` for `n=1` and even `n`, including `n=0`, and
`n.choose 2-1` for odd `n>1`. Canonical `prop:qF-P-degree-sharp` is therefore
**Exact**, and the formerly missing leading/odd-degree clause makes the
represented compound `p7:thm:Pn` **Exact**. This purely algebraic result does
not assert a unit-circle analytic continuation. The 0+3 leaf gives the
historical sharp checkpoint 921 modules and 11,575 public declarations.
`RvachevLaurentLeading` 1+6 then gives 922/11,582, and
`FinitePrefixAppellRecovery` 11+17 gives the historical 923/11,610 checkpoint.

The final source-only leaf is
`FabiusFunction.GeometricUniformMomentRatFunc`, with one public definition and
exactly four public theorems. The exhaustive API is
`Fabius.geometricUniformMomentRatFunc`,
`Fabius.qFactorial_mul_geometricUniformMomentRatFunc`,
`Fabius.eval_geometricUniformMomentRatFunc_eq_complexMomentProduct_taylorCoefficient`,
`Fabius.eval_geometricUniformMomentRatFunc_eq_exteriorComplexMomentGerm_taylorCoefficient`,
and `Fabius.eval_geometricUniformMomentRatFunc_one`. It packages the common
`a_n = d_n/n!` as one rational function, proves the global clearing identity
`[n]_X! a_n = P_n`, identifies safe evaluation with the actual inner and
exterior Taylor coefficients on `‖q‖ < 1` and `1 < ‖q‖`, and handles `q = 1`
through `[n]_1! = n!` rather than the literal totalized `0/0` quotient. In
composition with the algebraic polynomial API and the q-factorial/Pochhammer
identity, this makes canonical `thm:qF-moment-polynomial` **Exact**. It does
not assign analytic coefficient values at genuine poles or otherwise fill the
unit-circle MGF, germ-uniqueness, or pole-divisor boundary. The 1+4 leaf gives the historical 924/11,615
checkpoint.

The source-only `FabiusFunction.GeometricUniformMomentReciprocity` leaf has
one public definition and exactly five public theorems. Its exhaustive API is
`Fabius.geometricUniformComplexMomentGerm`,
`Fabius.geometricUniformComplexMomentGerm_of_norm_lt_one`,
`Fabius.geometricUniformComplexMomentGerm_of_one_lt_norm`,
`Fabius.analyticAt_geometricUniformComplexMomentGerm`,
`Fabius.geometricUniformComplexMomentGerm_reciprocity`, and
`Fabius.geometricUniformComplexMomentGerm_moment_convolution`. The combined
germ selects the inner product on `‖q‖ < 1` and the exterior reciprocal germ
on `1 < ‖q‖`. For `q != 0` and `‖q‖ != 1`, reciprocity is an `EventuallyEq`
at zero: `M_q(z) * M_(q⁻¹)(-z) = 1` on some neighbourhood. This local
boundary is essential because the inner product equals one at zero and is
therefore locally nonzero by continuity, but it can vanish farther away,
where Lean's total inverse prevents global cancellation. In the inner regime
the exterior definition rewrites the second factor as the local inverse of
the first; in the outer regime the same argument is applied to `q⁻¹`.
Leibniz' rule and the sign from `z ↦ -z` then give the exact binomial
convolution of all derivatives, with right side one at degree zero and zero
otherwise. These two theorems make canonical `thm:qF-reciprocity` **Exact**.
They do not assert a value at `q = 0` or on `‖q‖ = 1`, a global identity, an
explicit maximal germ disc, Mahler-germ uniqueness, or the exterior pole
divisor. The later merged-main additions give the pre-reciprocity
930/11,678 checkpoint; public complex-product differentiability gives
930/11,679, and the exhaustive reciprocity 1+5 leaf gives the historical
931/11,685 reciprocity checkpoint. The subsequently merged upstream
`DyadicBoundaryIdentity.lean` and `FinitePrefixThueMorseCollapse.lean` modules
add two facade modules and ten public declarations, giving the historical
dyadic/finite-prefix checkpoint 933/11,695. The incoming union adds one module
and fourteen public declarations: the new zero-definition/six-theorem
`ProuhetBaseTwoBridge.lean` module, one theorem added to
`DyadicBoundaryIdentity.lean`, and seven theorems added to
`ThueMorseNewmanSelfSimilarity.lean`. This gives the live 934/11,709 census,
with zero missing module headers and zero missing declaration comments.

The existing `FabiusFunction.ProbabilityLaplaceMoments` module then adds
exactly two public theorems:
`Fabius.ProbabilityRepresentation.weightedSumDistribution_real_Ici_eq_rvachevUp_of_nonneg`
and
`Fabius.ProbabilityRepresentation.integral_pow_weightedSumDistribution_eq_mul_intervalIntegral_rvachevUp`.
The first uses atomlessness to identify the closed tail of the canonical
weighted-sum law with `rvachevUp F t` for every `t >= 0`; composed with the
existing global reflection and nonnegative complement identities, it makes
`prop:up-tail` **Exact**, including the manuscript's `P(X >= t)` convention.
The second gives the full-law power-moment formula for every natural `n >= 1`
and makes `cor:up-moments` **Exact**. Degree zero is correctly excluded: its
left side is one while the displayed right side would vanish. These two
declarations give checkpoint 924/11,617 and promote no broader MGF,
fractional-moment, or complex-moment row.

The subsequent source-only
`FabiusFunction.RvachevLegendreBiorthogonality` leaf has the exhaustive public
surface one definition, `Fabius.rvachevLegendreAnalysisKernel`, and one
theorem, `Fabius.rvachevLegendreBiorthogonality`. The definition is exactly
the translated normalized Legendre analysis kernel in `def:leg-Lambda`; the
theorem proves the finite open-block Kronecker pairing for every nonzero
natural mesh `M`, every `l,m`, and `l <= padicValNat 2 M`. Thus
`def:leg-Lambda` and `thm:leg-biorthogonality` are **Exact/Complete**. The leaf
does not prove the larger support/smoothness/parity/Fourier--Bessel theorem
`thm:leg-Lambda` or the matrix-projector corollary. It gives the historical
925/11,619 census; the historical reciprocity census is 931/11,685 and the
historical dyadic/finite-prefix census is 933/11,695. The current live census
is 934/11,709, as recorded above, with zero missing module headers and zero
missing declaration comments.

The retained frontier, primary, walkthrough, geometric-q, and representation
PDFs predate these source-only overlays and claim no render parity.

The preceding source-only addition is
`FabiusFunction.GeometricRichardsonGenerating`, with three definitions and
seven theorems. Its
`Fabius.geometricLagrangeRichardson_generating` theorem is the exact formal
counterpart of canonical comb label `gq:thm:richardson-generating`; the module
also supplies the report-facing analytic companion
`Fabius.hasSum_geometricLagrangeRichardson_mul_pow` under strict nome
contraction and absolute summability. The retained canonical-frontier,
primary, walkthrough, and comb-synthesis PDFs all predate this crosswalk and
remain historical artifacts; none was rebuilt for this update.

The one-definition/seventeen-theorem
`FabiusFunction.GeometricUniformRealization` module transfers the canonical
law to arbitrary probability spaces carrying independent uniform coordinates;
the two-definition/one-theorem `FabiusFunction.RegularCentralQBinomialSum`
leaf proves `thm:regular-central-sum` under its exact product-nonvanishing
hypothesis. Together with the Lambert--Bernoulli and fixed-column-rate leaves,
they brought the preceding documentation checkpoint to 910 modules and 11,525
public declarations. The subsequent zero-definition/two-theorem
`GaussianBinomialGreaterOneAsymptotics`, one-definition/fourteen-theorem
`RvachevLagrangeNodesOnly`, and one-definition/eight-theorem
`GeometricUniformMomentPolynomial` leaves brought the next source checkpoint
to 913 modules and 11,551 public declarations. The subsequent zero-definition/
three-theorem `ThueMorseGammaTowerDifferential` leaf brought the next source
checkpoint to 914 modules and 11,554 public declarations. The one-theorem
strengthening of the existing `GeometricResidualMoments` module left the
module count unchanged and brought the next checkpoint to 914 modules and
11,555 public declarations. The zero-definition/one-theorem
`GeometricUniformMomentPolynomialBridge` leaf brought the next historical
checkpoint to 915 modules and 11,556 public declarations. The affine-Prouhet
strengthening of the existing `FinitePolynomialFunctional` module left the
module count unchanged and raised the next checkpoint to 915/11,557. The
one-definition/four-theorem `ThueMorseCornerIntegral` leaf then raised it to
916/11,562, and the zero-definition/three-theorem
`RvachevLegendreCentralSum` leaf brought the next checkpoint to 917 modules
and 11,565 public declarations. The complex moment-product leaf gave the
historical 918/11,568 checkpoint; `HalfQBinomialRootSimplicity` gave the actual
merged-main pre-local checkpoint 919/11,569; the exterior reciprocal-germ leaf
gave 920/11,572; and the sharp-degree leaf gave the historical 921/11,575
checkpoint. `RvachevLaurentLeading` then gives 922/11,582, and
`FinitePrefixAppellRecovery` gives the historical 923/11,610 checkpoint. The
RatFunc leaf gives the historical 924/11,615 checkpoint, the two probability
theorems give 924/11,617, and the Legendre biorthogonality 1+1 leaf gives the
historical 925/11,619 union. The subsequent merged-main additions give
930/11,678 before this reciprocity tranche, and the public differentiability
theorem plus the reciprocity leaf give the historical 931/11,685 union. The
subsequently merged upstream `DyadicBoundaryIdentity.lean` and
`FinitePrefixThueMorseCollapse.lean` modules add two modules and ten public
declarations, giving the historical dyadic/finite-prefix 933/11,695 union.
The incoming union adds one module and fourteen public declarations: the new
zero-definition/six-theorem `ProuhetBaseTwoBridge.lean` module, one theorem
added to `DyadicBoundaryIdentity.lean`, and seven theorems added to
`ThueMorseNewmanSelfSimilarity.lean`. This gives the live 934/11,709 union,
with zero documentation gaps.

`FabiusFunction.RvachevLaurentLeading` has one definition and six theorems.
Its manuscript-normalized punctured-neighborhood limit, together with the
Fourier-product coordinate, odd-core value and nonvanishing, generic cofactor
limit, and general integer-pole companion, makes
`is:p2:thm:Laurent-leading` Exact. Puncturing is necessary because Lean
totalizes inversion at a pole. No lower Laurent coefficients or later
Appell-coefficient asymptotics are promoted. This leaf first raised the
inverse package to 52 Lean-proved / 93 human-proved rows.

The eleven-definition/seventeen-theorem
`FabiusFunction.FinitePrefixAppellRecovery` leaf then makes both
`is:p2:thm:finite-prefix-expansion` and `is:p2:thm:exact-recovery` Exact. Its
uncentered and centered formulas hold for every `N,n`, including `N = 0`, at
the exact bases `1/2` and `1/4`; the recovery rows use respectively `n+1` and
`⌊n/2⌋+1` consecutive prefixes. The exact degrees `n` and `⌊n/2⌋` are outer
degrees in `Polynomial (Polynomial ℚ)`: a fixed-inner-`x` centered
specialization can drop degree, for example for odd `n` at `x = 0`. The
prefix moments are an algebraic finite-convolution model, not a new
random-variable, `HasLaw`, or analytic-MGF realization. These promotions give
the inverse package's historical 54 Lean-proved / 91 human-proved checkpoint.

The zero-definition/eight-theorem
`FabiusFunction.FinitePrefixThueMorseCollapse` leaf has the exhaustive public
surface `Appell.sum_thueMorseSign_mul_eval_poly`,
`Fabius.sum_thueMorseSign_mul_uncenteredDyadicPrefixAppellPolynomialRat`,
`Fabius.sum_thueMorseSign_mul_uncenteredDyadicPrefixAppellPolynomialRat_of_lt`,
`Fabius.sum_thueMorseSign_mul_uncenteredDyadicPrefixAppellPolynomialRat_self`,
`Fabius.sum_thueMorseSign_mul_centeredDyadicPrefixAppellPolynomialRat`,
`Fabius.sum_thueMorseSign_mul_centeredDyadicPrefixAppellPolynomialRat_succ`,
`Fabius.sum_thueMorseSign_mul_centeredDyadicPrefixAppellPolynomialRat_of_lt`,
and
`Fabius.sum_thueMorseSign_mul_centeredDyadicPrefixAppellPolynomialRat_self`.
Writing `s_N = 1 - 2^-N`, the uncentered theorem is exactly
`Σ_{k<2^N} ε_k A^unc_{N,n}(x+k/2^N) =
(-1)^N 2^-choose(N+1,2) n.descFactorial(N) x^(n-N)`. The centered theorem is
the sign-free identity
`Σ_{k<2^N} ε_k A^cen_{N,n}(x+s_N-2k/2^N) =
2^-choose(N,2) n.descFactorial(N) x^(n-N)`; at positive depth `N=m+1`, its
successor form uses the manuscript's literal grid `x+s_(m+1)-k/2^m`. The two
`_of_lt` theorems give Prouhet cancellation, and the two `_self` theorems give
the first nonzero constants. Hence `is:p2:thm:TM-uncentered`,
`is:p2:cor:Prouhet-canonical`, and `is:p2:thm:TM-centered` are
**Exact by composition**. The total main theorems include `N=0`, strengthening
the positive-depth formulas. This is rational coefficient algebra only: it
introduces no random variable or `HasLaw`, proves no analytic MGF, and makes
no Barnes-function identification. These three promotions put the 194-row
inverse concordance at 57 Lean-proved / 88 human-proved / 10 conjectural / 15
open / 24 nonassertoric rows.

The existing `FabiusFunction.ProbabilityLaplaceMoments` module now adds
exactly two public theorems:
`Fabius.weightedSumDistribution_real_Ici_eq_rvachevUp_of_nonneg` and
`Fabius.integral_pow_weightedSumDistribution_eq_mul_intervalIntegral_rvachevUp`.
Atomlessness changes the established strict tail to the manuscript's closed
event `X ≥ t` for every `t ≥ 0`; survival layer cake gives
`E[X^n] = n ∫₀¹ t^(n-1) up(t) dt` for every natural `n ≥ 1`, with the
expectation over the full weighted-sum law. Composed with the existing global
up/Fabius identities, these make `prop:up-tail` and `cor:up-moments` Exact.
No density assertion or degree-zero extension is claimed.

`FabiusFunction.RvachevLegendreBiorthogonality` has exactly one definition,
`Fabius.rvachevLegendreAnalysisKernel`, and one theorem,
`Fabius.rvachevLegendreBiorthogonality`. For `F : BoundedFabius` with
`IsFabius F`, natural `M ≠ 0`, arbitrary synthesis and analysis degrees
`l,m`, and `l ≤ padicValNat 2 M`, it proves the literal normalized open-block
identity
`M⁻¹ ∑_{-2M<k<2M} Q_l⁻(k/M) Λ_m(k/M) = if m=l then 1 else 0`.
The proof integrates the exact degree-`l` Rvachev synthesis against the
normalized Legendre mode and applies orthogonality; there is no restriction
on `m`. Thus `thm:leg-biorthogonality` is Exact. The larger
`cor:leg-biorthogonal-matrices` remains Partial because the reverse
projector, rank/trace, and Cauchy--Binet clauses are not Lean-covered; the
leaf also makes no dyadic-rationality claim for the analysis kernel.

The zero-definition/one-theorem
`FabiusFunction.HalfQBinomialRootSimplicity` leaf adds
`Fabius.halfQBinomial_sum_rootMultiplicity_two_pow`. Composed with the
existing rational zero classifier and Gaussian/half-q coefficient identity,
it makes `cor:halfbase-root-locus` Exact under the canonical rational-polynomial
and rational-root convention. Injective scalar extension preserves
the displayed multiplicities, but the leaf does not classify all roots over
every extension field. After the reciprocity promotion, the q
forward ledger is now 182 Exact / 78 Partial / 14 None / 8 interface rows,
and its source concordance is 95 Lean-proved / 383 human-proved frontier /
60 non-applicable / 9 conjectures.

`FabiusFunction.GaussianBinomialGreaterOneAsymptotics` has exactly the two
theorems
`Fabius.gaussianBinomial_gt_one_fixedColumn_relativeError_isBigO` and
`Fabius.gaussianBinomial_gt_one_central_isEquivalent`. For real `q > 1`, they
prove the printed normalized fixed-column error at rate
`(q⁻¹)^(n-k+1)` and
`[2m,m]_q ~ q^(m*m) (q⁻¹;q⁻¹)_∞⁻¹`. Together with the existing evaluated
reciprocity theorem, they make `cor:qgreaterone` Exact. Natural subtraction
is total in the rate theorem and reciprocity is used only eventually when
`k ≤ n`; no shifted-central, non-real, or wider-nome result is asserted.

`FabiusFunction.RvachevLagrangeNodesOnly` has the one definition
`Fabius.rvachevDeconvolvedPolynomialRat` and exactly fourteen theorems:
`Fabius.map_rvachevDeconvolvedPolynomialRat`,
`Fabius.rvachevDeconvolvedPolynomial_eq_sum_appell`,
`Fabius.eval_rvachevDeconvolvedPolynomial_eq_sum_even_iterateDerivative`,
`Fabius.rvachevDeconvolvedPolynomial_prod_X_sub_C_eq_sum_appell`,
`Fabius.eval_rvachevDeconvolvedPolynomial_lagrangeBasis_eq_sum_even_iterateDerivative`,
`Fabius.eval_rvachevDeconvolvedPolynomial_lagrangeBasis_eq_nodalWeight_mul_sum_appell`,
`Fabius.lagrangeRvachevDecoder_eq_nodalWeight_mul_sum_appell`,
`Fabius.map_lagrangeBasis_ratCast`,
`Fabius.map_rvachevDeconvolvedPolynomialRat_lagrangeBasis`,
`Fabius.lagrangeRvachevDecoder_eq_ratCast`,
`Fabius.rvachevRawMomentRat_eq_centeredRvachevFullMoment`,
`Fabius.momentCumulant_rvachevRawMomentRat_eq_centeredRvachevFullCumulant`,
`Fabius.momentCumulant_rvachevRawMomentRat_even_eq_bernoulliMersenne`, and
`Fabius.rvachevReciprocalMomentRat_eq_completeBellPolynomial_neg_centeredCumulant`.
By composition these give an Exact/Complete counterpart of
`cor:lag-nodes-only`: the ordinary-derivative and raw omitted-node Appell
forms, coefficientwise rational descent and rational lattice samples, and
the formal complete-Bell/Bernoulli--Mersenne coefficient description.
Rationality is asserted only at rational evaluation points, and the Bell
identity is formal coefficient algebra rather than analytic reciprocal-MGF
convergence. There is no single nodes-only wrapper theorem. Independently,
the existing `LagrangeRvachevSynthesis` declarations
`Fabius.normalized_sum_Ioo_lagrangeRvachevDecoder_mul_shifted_rvachevUp` and
`Fabius.sum_Ioo_lagrangeRvachevAtomCoefficient_mul_shifted_rvachevUp` make
`thm:lag-cardinal` Exact/Complete by assembly. The still-Partial
`thm:lag-right-inverse` and decoder optimality are not promoted.

`FabiusFunction.ThueMorseGammaTowerDifferential` has no definitions and
exactly three theorems:
`Fabius.hasDerivAt_mellin_mellinKernel_parameter`,
`Fabius.hasDerivAt_thueMorseGammaLog_succ`, and
`Fabius.iteratedDeriv_thueMorseGammaLog`. They prove the arbitrary-complex-
spectral Mellin parameter derivative, the successor law
`L_(r+1)'(a) = (r+1)L_r(a)`, and the full falling-factorial iteration for
`k ≤ r`, always under `0 < a`. Consequently `p2:thm:gamma-tower` is Exact
when its logarithm is read as the existing chosen GammaLog coordinate. No
principal-`Complex.log` identity or nonpositive-parameter differential law
is claimed. These additions are source-only; the retained frontier and
package PDFs remain historical renders and make no current-parity claim.

`FabiusFunction.ThueMorseCornerIntegral` has one public definition and four
theorems: `Fabius.centeredBoxIntegral`,
`Fabius.centeredBoxIntegral_zero`, `Fabius.centeredBoxIntegral_succ`,
`Fabius.symmetricMixedDifference_range_eq_centeredBoxIntegral`, and
`Fabius.symmetricMixedDifference_univ_eq_centeredBoxIntegral`. Together with
the existing `ThueMorseSymmetricDifference` algebra, they make
`thm:TM-corner` Exact/Complete exactly by composition. The range theorem assumes
nonnegative half-steps, `IsOpen I`, `OrdConnected I`,
`ContDiffOn ℝ N g I`, and containment of the full closed symmetric segment
in `I`; it is local rather than a global smoothness shortcut and includes
zero steps and `N = 0`. It is real-valued and fixes the recursive integration
order. The following Walsh conditional-expectation construction and its
`2^(-N)` normalization remain outside this result.

`FabiusFunction.RvachevLegendreCentralSum` has no definitions and exactly
three theorems: `Fabius.eval_legendrePolynomial_even_zero`,
`Fabius.eval_rvachevLegendreDeconvolutionPolynomial_even`, and
`Fabius.rvachevLegendreCentralSum`. For every `F : BoundedFabius` with
`IsFabius F` and every `n`, including `n = 0`, the last theorem proves the
literal finite central cancellation at mesh `4^n` by combining the normalized
Legendre value at zero, evenness, compact-support truncation, and pairing of
the positive and negative indices. This makes only `cor:leg-central-sum`
Exact; it adds no Jacobi decoder formula, reverse spectral closure, or larger
Lagrange right-inverse theorem. These source-only declarations are not
rendered by the retained frontier or synthesis PDFs.

The final source-only `FabiusFunction.GaussianBinomialFixedColumnRate` leaf has
no definitions and ten theorems:
`Fabius.norm_finiteQPochhammerIn_pow_sub_one_le_exp`,
`Fabius.norm_finiteQPochhammerIn_pow_sub_one_le`,
`Fabius.norm_finiteQPochhammerIn_self_mul_gaussianBinomial_sub_one_le`,
`Fabius.norm_gaussianBinomial_sub_inv_finiteQPochhammerIn_le`,
`Fabius.norm_gaussianBinomial_add_sub_inv_finiteQPochhammerIn_le`,
`Fabius.tendsto_gaussianBinomial_add_atTop`,
`Fabius.gaussianBinomial_fixedColumn_relativeError_isBigO`,
`Fabius.gaussianBinomial_shifted_fixedColumn_relativeError_isBigO`,
`Fabius.gaussianBinomial_fixedColumn_error_isBigO`, and
`Fabius.gaussianBinomial_shifted_fixedColumn_error_isBigO`. In a normed
commutative ring with normalized multiplicative norm, `‖q‖ ≤ 1` gives the
exponential and elementary bounds on `‖(q^m;q)_k-1‖` and the denominator-free
relative Gaussian bound, the last meaningful even at roots of unity. Over a
normed field, `‖q‖ < 1` gives fixed and shifted nonasymptotic bounds, shifted
convergence, and relative/additive `IsBigO` laws at `q^(n-k+1)` and `q^(n+1)`.
No completeness or `q ≠ 0` hypothesis is imposed, and the constant is not
claimed sharp. Together with the existing fixed-column limit, these results
make every clause of `thm:fixed-column-limit` exact; the relative pair encodes
the two displayed multiplicative `1+O` estimates.

The source-only `FabiusFunction.RvachevAppellHasse` leaf has one definition,
`Fabius.Appell.polynomialTransform`, and exactly fourteen theorems:
`Fabius.Appell.polynomialTransform_apply`,
`Fabius.Appell.polynomialTransform_monomial`,
`Fabius.Appell.polynomialTransform_eq_sum_hasseDeriv_of_natDegree_lt`,
`Fabius.Appell.polynomialTransform_eq_sum_hasseDeriv`,
`Fabius.rvachevReciprocalMomentRat_odd`,
`Fabius.rvachevDeconvolutionLinearMap_eq_appellPolynomialTransform`,
`Fabius.rvachevDeconvolvedPolynomial_eq_sum_even_hasseDeriv`,
`Fabius.eval_hasseDeriv_prod_X_sub_C_eq_elementarySymmetricEval`,
`Fabius.eval_rvachevDeconvolvedPolynomial_prod_X_sub_C`,
`Fabius.eval_rvachevDeconvolvedPolynomial_qFallingPower`,
`Fabius.lagrangeBasis_eq_nodalWeight_mul_prod_X_sub_C`,
`Fabius.lagrangeRvachevDecoder_eq_nodalWeight_mul_sum`,
`Fabius.geometric_nodalWeight_eq_geometricQPochhammer`, and
`Fabius.geometric_lagrangeRvachevDecoder_eq`. It identifies the generic finite
Appell transform with a Hasse-derivative sum, proves odd reciprocal centered
Rvachev moments vanish and hence gives the even-Hasse deconvolution, expands
root products through elementary symmetric polynomials, and specializes this
to q-falling powers and the full geometric Lagrange--Rvachev decoder. Thus
`gq:prop:q-Appell-falling` is exact by composition with
`Fabius.normalized_sum_Ioo_rvachevDeconvolvedPolynomial_mul_shifted_rvachevUp`,
and `gq:thm:gaussian-Appell-decoder` is exact by composition with
`Fabius.normalized_sum_Ioo_lagrangeRvachevDecoder_mul_shifted_rvachevUp`;
those separate synthesis theorems, rather than this algebraic leaf alone,
supply atom reconstruction. Here gamma is the formal reciprocal-moment
sequence `rvachevReciprocalMomentRat`, not a claim of analytic reciprocal-MGF
convergence. The displayed algebra is total at zero or colliding nodes because
field inversion is total, while the manuscript cardinal use assumes `c > 0`
and `0 < q < 1` (together with its mesh, interval, and degree hypotheses).
No larger matrix right inverse or decoder-optimality result is asserted.

The newest source-only addition leaves the module count unchanged and adds
three theorems to `FabiusFunction.GaussianBinomialCumulants`: the explicit
second derivative at one
`Fabius.eval_one_derivative_derivative_gaussianBinomial_X`, the division-free
raw second moment `Fabius.twelve_mul_secondMoment_gaussianBinomial_eval_one`,
and the division-free variance numerator
`Fabius.twelve_mul_varianceNumerator_gaussianBinomial_eval_one`. The first is a
characteristic-zero field identity on `k ≤ n`; the cleared identities are total
over every commutative semiring, including the above-row zero case. Their
probability language is the normalized-generating-polynomial interpretation of
algebraic identities, not a new probability-space construction.

The 1 September 2026 source-only q-Pochhammer overlay is likewise newer than
the retained PDFs.  The new `QPochhammerEntire.lean` leaf has zero definitions
and five theorems: for a fixed complex nome with norm less than one it proves
local uniform convergence of the infinite product, differentiability in the
symbol, the division-free factor-zero criterion, the reciprocal-power zero
lattice when the nome is nonzero, and analytic order one at every zero.  This
promotes only `thm:poch-entire` in the consolidated q-series monograph.  The
same current source also crosswalks the generic infinite/dissection API and
the later Euler, q-binomial, Jacobi, quantum-binomial, Rogers--Szegő,
cyclotomic-divisibility, q-Catalan, primitive-root-block, q-Lucas, Jackson
q-beta, geometric Newton-interpolation, integer/complex upper Gaussian, and
q-Pfaff--Saalschütz, and noncommutative q-multinomial tranches. Its 282-result
forward status totals are now 182 Exact / 78 Partial / 14 None / 8 interface:
`p7:thm:Pn` moves Partial-to-Exact and `prop:qF-P-degree-sharp` moves
None-to-Exact, while the RatFunc assembly now moves
`thm:qF-moment-polynomial` Partial-to-Exact and the probability extension
moves `prop:up-tail` and `cor:up-moments` Partial-to-Exact. The reciprocity
leaf additionally moves `thm:qF-reciprocity` None-to-Exact.
`FabiusFunction.GeometricResidualMoments` now has zero definitions and nine
public theorems. Its existing
`Fabius.sum_geometricLagrangeWeight_mul_scaled_geometric_pow_of_pos` supplies
the displayed positive-degree scaled-geometric moment formula, while the new
`Fabius.sum_geometricLagrangeWeight_mul_eval_scaled_geometric` supplies exact
evaluation at zero for every polynomial of degree at most the interpolation
order. Together they make `cor:scaled-geometric-moments` Exact by composition.
Both results hold over an arbitrary field under injectivity of the nodes
`k ↦ q^k` on `range (p + 1)`; the polynomial theorem permits every scale `c`,
including zero, and therefore subsumes the manuscript's `c ≠ 0` case. No
larger interpolation or node-collision claim is made.
The new `Fabius.sum_weight_mul_eval_affine_of_topCoeff_extractor` theorem in
the existing zero-definition/sixteen-theorem
`FinitePolynomialFunctional.lean` module transports a same-ring
top-coefficient extractor across `a + b*x` over every commutative semiring.
Composed with
`Fabius.halfQBinomial_negativeDyadic_polynomial_sum_eq_mersenne`, it makes
`cor:geometric-prouhet-affine` Exact under the established rational-polynomial
half-base convention. No `b ≠ 0` or distinct-node premise is needed, and the
cases `b = 0` and `n = 0` are included; this does not assert a half-base
extractor over arbitrary coefficient rings.
The partition-symmetry row is exact; the basic geometric-uniform row is now
exact because `GeometricUniformRealization.lean` transfers the canonical law
to an arbitrary ambient probability space carrying independent coordinates
with the uniform marginal law. The fixed-column Gaussian row is also exact by
the fixed and shifted limits and relative geometric-rate theorems above. The
outer spectral product now has an exact
locally-uniform/normal-convergence theorem; the compound centered/MGF and full
exterior uniqueness/pole-divisor layers remain partial.

The final terminating-basic-hypergeometric inventory is
`TwoPhiOneReversal.lean` (2 definitions + 12 theorems) and
`QChuVandermonde.lean` (10 theorems). The two q-Chu evaluations and the
terminating reversal lemma are exact for the actual `twoPhiOne` tsum. The
claim that reversal alone proves the second evaluation on its full displayed
domain remains partial: the compiled by-reversal theorem retains `C ≠ 0` and
`(A;q)_n ≠ 0`, while the unrestricted theorem uses finite q-Cauchy directly;
no rational-continuation or cleared commutative-ring extension is claimed.

The retained 389-page A4 PDF (3,254,138 bytes; historical SHA-256
`b8add607c85ee35be98dabf36879e1d45fb093c6b453e93679c80295fae715bc`)
was synchronized to the preceding 16,339-line, 810,779-byte source checkpoint
(SHA-256 `14c444feb14c435bc300becd9c8cd2765c1e96f608dd79da462becc41b28ed22`).
The live source and its current theorem promotions postdate that artifact, so
no current source/PDF parity is claimed. No live checksum manifest or
current-source digest is maintained.

The current finite-moment/Legendre/Gaunt crosswalk covers eleven modules with
20 public definitions and 109 public theorems, 129 declarations in all. The
new leaves are `LegendreGauntClosedForm.lean` (2 definitions, 25 theorems) and
`FabiusLegendreGauntClosedForm.lean` (0 definitions, 3 theorems). They define
the parity-and-weak-triangle support and the total rational square of the
integer-index zero-row Wigner datum, prove the central-binomial and factorial
forms, identify both rational and real Legendre Gaunt coefficients with twice
that square, characterize their exact zero/positive support, and rewrite the
finite rational and real up-law Gram-entry sums accordingly. This is a
square-level result only: it chooses no signed Wigner symbol or phase and adds
no half-integer, nonzero-magnetic-index, general `3j`/`6j`/`9j`, orthogonality,
recoupling, or infinite-series theory.

The volume consolidates the eleven former standalone research notebooks into
six thematic syntheses, followed by the later primary-exposition gap register:
reusable probability/discrete/asymptotic engines, repeated integration, the
exact dyadic web, dyadic endpoint asymptotics, quantitative Thue–Morse
convergence, and inverse/small-argument saddle analysis. It preserves their
natural-language arguments, symbolic computations, numerical evidence,
warnings, citations, provenance, and explicit proof obligations without
allowing any of that material to be mistaken for the formalization-backed
primary exposition.

Some passages use already-formalized results as inputs. That does not certify
the subsequent deductions. Conversely, when one claim is promoted to the
primary exposition, adjacent exploratory material remains here until its own
exact proof obligation is discharged.

## Placement and promotion rule

A mathematical claim belongs in the primary exposition only when a current
public Lean declaration proves the exact statement, including its domain,
normalization, hypotheses, endpoint convention, and conclusion or error term.
The declaration and its defining module must be recorded next to the claim or
in the primary document's audit map.

A related definition, a theorem with stronger hypotheses or weaker
conclusions, an executable computation, a paper citation, a numerical match,
an `.olean` file, an agent report, or an apparently immediate derivation is not
an exact counterpart. Material supported only in one of those ways stays in
this volume, however standard or plausible it appears.

Promotion is claim-by-claim:

1. Verify the exact Lean declaration in current source.
2. Integrate the supported material organically into
   [`Fabius_Function_and_Rvachev_Up.tex`](../Fabius_Function_and_Rvachev_Up/Fabius_Function_and_Rvachev_Up.tex)
   without duplicating material already there.
3. Remove or relabel the matching frontier obligation while preserving every
   adjacent claim that remains unformalized.
4. Rebuild and inspect every affected PDF.

Research drafts are temporary inboxes, not archives. Once every part of a
draft has either been integrated into the primary exposition or preserved in
the canonical frontier volume, delete the processed draft. Delete the draft
directory itself when it becomes empty.

## Consolidation provenance

The unified source records a provenance banner and the historically supplied
SHA-256 value for every absorbed document. A printed checksum is provenance
metadata, not a formalization claim; where no reachable repository blob
reproduces it, the canonical TeX labels it explicitly as unverified rather than
silently treating it as authenticated. The source snapshots consolidated on
25 August 2026 were recorded as follows:

| Former source | SHA-256 |
| --- | --- |
| `Fabius_Dyadic_Formulae_and_Alternative_Representations/Fabius_Dyadic_Formulae_and_Alternative_Representations.tex` | `462276b10fcd32b0446deb7cfedc4ec07c2ae55dbd333d5ff9b1d98f07df89e1` |
| `Fabius_Dyadic_q_Connections/Fabius_Dyadic_q_Connections.tex` | `81a0a911ac7ab28e12c6b87ccaf76ffccaf32e48f873abff18fb7a2d01bcf3e5` |
| `Fabius_Dyadic_Asymptotic_Bridge/Fabius_Dyadic_Asymptotic_Bridge.tex` | `c5ad7c5298d958ab63f459a3e246c2293d3020525223bc05ef2d0e1edab58f10` |
| `Fabius_Dyadic_Formulae_to_Asymptotics/Fabius_Dyadic_Formulae_to_Asymptotics.tex` | `6e98efd3afc402159a7f080e8604c951d5bc51be4a73383da67c1241d46d54ca` |
| `Fabius_Integration_Research_Frontiers/Fabius_Integration_Research_Frontiers.tex` | `21222ae5a8c64cf556dac562fd66943ae0b6ed881408e23e37edfa9113bdecbd` |
| `Fabius_Inverse_and_Saddle_Research_Frontiers/Fabius_Inverse_and_Saddle_Research_Frontiers.tex` | `f9d8605761aaaa1b2c2af83e3c5c55dcd6acfc847402163458b03b68c7b35ff8` |
| `Fabius_Thue_Morse_Convergence_Rate/Fabius_Thue_Morse_Convergence_Rate.tex` | `577c5f3426def68a774fedf3fce61552d32200c8da526ace44178f2a8995a6d3` |
| `Fabius_Thue_Morse_Convergence_Rate-2/Fabius_Thue_Morse_Convergence_Rates.tex` | `384d69b461cb94af33f1c080703e269ea77104405d1940413f1944172b3312c0` |
| `Repeated_Integration_and_Rvachev_Up/Repeated_Integration_and_Rvachev_Up.tex` | `eadcb4b414ac93723a91acbd5062d44340f78134a2cecbc18f7d7ba67eb2c9be` |
| `Rvachev_Up_from_Repeated_Integration-2/Rvachev_Up_from_Repeated_Integration.tex` | `fad16072df30d9e6eb5df03da57dd217769180730581f1dfd19fa5be0d16b262` |
| `Small_Argument_Asymptotics/Small_Argument_Asymptotics.tex` | `85f51a20fc7b6bdf3b1d049ec4506f508aee3c4cd70554e6a68cbcc30977cb0b` |
| `Primary_Exposition_Gap_Register/Primary_Exposition_Gap_Register.tex` | `06c7b888d9601b67ad7a5c0aee3f087d44d9ecaaa9abfb3bf3edfda4bd29c0d1` |

The eleven notebooks are represented by six thematic syntheses, followed by
the post-audit gap register. Overlapping dossiers were merged around their
stronger backbones: independent derivations, sharper later statements, distinct
warnings, numerical data, figures, and useful provenance remain, while
genuinely redundant repetitions are compressed and cross-referenced. The
recorded checksums identify the intended absorbed snapshots subject to the
verification qualification above; subsequent synthesis and status corrections
are tracked by Git history in the canonical source.

## Draft layout

The draft inboxes under [`drafts/`](drafts/) are grouped thematically
(2026-08-28): `rvachev_up_fourier_decay/` (the Fourier-decay corpus),
`thue-morse/`, `exponents-and-q-series/`, `spectra-and-arithmetic/`,
`integration-and-transforms/`, `inverse-and-sampling/`,
`representations/`, `frontier-compilations/`, `lambert-w/` (added
when four articles on the Lambert W function itself arrived), and
`series-and-transseries/` (added 2026-09-02 for packages about the
formal-series calculus itself), with new
archives arriving through `drafts/incoming/` (see its README for the
protocol).

The inverse group publishes the canonical source
[*Inverse Fabius Theory: Analyticity, Asymptotics, Computability, and Dyadic
Sampling*](drafts/inverse-and-sampling/Inverse_Fabius_Analyticity_Asymptotics_and_Computability/inverse_fabius_theory.tex)
([PDF](drafts/inverse-and-sampling/Inverse_Fabius_Analyticity_Asymptotics_and_Computability/inverse_fabius_theory.pdf)).
Its immutable extraction input is pinned at
`0a0cdabeb72a6f7d67cfdfb76d02a8f7381c7bf7`; all 194 source-result rows have
reviewed dispositions, all 88 files in the two superseded source subgroups have
asset dispositions, and the deduplicated live asset ledger covers 63 retained
payloads. The former package paths, source hashes, nested lineage, and recovery
revisions remain in the package's
[`PROVENANCE.md`](drafts/inverse-and-sampling/Inverse_Fabius_Analyticity_Asymptotics_and_Computability/PROVENANCE.md).
Its retained 134-page, 2,027,726-byte A4 publication has SHA-256
`22bc68d855ad04dde9654e9fbd20b3ba7f05a33e3c5df0e5b80bb8991c94b41d`.
The package README records that historical checkpoint's clean three-pass
build, font preflight, and visual inspection.  The current 23-input source
closure has SHA-256
`aedf007c2cd150b1f83de6d8996b4bf31e267b3dbcec2d5cd4720f5d92122bdb`
and postdates the retained PDF, so a fresh three-pass build is required before
source/PDF synchronization may be claimed. The reviewed concordance classifies
54 source rows as Lean-proved and 91 as human-proved frontier results, with 10
conjectures, 15 open problems, and 24 non-applicable rows. Its newest exact
matches include the punctured leading-Laurent theorem and the full uncentered/
centered finite-prefix Appell expansion and exact-recovery pair described
above; these do not assert lower Laurent coefficients or a probabilistic
realization of the algebraic prefix model.

Later the same day the groups other than the Fourier-decay corpus were
**consolidated into volumes**, in two styles: the original members were
merged mechanically — one document per group, absorbing the member
drafts verbatim with per-part label prefixes (the later second-wave
integral-transforms arrival was folded into that volume the same way,
as Part XII) — while the closely overlapping arrivals of waves two
through six were merged **editorially** into additional volumes
(`inverse-and-sampling/comb-interpolation/comb_interpolation_synthesis/`, the
former `inverse-and-sampling/inverse-asymptotics-and-computability/Inverse_Endpoint_All_Orders/`
now recorded as an input to the canonical inverse synthesis, and
`representations/Up_Polynomial_Synthesis/`): shared theorems stated
once with the best proof, unified notation, cross-source constants
verified, all source-specific material retained.  Waves seven through
thirteen (all 2026-08-28) were then absorbed into these standing
volumes rather than opening new ones: the lattice draft became a
chapter of `Up_Polynomial_Synthesis`; the two representation volumes
were unified into the single eight-part `Representation_Frontiers`;
the finite-sinc, Fourier-image, transport-geometry, and
atomic-splines reports became Parts III–VI of
`Exponents_and_q_Series_Frontiers`; and the three
Euler–Maclaurin/exhaustion/phase reports were merged editorially into
the comb volume's Bernoulli-periodization section, where the
consolidation itself settled six previously open items (the spectral
positivity D(2r) > 0, the twisted positivity at every odd scale with
its Thue–Morse sign law, both phase-classification conjectures, the
alternating Bernoulli-moment sign law, and the odd half of the sharp
threshold).  The fourteenth and fifteenth waves — a second and a third
independent reconstruction of Rvachev's atomic-functions chapter —
were merged editorially into that volume's Part VI, adding the
fractal-string/tube-formula geometry, the local-degree law with its
critical exponential limit, quantitative Gaussian and uniform
parameter limits, the exact general-base Gamma–zeta Laplace
decomposition (settling the transform-level half of the
periodic-Lambert conjecture), the two Fup hierarchies (the canonical
ladder and the classical narrowing family with its triangular
reconstruction and Gaussian regime), signed gap leading coefficients,
derivative equimeasurability with the full L^p ladder, and the edge
pantograph equations.  The sixteenth and seventeenth waves — same-topic
twins on the signed/reciprocal parameter orbit of the geometric-uniform
family — were merged editorially as that volume's Part VII, adding
affine sign conjugacy, reciprocal germ inversion with its
Laplace/vertical-line dual, geometric multisection, the two-nome
Pochhammer–Prouhet partition function, the exact inverse-geometric
endpoint lattice with its jets and two-term asymptotics, and the
resolution of the periodic-cocycle conjecture via Part VI's exact
Laplace decomposition.  Eight revised or expanded editions of the atomic-functions
reports were then merged into Part VI, adding the spectral
Stieltjes–Wigert bridge, the distance-Mellin law, the q-Gaussian
derivative Gram geometry with theta-function Riesz bounds, the
log-Weibull jet-intermittency law, a proof of the Fup_n Edgeworth
register conjecture, then — from the audit-aware expanded editions —
the closed Gaussian-binomial Gram–Schmidt orthogonalization with its
Rogers–Szegő identification, the wrapped-heat-kernel circle model,
the MacMahon determinant constant with triple-product Riesz bounds,
the physical-space Stieltjes–Wigert differential ladder (identified
during the merge with the Gram–Schmidt vectors, a check that caught
and repaired a sign-convention slip in that theorem's first
printing), the derivative-jet Gram determinants, the autocorrelation
germ with zero Taylor radius, the exact derivative-energy
factorization with its Bernoulli-convolution limit and entropy laws,
the nodal-polynomial and exact-inverse closure of the orthogonalization
with its minimum-phase theta whitening filter, the Schur-minor strict
total positivity of the derivative Gram kernel, the two-term jet tail
with its sharp Orlicz threshold, the highest-jet partial-theta law with
the joint jet–distance transform, and eight register conjectures
(overlap-regime theta and energy, explicit spectral null modes, infinite
dual tower, finite-section boundary layer, centered staircase limit set,
partial-theta recreation of the complex dimensions, and graph-directed
Gaussian-binomial prediction).  For provenance the first of
these editions shipped the Russian source scan itself; the scan and
the raw OCR were deleted once their recoverable content was merged
and verified against the volume (SHA-256 hashes stay in the volume's
provenance list; git history archives the files; two later editions
re-shipped byte-identical copies, likewise not retained).  A new
`lambert-w/` group collected four independently written articles on
the Lambert W function itself; they were merged editorially into the
single consolidated volume `Lambert_W_Guide/` (the most complete
treatment as the body, the other three's unique layers in a
complements section, a four-way concordance, and a corpus-role
section tying W₋₁ to the endpoint theory).  Six polynomial-logarithmic
transseries articles that arrived on 2026-09-01 were filed in that group
too, since Lambert W is their guiding example; because their subject is
the transseries calculus rather than the function, they were regrouped on
2026-09-02 into the new `series-and-transseries/` group, under its
`polynomial-logarithmic-transseries/` subgroup.  That move was verbatim —
no source or PDF changed — and the same day the six were merged editorially
into the single canonical volume *Polynomial–Logarithmic Transseries:
Algebra, Composition, Series Reversal, and the Lambert W Archetype* (412 A4
pages).  None of the six was a superset of the others and each contributed a
layer no other supplied, so the merge kept every distinct result and collapsed
only repetition.  Every statement in the volume carries a proof: where a source
asserted a result without one it was supplied, and where a source claimed
analytic validity on the strength of formal algebra the claim was weakened to
what the algebra establishes, each repair marked at the point of repair and
collected in the volume's ledger.  Its formalization register records what the
Lean corpus does and does not cover, distinguishing a formalized *neighbour* —
the corpus proves Lagrange inversion and the Lambert series at the **origin**,
while this volume works at **infinity** — from actual coverage.  The absorbed
directories were deleted after a residue audit.  By the same precedent, a
standalone reference monograph on q-Pochhammer symbols and q-binomial
coefficients — the machinery consumed by the exponents
volume's Parts II/VI/VII and the formalized Gaussian-binomial core —
was filed as a second member of `exponents-and-q-series/` rather than
merged into the frontier volume, after an on-arrival audit (symbolic
re-verification of its core theorems, 30-digit numerical checks of
its two newest identities, one repaired majorant).  Initially 96 pages, the
post-consolidation monograph now has 212 A4 pages. Several volumes'
part-boundary section numbering and
page-counter handling were repaired along the way (edits are marked
`% ed.:` in the sources).  Every volume carries
a provenance section with each absorbed member's SHA-256; the absorbed
directories were deleted (git history is the archive). The Fourier-decay
corpus initially stayed separate so its independent reports could be audited;
on 2026-08-31 it too was consolidated, editorially, into one corrected proof
volume. Its source concordance and immutable pre-consolidation Git links retain
that audit evidence without leaving superseded documents live (see its README).
Each group carries a
`README.md` stating its purpose and contents, and
[`drafts/MANIFEST.md`](drafts/MANIFEST.md) is the global inventory:
every volume with its title and the previous paths of what it
absorbed. Path strings *inside* the documents predate the grouping and
are resolved through that manifest; the mechanical steps changed no
member's mathematical content, and the editorial merges record their
deduplication decisions in their provenance appendices.

## Maintenance

New unformalized mathematical write-ups must be merged into the canonical
LaTeX volume rather than retained as permanent parallel dossiers. A temporary
subdirectory may serve as an inbox during concurrent work (placed in the
matching thematic group above, and added to `drafts/MANIFEST.md`), but it
must be audited, absorbed, and removed promptly — updating the manifest and
group README on removal.

### Consistency audits

The scripts under [`scripts/`](scripts/) check the volumes and module
documentation against the Lean corpus. `scripts/audit_all.sh` runs all four
hard checks and exits nonzero if any hard check fails; run it before pushing
any change that touches either side. The stale-claim and crosswalk-coverage
surveys are advisory; the build-log checker is run separately after compiling
a changed volume.

- `scripts/audit_facade_reachability.py` — every module on disk is reachable from the
  library root `FabiusFunction.lean`. A newly added leaf module that nothing
  imports is never elaborated by `lake build FabiusFunction`, so a whole-library
  build would report success while silently skipping it.
- `scripts/audit_crosswalk_names.py` — every `Fabius.*` name cited in a `.tex` file
  resolves to a declaration or a namespace that exists in the corpus. The
  corpus is scanned with a namespace stack, so dotted citations such as
  `Fabius.SaddleExpansion.expCoeff` are matched whole rather than truncated at
  the first dot. A citation that no longer resolves usually means a Lean
  declaration was renamed without its crosswalk being updated.
- `scripts/audit_duplicate_names.py` — no two modules declare the same non-private,
  fully qualified name. A collision generally means that a new module has
  reproved an existing result and should import it instead.
- `scripts/audit_docstring_names.py` — backticked identifiers advertised in bulleted
  module-docstring declarations resolve in the corpus. An unresolved
  `Fabius.*` name is a hard failure. An unresolved unqualified name is advisory
  only, because it may be a root-namespace Mathlib declaration that this
  lexical audit cannot distinguish from a stale local name.
- `scripts/audit_stale_claims.py` and `scripts/audit_crosswalk_coverage.py` — advisory worklists
  for contradictory “open” claims and theorem environments lacking either a
  nearby Lean citation or an explicit formalization disclaimer.

The four hard checks have no standing exceptions. If one starts reporting a
failure that looks spurious, fix the script rather than carrying the exception:
the three false positives the crosswalk used to report were hiding about ninety
citations that were only being checked at their first component. Docstring-name
advisories are printed for review but intentionally do not change the exit
status.

`scripts/audit_overfull.py <file.log> [threshold_pt]` is a separate post-build
helper, not part of `scripts/audit_all.sh`: it parses both horizontal excess widths and vertical
excess heights without the shell-escaping ambiguity of the old `grep` pipeline,
and exits nonzero above the chosen threshold.  Output-routine vertical boxes,
which carry no source-line range in a LaTeX log, are reported explicitly rather
than mistaken for a checker failure.

Build the canonical document with exactly three `pdflatex` passes, inspect the
rendered PDF, and commit the PDF with its source. A coordinator may authorize a
source-only feature-branch checkpoint for semantic review before the rebuild;
such a checkpoint is never promoted to `main`. Before integration into
`origin/main`, the matching rendered PDF must be rebuilt, inspected, and
committed. Never advance `main` with a TeX/PDF mismatch. Do not commit `.aux`,
`.log`, `.out`, `.toc`, or rendered page images.
