# Lambert W

The Lambert W function enters the Fabius–Rvachev corpus through the
two-scale endpoint asymptotics and the phase-locked Richardson layer of
the exponents-and-q-series group.  Its finite coefficient pipeline now runs
from the exact residual-moment algebra in
`LambertPhaseLockedRichardson.lean`, through the generic
complete-homogeneous/Bell dictionary in `CompleteHomogeneousBell.lean`, to
the shifted-reciprocal Bell specialization in
`LambertPhaseLockedBell.lean`.  The fixed-order analytic extractor remains
in `FabiusLambertPhaseExtraction.lean`, with its pullback,
complete-homogeneous, and reciprocal-row estimate modules, while the κ∞
decay gauge remains separate.  The endpoint programs of that volume's Parts
VI–VII and of the inverse-endpoint volume use the lower branch W₋₁ as their
canonical coordinate.  These articles treat the function itself, so they
form their own group.

Four independently written article packages arrived together on
2026-08-28 and were **merged editorially** (same day) into the single
consolidated volume:

Member: `Lambert_W_Guide/` — *The Lambert W Function: A Real-Variable
Guide*.  Its earlier 66-page, 1,107,064-byte A4 artifact remains a historical
receipt for its named source.  The most complete of the four treatments forms
the body; the unique layers of the
other three (the
complete power-tower convergence theorem, inverse-Taylor corrections,
the branch-exchange involution, the transcendence theorem, a
practitioner's toolkit, further applications, and the r-Lambert
outlook) are preserved in a complements section; a four-way concordance
appendix records that the shared core agreed theorem for theorem and
constant for constant, and a corpus-role section links W₋₁ to the
Fabius endpoint theory.  The four packages’ figures, data, and
verification scripts are preserved under `Lambert_W_Guide/assets/`;
the absorbed source documents themselves are deleted after merging,
with SHA-256 provenance in the document itself (git history is the
archive).

The synchronized publication receipt (2026-09-04) records a historical
checkpoint superseded by the current `b899` receipt below. The checkpoint
comprised the
4,876-line, 177,511-byte TeX source at SHA-256
`d852a345685dd61335a89fc4fd1092680bdc597a5d1e6ac612883946ad0d99ea`.
Exactly three successful serial halt-on-error passes from absent sidecars ran
68 pages / 963,230 bytes → 70 / 986,865 → 70 / 986,865. The final 70-page,
986,865-byte A4 PDF has SHA-256
`0b8801649a6dd43d9f02dcfc2f60cac50b5c8f88bd782645bf97d30cc3dfbd41`.
All 42 font rows are embedded and subset, five are Libertinus, and none is Type
3. Final-log reference/rerun/error checks, PDF metadata (with intentionally
empty author and keywords), every-page render and
nonblank-text checks, and representative visuals passed; generated sidecars
and forbidden checksum basenames both close at zero. The previous clipped-box
warning is gone; the sole harmless 0.82504 pt overfull box is readable, and the
final log has 133 underfull diagnostics.

The current synchronized `b899` source has 4,940 lines and 181,577 bytes, with
SHA-256
`2e6a4782fc4e4b945869f5fb45b39cf94e8dc34296866edf26b4cdfe19b1898b`.
Exactly three serial halt-on-error passes from absent sidecars ran 68 pages /
968,083 bytes → 70 / 991,847 → 70 / 991,848. The final 70-page,
991,848-byte PDF has SHA-256
`f802d78299f8f6aca7d31b935a4884f9343389a7307decb04c18b5159c8a4f04`.
All 70 pages are A4 at rotation zero, render successfully, and contain nonblank
text. All 42 font rows are embedded and subset, five are Libertinus, and none
is Type 3. Required log, reference/rerun, metadata (with intentionally blank
author and keywords), visual, cleanup, and forbidden-basename gates passed. The
only box diagnostic is one nonblocking 0.83 pt horizontal box.

Six polynomial-logarithmic transseries packages were also filed here on
2026-09-01, because Lambert W is their guiding example.  Their subject is the
transseries calculus rather than the function, so on 2026-09-02 they were
regrouped into
[`../series-and-transseries/polynomial-logarithmic-transseries/`](../series-and-transseries/Transseries_And_Inversion/),
which held their intake receipts.  Those six were consolidated, and on
2026-09-04 the whole `series-and-transseries` group became the single volume
linked above.  This group keeps only the articles about the Lambert W
function itself.

See [`../MANIFEST.md`](../MANIFEST.md) for the group record.

The corpus formalizes the real Lambert pair: the lower branch in
`LowerLambertW.lean` (definition, defining equation, uniqueness,
monotonicity, range, branch-point continuity, and continuity on the full
domain `[-1/e, 0)`) and the principal branch in `PrincipalLambertW.lean`
(defining equation on `[-1/e, ∞)` with the branch bound `W₀ ≥ -1`, uniqueness
among solutions `≥ -1`, the branch point `W₀(-1/e) = -1`, `W₀(0) = 0`,
`W₀(e) = 1`, strict monotonicity of the branch and of the forward map
`t·eᵗ`, branch-point continuity, continuity on the full domain
`[-1/e, ∞)`, the exact image `(-1, ∞)`, and the restricted image
`W₀([-1/e, 0]) = [-1, 0]`).  The endpoint/full-domain declarations are
`principalLambertW_continuousWithinAt_branchPoint`,
`principalLambertW_continuousOn_Ici`,
`lowerLambertW_continuousWithinAt_branchPoint`, and
`lowerLambertW_continuousOn_Ico`.  The inverse-function derivative
`W₀' = 1/(e^{W₀}(W₀+1))`, its strict positivity, and the exact endpoint value
`W₀'(0) = 1` (`deriv_principalLambertW_zero`) are kernel-verified.
The pair-level facts live in `LambertBranchDichotomy.lean`: the global
bound `-1/e ≤ t·e^t` derived from `1+x ≤ e^x` alone, the forward map
strictly decreasing on `(-∞, -1]` (the mirror of the principal-side
monotonicity), the closed value `W₋₁(-2e⁻²) = -2`, and the **branch
dichotomy**: every real solution of `w·e^w = z` is `W₀(z)` or `W₋₁(z)`
(`Fabius.eq_principalLambertW_or_eq_lowerLambertW`) — the guide's
two-branch inversion statement, kernel-verified.

The guide's exact branch-pair parametrization and symmetric corollary now have
a focused three-module crosswalk.  `LambertWBranchPairing.lean` has zero
definitions and seven theorems, including both displayed formulas for W₋₁;
`LambertWGapBijection.lean` has four definitions and sixteen theorems,
including the inverse bijection and all three `t > 1` coordinate formulas;
and `LambertWBranchSymmetry.lean` has zero definitions and nine theorems for
the quotient, exponential-rational and hyperbolic sum/product forms, and the
strict sum/product bounds.  The disjoint union is four definitions and 32
theorems, hence 36 public declarations.  The forward pairing and symmetric
laws use the sharp open input interval `(-exp(-1), 0)`.  In the converse
module the four coordinate definitions are total, `gapLower_eq_mul_exp` is
unconditional, the reconstruction results use a positive gap, and the three
logarithmic-coordinate results assume `t > 1`; its inverse and bijection
statements connect exactly the two open domains.  At the input interval's
left endpoint both branches equal `-1`, so the sum is exactly `-2` and the
product exactly `1`, while the lower branch has no finite value at zero.

The companion `LambertWBranchGapBernoulli.lean` has the exhaustive
surface zero definitions and five theorems:
`summable_norm_bernoulli_mul_pow_div_factorial`,
`summable_bernoulli_mul_pow_div_factorial_iff`,
`hasSum_bernoulli_mul_pow_div_factorial`,
`hasSum_bernoulli_mul_pow_div_factorial_complex_iff`, and
`principalLambertW_lowerLambertW_eq_bernoulliSeries`.  They prove absolute
summability of the real Bernoulli exponential generating series for
`|z| < 2*pi`; the exact complex criterion that the series is summable if and
only if `‖z‖ < 2*pi`, so it diverges on the boundary and throughout the
exterior; the complex `HasSum` value `(complexExpm1Div z)⁻¹` exactly on that
disk; its actual all-index real sum `z / (exp z - 1)` for `z != 0`; and the
paired compact branch-gap sums for a positive gap below `2*pi`.  At the origin
the complex target has the standard removable value `1`; away from the origin
it rewrites to the literal quotient.  No equality with Lean's totalized
quotient at zero is claimed.  This exactly crosswalks Guide label
`eq:pair-Bernoulli-general` and makes `eq:bernoulli-gen` wholly Exact under
that explicit removable-origin convention.  The Guide's nearest-nonzero-zero
argument is not the formal proof route.  With the three finite
branch-coordinate modules, the four-module union is four definitions and 37
theorems, 41 declarations.  The signed higher/convergent Puiseux program
remains open. The current 70-page `b899` Guide PDF recorded above renders the
source overlay and is synchronized; the preceding 70-page receipt remains
historical. The exact-radius
four-theorem checkpoint had census 903/11,447; the fifth theorem brought the
next local checkpoint to 903 modules and 11,449 public declarations, including
the retained unconditional public q-Pochhammer bridge.  The later sibling
`FabiusFunction.GeometricUniformMomentPolynomial` module has one definition
and eight theorems for its recursive polynomial, residual-product recurrence,
degree bound, value at zero, and first four nonconstant cases.  That algebraic
leaf produced the historical checkpoint 904 modules and 11,457 public
declarations.  Its companion
`FabiusFunction.GeometricUniformMomentPolynomialBridge` has the exhaustive
surface zero definitions and one theorem,
`Fabius.geometricUniformMomentPolynomial_eval₂_eq_mgf_taylorCoefficient`.
For every real `|q| < 1`, it supplies the actual-MGF normalization and makes
external source label `p7:eq:Pn-def` Exact in that real regime.  It constructs
no complex-q infinite product by itself.  At this bridge checkpoint the
leading-coefficient and strict odd-degree clauses were still absent, so the
compound `p7:thm:Pn` was then Partial; the later sharp-degree sibling below
makes it Exact.  This bridge produced the historical checkpoint 905 modules
and 11,458 public declarations.  The subsequent sibling
`FabiusFunction.GeometricUniformComplexMomentProduct` has the exhaustive
current surface one public definition and three public theorems:
`Fabius.geometricUniformComplexMomentProduct`,
`Fabius.hasProdLocallyUniformly_geometricUniformComplexMomentProduct`,
`Fabius.differentiable_geometricUniformComplexMomentProduct`, and
`Fabius.geometricUniformMomentPolynomial_eval₂_eq_complexMomentProduct_taylorCoefficient`.
For complex `‖q‖ < 1` it supplies the actual locally uniform product and its
complex differentiability on the whole plane, together with its normalized
Taylor-coefficient bridge.  This is an analytic analogue; it does
not extend the probability-moment reading of `p7:eq:Pn-def` beyond real
`|q| < 1`.  At this historical checkpoint the canonical q-monograph
`thm:qF-moment-polynomial` remained Partial because the global `RatFunc`
identification and its pole-clearing polynomial continuation at roots were
absent.  The original `1+2` surface produced the historical checkpoint 906
modules and 11,461 public declarations; the subsequently exposed
differentiability theorem belongs only to the live census below.
The zero-definition/one-theorem
`FabiusFunction.HalfQBinomialRootSimplicity` sibling exposes
`Fabius.halfQBinomial_sum_rootMultiplicity_two_pow`; composed with the
existing rational root classifier, it makes `cor:halfbase-root-locus` Exact
without an arbitrary-base or arbitrary-field claim.
The subsequent sibling
`FabiusFunction.GeometricUniformExteriorComplexMomentGerm` also has the
exhaustive surface one public definition and two public theorems:
`Fabius.geometricUniformExteriorComplexMomentGerm`,
`Fabius.analyticAt_geometricUniformExteriorComplexMomentGerm`, and
`Fabius.geometricUniformMomentPolynomial_eval₂_eq_exteriorComplexMomentGerm_taylorCoefficient`.
For complex `1 < ‖q‖` it supplies the actual reciprocal germ, analyticity at
the origin, and its normalized Taylor-coefficient bridge.  It makes no unit-
circle or global rational-function claim.  The exhaustive zero-definition/
three-theorem `FabiusFunction.GeometricUniformMomentPolynomialDegree` sibling
consists of `Fabius.coeff_geometricUniformMomentPolynomial_choose_two`,
`Fabius.coeff_geometricUniformMomentPolynomial_choose_two_sub_one`, and
`Fabius.geometricUniformMomentPolynomial_natDegree_eq`.  It proves the exact
top and subleading Bernoulli coefficients and the parity-sensitive degree,
making `p7:thm:Pn` and `prop:qF-P-degree-sharp` Exact.  At that checkpoint
`thm:qF-moment-polynomial` was still Partial at the global `RatFunc` boundary.

The final `FabiusFunction.GeometricUniformMomentRatFunc` sibling has one
public definition, `Fabius.geometricUniformMomentRatFunc`, and four public
theorems: `Fabius.qFactorial_mul_geometricUniformMomentRatFunc`,
`Fabius.eval_geometricUniformMomentRatFunc_eq_complexMomentProduct_taylorCoefficient`,
`Fabius.eval_geometricUniformMomentRatFunc_eq_exteriorComplexMomentGerm_taylorCoefficient`,
and `Fabius.eval_geometricUniformMomentRatFunc_one`.  It packages one
`RatFunc ℚ`, proves the global q-factorial clearing identity, identifies that
same rational function with both strict off-unit-circle Taylor-coefficient
regimes, and treats `q = 1` through `[n]₁! = n!`.  Together with the algebraic
polynomial leaf, this makes `thm:qF-moment-polynomial` Exact.  It does not
assign analytic values at genuine unit-root poles or prove their divisor or
orders.

The later `FabiusFunction.GeometricUniformMomentReciprocity` sibling has one
public definition, `Fabius.geometricUniformComplexMomentGerm`, and five public
theorems:
`Fabius.geometricUniformComplexMomentGerm_of_norm_lt_one`,
`Fabius.geometricUniformComplexMomentGerm_of_one_lt_norm`,
`Fabius.analyticAt_geometricUniformComplexMomentGerm`,
`Fabius.geometricUniformComplexMomentGerm_reciprocity`, and
`Fabius.geometricUniformComplexMomentGerm_moment_convolution`.  It joins and
identifies the strict inner and exterior branches, proves analyticity at zero
off the unit circle, and, for `q != 0` and `‖q‖ != 1`, proves the local
`EventuallyEq` `M_q(z) * M_(q⁻¹)(-z) = 1` and its exact all-order binomial
derivative convolution.  It makes `thm:qF-reciprocity` Exact.  A global
pointwise identity through genuine inner-product zeros is deliberately not
claimed.

The later germ-related addition
`FabiusFunction.RvachevLaurentLeading` has one definition and six theorems and
makes `is:p2:thm:Laurent-leading` exact through the manuscript-normalized
punctured-neighborhood limit and its coordinate, odd-core, nonvanishing,
cofactor, and general-pole companions.  Puncturing is essential because Lean
totalizes inversion at a pole; no lower Laurent coefficient is claimed.  The
eleven-definition/seventeen-theorem
`FabiusFunction.FinitePrefixAppellRecovery` sibling makes
`is:p2:thm:finite-prefix-expansion` and `is:p2:thm:exact-recovery` Exact for
every starting depth, including zero, at bases `1/2` and `1/4`.  Its exact
degrees are outer degrees in `Polynomial (Polynomial ℚ)` and may drop after a
fixed-inner-variable specialization; its finite-convolution moments are not a
random-variable or analytic-MGF realization.

In the origin-side chronology the sharp leaf gave the historical 921/11,575
checkpoint, `RvachevLaurentLeading` gave 922/11,582, and
`FinitePrefixAppellRecovery` gave 923/11,610.  The RatFunc leaf gives the
historical 924/11,615 checkpoint.  Two later theorems in
`ProbabilityLaplaceMoments` make `prop:up-tail` and `cor:up-moments` Exact,
and the unrelated exhaustive 1+1
`FabiusFunction.RvachevLegendreBiorthogonality` leaf gives the historical
925/11,619 checkpoint.  Its public declarations are
`Fabius.rvachevLegendreAnalysisKernel` and
`Fabius.rvachevLegendreBiorthogonality`; they close the normalized translated
kernel definition and finite Legendre biorthogonality, but not the larger
Fourier--Bessel or matrix-projector claims.  Subsequent source-only tranches,
including the reciprocity sibling, give the historical reciprocity checkpoint
931/11,685.  The subsequently merged upstream `DyadicBoundaryIdentity.lean`
and `FinitePrefixThueMorseCollapse.lean` modules add two modules and ten
public declarations, making the historical dyadic/finite-prefix census
933/11,695.  The incoming union adds one module and fourteen public
declarations: the new zero-definition/six-theorem
`ProuhetBaseTwoBridge.lean` module, one theorem added to
`DyadicBoundaryIdentity.lean`, and seven theorems added to
`ThueMorseNewmanSelfSimilarity.lean`.  This made 934/11,709 an explicitly
historical post-Prouhet checkpoint.  Subsequent source-only
transseries/Catalan and Thue--Morse additions made 943/11,791 the next
historical checkpoint.  The finalized one-definition/eleven-theorem
`TransseriesFlat.lean` module and three integer-zpow theorems in
`TransseriesDifferentialBlock.lean` gave the historical census 944/11,806; the merged live census is 979/12,142.
The q ledger is 181 Exact / 79 Partial / 14 None / 8 interface, the relevant Dyadic
Gaussian--Thue--Morse chapter is 13/43/0/0, and the source concordance is 103
Lean-proved / 375 human-proved frontier / 60 non-applicable / 9 conjectures.
All of these sibling source-only additions are likewise absent
from the retained historical PDFs.

The exact raw second-order package is `LambertWCurvature.lean`.  Its
principal API is `deriv_principalLambertW`,
`deriv_principalLambertW_hasDerivAt`,
`deriv_deriv_principalLambertW`,
`deriv_deriv_principalLambertW_zero`,
`deriv_deriv_principalLambertW_neg`, and
`strictConcaveOn_principalLambertW`; in particular, `W₀''(0) = -2` and
`W₀` is strictly concave on the full closed domain `[-1/e, ∞)`.  The lower
API is `deriv_lowerLambertW_hasDerivAt`,
`deriv_deriv_lowerLambertW`,
`deriv_deriv_lowerLambertW_pos_iff`,
`deriv_deriv_lowerLambertW_neg_iff`,
`deriv_deriv_lowerLambertW_eq_zero_iff`, and
`strictConvexOn_lowerLambertW_left`/
`strictConcaveOn_lowerLambertW_right`.  Thus `W₋₁''` changes sign exactly at
`-2e⁻²`, with strict convexity on `[-1/e,-2e⁻²]` and strict concavity on
`[-2e⁻²,0)`.

The one-sided branch-point geometry package is
`LambertWBranchPointGeometry.lean`.  Its exhaustive eight-theorem surface is
`tendsto_deriv_principalLambertW_branchPoint_atTop`,
`tendsto_deriv_lowerLambertW_branchPoint_atBot`,
`tendsto_principalLambertW_secantSlope_branchPoint_atTop`,
`tendsto_lowerLambertW_secantSlope_branchPoint_atBot`,
`principalLambertW_not_differentiableWithinAt_branchPoint`,
`lowerLambertW_not_differentiableWithinAt_branchPoint`,
`principalLambertW_not_differentiableAt_branchPoint`, and
`lowerLambertW_not_differentiableAt_branchPoint`.  As the input approaches
`-exp(-1)` from the right, the principal derivative and endpoint secant slope
tend to `+∞`, while their lower-branch counterparts tend to `-∞`.  Hence
neither branch has a finite right derivative there, and neither totalized
branch is differentiable at the branch point.

The leading square-root package is
`LambertWBranchPointAsymptotics.lean`.  Its exhaustive public surface is the
definition `lambertWBranchPointScale` and the eight theorems
`lambertWBranchPointScale_pos`, `lambertWBranchPointScale_sq`,
`tendsto_principalLambertW_add_one_sq_div_branchPoint`,
`tendsto_lowerLambertW_add_one_sq_div_branchPoint`,
`principalLambertW_add_one_sq_isEquivalent_branchPoint`,
`lowerLambertW_add_one_sq_isEquivalent_branchPoint`,
`principalLambertW_add_one_isEquivalent_branchPoint`, and
`lowerLambertW_add_one_isEquivalent_branchPoint`.  The positive scale is
`sqrt(2 exp(1) (z + exp(-1)))`; its square is exactly
`2 exp(1) (z + exp(-1))` to the right of the branch point.  For both branches,
`(W(z)+1)^2 / (z+exp(-1)) → 2 exp(1)`, equivalently the squared displacement is
asymptotic to that exact linear normalization.  The signed leading laws are
`W₀(z)+1 ~ lambertWBranchPointScale(z)` and
`W₋₁(z)+1 ~ -lambertWBranchPointScale(z)` from the right.

The scaled integer-power profile package lives in
`PowerExponentialLambert.lean`, `PowerExponentialLambertCalculus.lean`,
`PowerExponentialLambertInverse.lean`,
`PowerExponentialLambertAsymptotics.lean`, and
`PowerExponentialLambertFabius.lean`.  Its second-order companion is
`PowerExponentialLambertCurvature.lean`.  For nonzero natural power and
positive amplitude/rate it gives both real phases, endpoint-inclusive solve laws,
exact branch images, interior derivatives and signs, and two-sided `InvOn`
laws.  The normalized argument is continuous
(`powerExponentialLambertArgument_continuous`), the principal phase is
continuous on the full closed value interval
(`principalPowerExponentialPhase_continuousOn_Icc`), and the lower phase is
continuous on the positive endpoint-inclusive interval
(`lowerPowerExponentialPhase_continuousOn_Ioc`).  Among nonnegative
variables, `powerExponentialSaddle_eq_iff_eq_principal_or_eq_lower` is the
exact solution iff through the peak, and
`principalPowerExponentialPhase_ne_lowerPowerExponentialPhase` makes the two
roots distinct strictly below it.  This does not classify additional
negative roots possible for even powers.

On the common smooth interval `(0,peak)`, the curvature companion proves
`deriv_principalPowerExponentialPhase_hasDerivAt`,
`deriv_deriv_principalPowerExponentialPhase`,
`deriv_lowerPowerExponentialPhase_hasDerivAt`, and
`deriv_deriv_lowerPowerExponentialPhase`.  For either phase `lambda`, the
exact formula is
`lambda * (m - (m - beta*lambda)^2) /
(x^2 * (m - beta*lambda)^3)`.  This generic module is formula-only: the
sign/zero thresholds `beta*lambda₀ = m - sqrt(m)` and
`beta*lambda₋₁ = m + sqrt(m)`, together with the resulting generic strict
shape theorems, remain open Lean work.

At zero, `principalPowerExponentialPhase_isEquivalent_rpow` identifies the
principal root equivalent `(x/A)^(1/m)`, while
`tendsto_lowerPowerExponentialPhase_nhdsGT_zero_atTop` gives divergence of
the lower phase to `+∞`.  The lower result
`lowerPowerExponentialPhase_sub_intrinsicMain_tendsto_zero` is specifically
the intrinsic-epsilon two-term expansion for
`epsilon = (beta/m)(x/A)^(1/m)`.  It does not yet give a cleaned
`L = log(A/x)` normalization or a full generic asymptotic series.

The Fabius specialization `(m,A,beta) = (1,1,log 2)` now includes the
principal phase `fabiusPrincipalLambertPhase`, the exact nonnegative-root iff
`fabiusSaddle_eq_iff_eq_principal_or_eq_lower`, strict interior distinctness
`fabiusPrincipalLambertPhase_ne_fabiusLambertPhase`, full interval
continuity in `fabiusPrincipalLambertPhase_continuousOn_Icc` and
`fabiusLambertPhase_continuousOn_Ioc`, and the zero-endpoint equivalence
`fabiusPrincipalLambertPhase_isEquivalent_id`; the lower generic phase is
identified with `fabiusLambertPhase` by
`lowerPowerExponentialPhase_one_one_log_two`.

`PowerExponentialLambertFabiusCurvature.lean` closes the classical curvature
specialization.  It defines
`fabiusLambertInflectionInput = 2*exp(-2)/log 2`;
`fabiusLambertInflectionInput_mem_Ioo` proves that this lies strictly below
the peak, and `fabiusLambertPhase_inflectionInput` gives the lower phase
there as `2/log 2`.  The module also gives
`deriv_deriv_fabiusLambertPhase`,
`deriv_deriv_fabiusLambertPhase_pos_iff`,
`deriv_deriv_fabiusLambertPhase_neg_iff`,
`deriv_deriv_fabiusLambertPhase_eq_zero_iff`, and
`deriv_deriv_fabiusLambertPhase_inflectionInput`, and proves
`strictConvexOn_fabiusLambertPhase_left` on the positive interval through
the inflection and `strictConcaveOn_fabiusLambertPhase_right` from there
through the peak.  For the principal phase, the same module exports
`fabiusPrincipalLambertPhase_eq_principalLambertW`,
`fabiusPrincipalLambertPhase_continuousOn_Iic`,
`fabiusPrincipalLambertPhase_hasDerivAt`,
`deriv_fabiusPrincipalLambertPhase`,
`deriv_fabiusPrincipalLambertPhase_hasDerivAt`,
`deriv_deriv_fabiusPrincipalLambertPhase`,
`deriv_deriv_fabiusPrincipalLambertPhase_pos`,
`deriv_deriv_fabiusPrincipalLambertPhase_zero`, and
`strictConvexOn_fabiusPrincipalLambertPhase` on the whole closed half-line
ending at `exp(-1)/log 2`, including negative inputs and zero.

The branch-point results do not assign either branch a finite derivative at
the endpoint.  Still open in Lean are an `O(z + exp(-1))` remainder after the
signed leading square-root term, a convergent signed Puiseux expansion and its
higher coefficients, named generic/Fabius phase wrappers for the derivative,
secant, and square-root endpoint laws, and the generic square-root
threshold/shape package stated above.

For the Fabius endpoint observable itself,
`FabiusLambertPhaseLockedPullback.lean`,
`CompleteHomogeneousAsymptotics.lean`,
`LambertReciprocalAsymptotics.lean`, and
`FabiusLambertPhaseExtraction.lean` prove that every fixed reciprocal
Lagrange row extracts the periodic term with a complete finite Poincaré
remainder hierarchy.  Subtracting the first `S` residuals at row order `r`
leaves `O(lambda^(-(r+1+S)))`, and the estimator converges to the prescribed
periodic value along every integer phase ray.  The new finite rewrite tranche
is recorded by
`completeHomogeneousEvalOn_shiftedReciprocal_eq_bell`,
`sum_shiftedReciprocalLagrangeWeight_mul_invPow_card_add_eq_bell`, and
`sum_shiftedReciprocalLagrangeWeight_mul_invPow_eq_bell`: the generalized
harmonic power sums become factorially weighted Bell inputs, and the exact
fixed-order residual moments become factorially normalized complete Bell
polynomials.  The direct normalized specialization uses a field with
rational-algebra structure, and the weighted moment forms assume
characteristic zero; total inversion adds no positivity or nonzero-shift
premise.  This is a finite algebraic conversion only.  No convergence of
the formal infinite residual series, multiplicative relative-error hierarchy,
derivative extractor, uniformity in growing row order or residual depth, or
new sign control at those boundaries is claimed.
