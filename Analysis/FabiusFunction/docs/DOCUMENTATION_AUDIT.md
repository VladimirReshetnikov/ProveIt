# Documentation audit

`AGENTS.md` lists two documentation invariants for
`Analysis/FabiusFunction/Lean`:

- every source file carries a `/-! ... -/` module header; and
- every non-`private` declaration carries a `/-- ... -/` doc comment.

Neither held corpus-wide when this audit was first run.  This file records the
gap, and
[`scripts/doc_audit.py`](../scripts/doc_audit.py) makes it measurable, so that
a reviewer can check a change did not make it worse rather than re-deriving
the numbers by hand.  `AGENTS.md` asks for exactly this: a recorded, executable
scan rather than a number quoted from a vanished shell session.

## Running it

From the repository root:

```sh
python3 Analysis/FabiusFunction/scripts/doc_audit.py
python3 Analysis/FabiusFunction/scripts/doc_audit.py --list
```

The first form prints the totals and the twenty worst files.  The second adds
every undocumented declaration as `file:line  name`, which is the form to use
when clearing one file.

To use it as a gate:

```sh
python3 Analysis/FabiusFunction/scripts/doc_audit.py \
  --baseline Analysis/FabiusFunction/docs/doc_audit_baseline.json
```

This exits non-zero if the missing-doc total rises, if any individual file gets
worse, if a new file appears without a module header, or if the corpus inventory
changes without a reviewed baseline refresh.  The ratchet was originally
needed to make progress against a large inherited backlog.  As of 2026-08-29
that backlog is zero, so the checked baseline now enforces both invariants
without an exception.

Refresh the baseline with `--write-baseline` after genuinely reducing the
missing-doc count or after verifying a fully documented corpus addition.

## What the script does and does not check

It is a lexical scan, not Lean elaboration.  It tracks nested `/- -/` blocks,
`/-- -/` doc comments, `/-! -/` module comments, string literals and `--` line
comments, so a declaration keyword appearing inside a comment or a string is
never counted.  It accepts an attribute line (`@[simp]`, a multi-line
`@[...]`), an attribute on the same line as its declaration
(`@[simp] theorem foo`), a `set_option ... in` line, or blank lines between a
doc comment and the declaration it documents.  It also accepts the one-line
`/-- ... -/ theorem foo` form.

It does not see declarations produced by macros.  A `to_additive`-generated
name is invisible to it, exactly as it is to a reader of the source, so a
generated declaration is neither counted as present nor reported as
undocumented.

It says nothing about whether a doc comment is *correct*.  That is the more
expensive audit, and three defects it would have caught are recorded below.

## Findings

### Module headers

Twelve modules had no `/-! ... -/` header at all, verified by direct grep
(`/-!` occurring zero times in the file):

`PeriodicFourier`, `PeriodicMean`, `HalfQBinomial`, `ThueMorseGenerating`,
`ThueMorsePrefix`, `FabiusSaddleCentral`, `SaddleAllOrders`,
`FabiusSaddleExponentAllOrders`, `FabiusSaddleTailAllOrders`,
`FabiusSaddleReferenceTail`, `NegativeLaplaceVerticalOrdinaryJets`,
`GammaSecondOrder`.

Four more had a bare title with at most one line of prose, and one of those
described finished, downstream-consumed results as scratch development:

`FabiusLambertDerivativeBounds`, `FabiusSaddleCentralLambert`,
`NegativeLaplaceVerticalTaylor`, `NegativeLaplaceVerticalFourthBound`.

`SaddleLogExpansionAlgebra` called itself a scratch module in an otherwise
accurate header.

All of these have been written or rewritten.  Every header was drafted against
the whole file and then checked by a second reader against the same file,
because a header that is trusted and wrong is worse than one that is absent.

`PeriodicFourier` is the case that mattered most: 72 public declarations, the
entire Mellin and Fourier analysis of the regularized Bose kernel, and no
statement anywhere in the file of what it was for.

### Doc comments

The backlog began at 862 undocumented public declarations, 31% of the corpus.
Two documentation waves and a pass over the two root modules first brought it
to 176, or 6.2%, and the original 191-module corpus was subsequently cleared
according to the then-current checker.

That apparent zero exposed a checker defect: declarations written as
`@[simp] theorem foo` on one line were not counted at all.  After teaching the
auditor to remove balanced leading attribute blocks, and after the corpus grew
to 311 modules, the corrected 2026-08-27 inventory initially contained 4,803
public declarations with 105 missing comments in 40 files.  The old parser saw
only 4,606 declarations and
36 gaps on those same bytes; the correction therefore recovered 197 attributed
declarations, including 69 undocumented ones.  Run the script for the live
numbers rather than copying these historical values.

The historical post-merge 2026-09-01 inventory contained 675 modules and 8,909
lexically visible public declarations, with zero missing module headers and
zero missing doc comments.  A fresh 2026-09-04 audit for this documentation
pass scans 952 facade-reachable modules and 11,884 explicit public declarations.  It
finds no missing module header or declaration comment, including throughout
`FabiusInverseExactDyadicModulus.lean`, `JacobiTwoSquareCount.lean`, and
`LagrangeRvachevMatrix.lean`, as well as the incoming
`GeometricRichardsonGenerating.lean`, `TwoPhiOneReversal.lean`, and
`QChuVandermonde.lean` APIs and the strengthened
`GaussianBinomialCumulants.lean` surface, and the new
`GeometricUniformRealization.lean`, `RegularCentralQBinomialSum.lean`,
`LambertWBranchGapBernoulli.lean`, `GaussianBinomialFixedColumnRate.lean`, and
`RvachevAppellHasse.lean`, `GeometricUniformMomentPolynomial.lean`,
`RvachevLagrangeNodesOnly.lean`, `GaussianBinomialGreaterOneAsymptotics.lean`,
`ThueMorseGammaTowerDifferential.lean`,
`GeometricUniformMomentPolynomialBridge.lean`,
`GeometricUniformComplexMomentProduct.lean`, `ThueMorseCornerIntegral.lean`,
`RvachevLegendreCentralSum.lean`, `HalfQBinomialRootSimplicity.lean`,
`GeometricUniformExteriorComplexMomentGerm.lean`,
`GeometricUniformMomentPolynomialDegree.lean`,
`RvachevLaurentLeading.lean`, `FinitePrefixAppellRecovery.lean`,
`GeometricUniformMomentRatFunc.lean`, `RvachevLegendreBiorthogonality.lean`,
`GeometricUniformMomentReciprocity.lean`,
`QPochhammerLambertForm.lean`, `CentralQVandermondeInfinite.lean`,
`ThueMorseNewmanSelfSimilarity.lean`, `TriangularPowerProduct.lean`,
`DyadicBoundaryIdentity.lean`, `MeanValueBracket.lean`, and
`FinitePrefixThueMorseCollapse.lean`, `ProuhetBaseTwoBridge.lean`,
`UnitSeriesBellCoefficients.lean`, `TransseriesWellBased.lean`,
`TransseriesHeight.lean`, `TransseriesScale.lean`,
`TransseriesScaleDominance.lean`, `TransseriesPolyLogScale.lean`,
`TransseriesBlockAntiderivative.lean`, `TransseriesDifferentialBlock.lean`, and
`QuadraticCoreCatalan.lean` leaves, and the later
`DerangementNearestInteger.lean`, `LinLogCoreInversion.lean`,
`OrdinaryPartialBell.lean`, `PowerLogCoreInversion.lean`,
`RemainderTransport.lean`, `StaircaseInversion.lean`,
`TransseriesFlat.lean`, `TransseriesHarmonicIncrement.lean`, and
`WrightOmega.lean` tranche together with the integer-exponent extension of
`TransseriesDifferentialBlock.lean`,
together with the strengthened
`ProbabilityLaplaceMoments.lean` surface,
as well as the sixteenth theorem in `FinitePolynomialFunctional.lean`.
Relative to the
610/8,318 activation checkpoint, the current tree adds 342 modules and 3,566 declarations.
Relative to the earlier 630/8,552 merged checkpoint, concurrent source work
adds 322 modules and 3,332 declarations.  The post-merge 675/8,909 inventory,
the intervening 903/11,448 Lambert-series inventory, and the immediately
preceding 914/11,555 scaled-geometric and 915/11,556 real-MGF-bridge
checkpoints, together with the incoming branch's 906/11,461 complex-product
checkpoint, remain historical, not descriptions of the live facade.  In the
merged chronology, the historical complex-product checkpoint 918/11,568 was
followed by the half-base root-simplicity leaf at the merged-main pre-local
checkpoint 919/11,569, the exterior reciprocal-germ leaf at 920/11,572, and
the sharp coefficient-and-degree leaf at the historical 921/11,575
checkpoint.  The one-definition/six-theorem Laurent-leading leaf then gave
922/11,582, the eleven-definition/seventeen-theorem finite-prefix leaf gave
the historical pre-RatFunc checkpoint 923/11,610, and the one-definition/
four-theorem global RatFunc leaf gave the historical 924/11,615 checkpoint.
Two theorems added to `ProbabilityLaplaceMoments.lean` then gave 924/11,617,
and the one-definition/one-theorem Legendre--Rvachev biorthogonality leaf gave
the historical 925/11,619 checkpoint.  Later merged source work contributes
the zero-definition leaves `QPochhammerLambertForm` 0+5,
`CentralQVandermondeInfinite` 0+4, `TriangularPowerProduct` 0+2,
and `MeanValueBracket` 0+6; the 1+12 `ThueMorseNewmanSelfSimilarity` leaf; and
a net twenty-nine further declarations in existing modules.  These changes
reached the immediate pre-reciprocity checkpoint 930/11,678.  Promoting the
complex-product differentiability theorem and adding the exhaustive 1+5
reciprocity leaf add one module and seven declarations, giving the historical
reciprocity checkpoint 931/11,685.  The subsequently merged zero-definition
leaves `DyadicBoundaryIdentity` 0+2 and `FinitePrefixThueMorseCollapse` 0+8 add
two modules and ten declarations, giving the historical 933/11,695 checkpoint.
Finally, `ProuhetBaseTwoBridge` 0+6, one new theorem in
`DyadicBoundaryIdentity`, and seven new theorems in
`ThueMorseNewmanSelfSimilarity` add one module and fourteen declarations in
total, giving the historical 934/11,709 census.  The nine series/transseries
modules then add 72 lexically explicit public declarations; `to_additive`
also generates two Neumann twins that the lexical audit intentionally does not
count.  Together with six concurrent declarations elsewhere, this gave the
historical 943/11,787 census.  The later nine-module transseries tranche adds
90 declarations, and four integer-exponent theorems extend
`TransseriesDifferentialBlock.lean`; this gave the historical incoming
952/11,881 checkpoint.  The two explicit OrderDual Neumann wrappers and the
Wright-omega analyticity theorem subsequently bring the live census to
952/11,884.
On the earlier
exterior-germ branch, the inner-complex 906/11,461 checkpoint was followed by
the branch-local 907/11,464 checkpoint; its preceding real-MGF and algebraic
moment-polynomial checkpoints were 905/11,458 and 904/11,457.  These older
branch-local counts are explicitly historical.

#### Terminating `₂φ₁` reversal and q-Chu--Vandermonde tranche

That public API growth left the module count unchanged and added twelve
declarations to the immediately preceding 901/11,418 live inventory.
`TwoPhiOneReversal.lean` grows from 1+6 to 2+12 (one definition and six
theorems added), and `QChuVandermonde.lean` grows from 0+5 to 0+10 (five
theorems added).  The resulting q-Chu checkpoint was therefore exactly 901
modules and 11,430 public declarations; the generating-function tranche below
is the subsequent live increment.

The exhaustive `TwoPhiOneReversal.lean` inventory is two definitions,
`twoPhiOneFinite` and `twoPhiOneReflection`, and twelve theorems:
`choose_two_add_succ_choose_two`, `finiteQPochhammerIn_sub_eq`,
`finiteQPochhammerIn_reversal_ne_zero`,
`finiteQPochhammerIn_inv_pow_self`, `twoPhiOneReflection_involutive`,
`twoPhiOneFinite_reversal`, `twoPhiOneFinite_reversal_twice`,
`twoPhiOneFinite_eq_sum_twoPhiOneTerm`,
`twoPhiOne_eq_twoPhiOneFinite_inv_pow`, `twoPhiOne_reversal`,
`twoPhiOne_reversal_twice`, and `twoPhiOne_one_eq_twoPhiOneFinite_zero`.
The monograph label `lem:2phi1-reversal` is **Exact**: the theorem is exposed
for the actual `twoPhiOne` tsum, the terminating bridge has no analytic
convergence premise, reflection is involutive, and double reversal cancels
both prefactors.  The reversal retains exactly `q,a,c,z ≠ 0` and nonvanishing
of `(q;q)_n`, `(c;q)_n`, and `(q^{1-n}/a;q)_n`; its separate `n=0` bridge
also covers `q=0`.

The exhaustive `QChuVandermonde.lean` inventory has no definitions and ten
theorems: `two_mul_choose_two`, `mul_sub_one_eq_mul_sub_add`,
`finiteQPochhammerIn_div_eq_sum_chu`, `q_chu_vandermonde_first`,
`finiteQPochhammerIn_div_eq_sum_chu_second`,
`twoPhiOneFinite_mul_finiteQPochhammerIn_eq_chu_second`,
`q_chu_vandermonde_second`, `q_chu_vandermonde_second_by_reversal`,
`twoPhiOne_q_chu_vandermonde_first`, and
`twoPhiOne_q_chu_vandermonde_second`.  The label `cor:q-chu` is **Exact**:
both formulas have actual-`twoPhiOne` wrappers throughout their displayed
rational domain `q ≠ 0`, `A ≠ 0`, `(q;q)_n ≠ 0`, `(C;q)_n ≠ 0`; in
particular the second formula assumes neither `C ≠ 0` nor `(A;q)_n ≠ 0`.
The label `prop:qchu2-by-reversal` is **Partial**.  Its provenance theorem
uses `twoPhiOneFinite_reversal` only on the additional locus `C ≠ 0` and
`(A;q)_n ≠ 0`; the stronger full-domain finite theorem and actual-tsum
wrapper instead follow from a direct denominator-cleared q-Cauchy argument.
The monograph's rational-continuation step and cleared commutative-ring
extension remain unformalized.

#### Geometric Richardson generating-function tranche

`GeometricRichardsonGenerating.lean` added one source module and exactly ten
public declarations to the 901/11,430 q-Chu checkpoint.  The resulting
historical checkpoint was 902 modules and 11,440 public declarations.  Its
three definitions are `geometricRichardsonKernel`,
`qPochhammerNormalizedDataSeries`, and
`geometricRichardsonTransform`.  Its seven theorems are
`coeff_rescale_qPochhammerSeries_eq_geometricRichardsonKernel`,
`coeff_qPochhammerNormalizedDataSeries`,
`geometricRichardsonTransform_generating`,
`geometricRichardsonTransform_eq_sum_lagrange`,
`geometricLagrangeRichardson_generating`,
`hasSum_geometricRichardsonTransform_mul_pow`, and
`hasSum_geometricLagrangeRichardson_mul_pow`.  Two private proof helpers are
excluded from the public count.

The comb-interpolation label `gq:thm:richardson-generating` is **Exact** via
`geometricLagrangeRichardson_generating`.  The stronger formal layer works
over every commutative ring, with no topology or `QRegular` hypothesis, and
uses `Ring.inverse` to make coefficients total even when a finite
q-Pochhammer factor is not a unit.  Over a field, `q ≠ 0` identifies this
convolution with the canonical totalized Lagrange row.  Roots of unity need
not be excluded for the algebraic equality, but colliding nodes are not
thereby a valid interpolation scheme; at `q = 0`, nodes repeat for `n ≥ 2`
and the closed Lagrange formula fails, so the report-facing bridge correctly
excludes that base.  The analytic pair assumes a complete normed field,
`‖q‖ < 1`, and norm-summability of the normalized data series at the chosen
`z`; the Lagrange form additionally assumes `q ≠ 0` and proves a `HasSum`
identity.  It does not claim a general analytic evaluation operation for
arbitrary formal power series.

#### Gaussian-binomial second-moment tranche

The later strengthening of the existing `GaussianBinomialCumulants.lean`
module left its then-live module count at 905 and added three public theorems,
bringing that historical checkpoint to 11,474 public declarations.  The
module's exhaustive public
inventory is two definitions, `meanAtOne` and `varAtOne`, and twenty-four
theorems: `meanAtOne_one`, `varAtOne_one`, `meanAtOne_mul`, `varAtOne_mul`,
`meanAtOne_prod`, `varAtOne_prod`, `eval_one_derivative_X_pow`,
`eval_one_derivative_derivative_X_pow`, `eval_one_qInt_X`,
`eval_one_derivative_qInt_X`, `eval_one_derivative_derivative_qInt_X`,
`meanAtOne_qInt_X`, `varAtOne_qInt_X`, `one_sub_X_pow_succ_eq`,
`gaussianBinomial_X_mul_prod_qInt`, `eval_one_gaussianBinomial_X`,
`sum_mean_diff`, `sum_var_diff`, `meanAtOne_gaussianBinomial_X`,
`varAtOne_gaussianBinomial_X`, `eval_one_derivative_gaussianBinomial_X`,
`eval_one_derivative_derivative_gaussianBinomial_X`,
`twelve_mul_secondMoment_gaussianBinomial_eval_one`, and
`twelve_mul_varianceNumerator_gaussianBinomial_eval_one`.

The last three are the new declarations.  The first gives the explicit second
derivative at one over a characteristic-zero field when `k ≤ n`.  The other
two clear all denominators: over every commutative semiring and for all natural
`n,k`, including the above-row zero case, they give the raw second coefficient
moment and the variance numerator.  The probability terminology is the
interpretation of the normalized coefficient generating polynomial; the
generic theorems themselves are algebraic identities and do not construct a
separate probability-space random variable.  Three private transport helpers
are excluded from the public census.

#### Exact Lambert branch-pairing tranche

The three-module Lambert branch-pairing union is exhaustively counted as
`LambertWBranchPairing.lean` 0+7, `LambertWGapBijection.lean` 4+16, and
`LambertWBranchSymmetry.lean` 0+9: four definitions and 32 theorems, hence 36
public declarations.  The seven pairing theorems are
`principalLambertW_sub_lowerLambertW_pos`,
`lowerLambertW_eq_principalLambertW_mul_exp_gap`,
`principalLambertW_eq_neg_gap_div`,
`lowerLambertW_eq_neg_gap_mul_exp_div`,
`lowerLambertW_eq_neg_gap_div_one_sub_exp_neg`,
`eq_neg_gap_div_mul_exp`, and
`principalLambertW_lowerLambertW_eq_of_exp_gap`.

The converse module defines `gapPrincipal`, `gapLower`, `gapArg`, and
`branchGap`.  Its sixteen theorems are `gap_denominator_pos`,
`gapPrincipal_mem_Ioo`, `gapLower_eq_mul_exp`, `gapLower_eq_sub`,
`gapLower_lt_neg_one`, `gapLower_mul_exp`, `gapArg_mem_Ioo`,
`principalLambertW_gapArg`, `lowerLambertW_gapArg`, `branchGap_gapArg`,
`gapArg_branchGap`, `branchGap_invOn`, `branchGap_bijOn`,
`principalLambertW_gapArg_log`, `lowerLambertW_gapArg_log`, and `gapArg_log`.
Together with the forward formulas they prove that the positive gap and the
explicit reconstructed argument are two-sided inverses between the strict
domains `(-exp(-1),0)` and `(0,∞)`.  The final three declarations give all
three `t=exp Δ`, `t>1` forms: the principal branch, lower branch, and common
argument.

The nine symmetric theorems are
`lowerLambertW_div_principalLambertW_eq_exp_branchGap`,
`principalLambertW_add_lowerLambertW_eq_exp_branchGap`,
`principalLambertW_add_lowerLambertW_eq_cosh_div_sinh_branchGap`,
`principalLambertW_mul_lowerLambertW_eq_exp_branchGap`,
`principalLambertW_mul_lowerLambertW_eq_sinh_sq_branchGap`,
`principalLambertW_add_lowerLambertW_lt_neg_two`,
`principalLambertW_mul_lowerLambertW_pos`,
`principalLambertW_mul_lowerLambertW_lt_one`, and
`principalLambertW_mul_lowerLambertW_mem_Ioo`.  They record the exact branch
ratio, both exponential and hyperbolic sum/product forms, and the strict
interior inequalities `W₀+W₋₁<-2` and `0<W₀W₋₁<1`.  Their hypotheses exclude
both the branch point and zero endpoint.  These three finite modules do not
themselves prove a Bernoulli-number series or any branch-point or small-input
asymptotic; the separate analytic series leaf is inventoried next.

#### Exact Lambert branch-gap Bernoulli tranche

`LambertWBranchGapBernoulli.lean` first added one source module and four public
theorems to the historical 902/11,443 checkpoint, giving the historical exact-radius
checkpoint 903/11,447.  Its fifth public theorem leaves the module count fixed
and gives the historical 903/11,448 Lambert checkpoint.  Its exhaustive public
surface is
`summable_norm_bernoulli_mul_pow_div_factorial`,
`summable_bernoulli_mul_pow_div_factorial_iff`,
`hasSum_bernoulli_mul_pow_div_factorial`,
`hasSum_bernoulli_mul_pow_div_factorial_complex_iff`, and
`principalLambertW_lowerLambertW_eq_bernoulliSeries`; five private majorant,
coefficient-transport, norm-transport, zeta-lower-bound, and even-term helpers
are excluded from the public count.  Together with the three finite
branch-coordinate modules, this makes the four-module Lambert union four
definitions and 37 theorems, 41 declarations.

The first theorem proves absolute convergence of the real Bernoulli
exponential generating series for `|z| < 2π`.  The second proves for every
complex `z` that the series is summable exactly when `‖z‖ < 2π`; consequently
every boundary and exterior point diverges, and its proof exhibits an
even-indexed subsequence whose term norms stay at least `2`.  The third gives the real
series its actual `HasSum` value `z/(exp z-1)` under the additional condition
`z ≠ 0`.  The fourth theorem gives the strongest complete complex statement:
the series has sum `(complexExpm1Div z)⁻¹` exactly when `‖z‖ < 2π`, including
value `1` at the removable origin.  The final theorem specializes the real
evaluation to
`x ∈ (-exp(-1),0)` and
`branchGap x < 2π`, returning both branch identities as one conjunction.  It
makes Lambert Guide label `eq:pair-Bernoulli-general` **Exact**.  Label
`eq:bernoulli-gen` is also **Exact** only when its displayed quotient is read as
the canonical removable-origin representation `(complexExpm1Div z)⁻¹`; this
does not assert equality to Lean's literal totalized quotient at `z=0` or a
holomorphy theorem.  The real quotient theorem deliberately excludes `z=0`,
while the branch theorem excludes both endpoints.  No remainder estimate or
higher/convergent Puiseux expansion is included.

#### Arbitrary-space geometric-uniform realization tranche

`GeometricUniformRealization.lean` adds one source module, one definition, and
seventeen theorems.  The definition is `geometricUniformRealization`.  The
theorems are `geometricUniformRealization_eq_tsum`,
`geometricUniformRealization_split`, `uniformProcess_hasLaw_uniformProduct`,
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
`measureReal_geometricUniformRealization_le_eq_one_of_one_le`.

The definition, literal tsum identity, and absolute-convergence theorem are
pointwise on any type.  The probabilistic transport applies on any supplied
measurable space and measure carrying `Icc 0 1`-valued coordinates whose
marginals have the interval-volume law and which satisfy `iIndepFun`; it does
not construct those coordinates on every probability space.  Under `|q|<1`
the realization has the canonical law, mean `1/2`, reflection symmetry, and
canonical CDF.  The range, support, and exterior-CDF statements use
`0≤q<1`; the conditioning integral uses `0<q<1`.  The affine fixed-point
wrappers additionally assume `IsProbabilityMeasure P` and the displayed
independence of the fresh uniform coordinate and canonical-law copy.  Thus the
q-monograph's `thm:geometric-uniform-basic` is Exact on its stated `0<q<1`
domain, without silently asserting universal existence of a realization.

#### Regular central q-binomial-sum tranche

`RegularCentralQBinomialSum.lean` adds one source module and exactly three
public declarations: definitions `qNumberC` and
`regularCentralQBinomialTerm`, and theorem
`hasSum_regularCentralQBinomial`.  For real `0<q<1` and complex `alpha`, it
proves the actual series `HasSum` with value
`qGammaC (q^2) (3/2) * qGammaC (q^2) ((alpha+1)/2) /
qGammaC (q^2) ((alpha+2)/2)`.  Its sole parameter condition is
`qPochhammerInfIn (q^(alpha+1)) (q^2) ≠ 0`, exactly the simultaneous
nonvanishing condition for the generalized q-numbers in the summand.  Even
negative integral `alpha` are not excluded; at those parameters the totalized
q-Gamma quotient, like the product evaluation used in the proof, is zero.
This closes `thm:regular-central-sum`; it does not formalize the separate
classical-limit corollary.

#### Effective fixed-column Gaussian-rate tranche

`GaussianBinomialFixedColumnRate.lean` adds one source module, no definitions,
and exactly ten theorems:
`norm_finiteQPochhammerIn_pow_sub_one_le_exp`,
`norm_finiteQPochhammerIn_pow_sub_one_le`,
`norm_finiteQPochhammerIn_self_mul_gaussianBinomial_sub_one_le`,
`norm_gaussianBinomial_sub_inv_finiteQPochhammerIn_le`,
`norm_gaussianBinomial_add_sub_inv_finiteQPochhammerIn_le`,
`tendsto_gaussianBinomial_add_atTop`,
`gaussianBinomial_fixedColumn_relativeError_isBigO`,
`gaussianBinomial_shifted_fixedColumn_relativeError_isBigO`,
`gaussianBinomial_fixedColumn_error_isBigO`, and
`gaussianBinomial_shifted_fixedColumn_error_isBigO`.

The first two estimates hold in every normed commutative ring with normalized
multiplicative norm when `‖q‖ ≤ 1`: they bound
`‖(q^m;q)_k-1‖` by `exp(k‖q‖^m)-1` and then by
`(k exp k)‖q‖^m`.  Under `k≤n`, the third gives the denominator-free relative
bound `‖(q;q)_k[n,k]_q-1‖ ≤ (k exp k)‖q‖^(n-k+1)`, which remains meaningful at
roots of unity.  Over any normed field, `‖q‖<1` suffices for the fixed and
shifted nonasymptotic additive bounds, the shifted `Tendsto`, and all four
relative/additive `IsBigO` results at the rates `q^(n-k+1)` and `q^(n+1)`.
There is no completeness or `q≠0` hypothesis, and the displayed constant is
elementary rather than sharp.  Together with the pre-existing
`tendsto_gaussianBinomial_atTop`, the shifted limit and two relative-error
theorems discharge every clause of `thm:fixed-column-limit`; the two additive
theorems are stronger companion estimates.

Together with the prior 905/11,474 branch inventory and the three-declaration
Lambert leaf, the geometric-uniform and regular-central leaves, and this final
ten-theorem leaf, the fixed-column checkpoint was 909 modules and 11,508
public declarations.

#### Greater-than-one Gaussian asymptotics

`GaussianBinomialGreaterOneAsymptotics.lean` adds no definitions and exactly
two theorems:
`gaussianBinomial_gt_one_fixedColumn_relativeError_isBigO` and
`gaussianBinomial_gt_one_central_isEquivalent`.  For real `q` under exactly
`1 < q`, the first gives the fixed-column normalization
`(q⁻¹;q⁻¹)_k * (q^(k*(n-k)))⁻¹ * [n,k]_q - 1 =
O((q⁻¹)^(n-k+1))`; natural subtraction is total, and reciprocity is invoked
only eventually once `k ≤ n`.  The second gives the central equivalence
`[2m,m]_q ~ q^(m*m) * (q⁻¹;q⁻¹)_∞⁻¹`.  Together with the existing
`gaussianBinomial_inv`, this makes `cor:qgreaterone` **Exact**.  No
shifted-central statement or wider nome domain is claimed.

#### Rvachev--Appell Hasse and geometric-decoder tranche

`RvachevAppellHasse.lean` adds one source module, one definition,
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
`Fabius.geometric_lagrangeRvachevDecoder_eq`.

The commutative-semiring foundation is the coefficientwise linear transform
which sends each monomial to the corresponding arbitrary Appell polynomial;
the two cutoff theorems identify it with a finite Hasse-derivative sum.  The
reciprocal centered-Rvachev coefficients vanish in odd degrees, so real
Rvachev deconvolution is the finite even-Hasse sum.  Taylor's coefficient
formula and Vieta's identity turn Hasse derivatives of a root product into
complementary elementary symmetric functions, yielding the displayed
q-falling-power formula with no condition on `c` or `q`.  The field-level
Lagrange factorization, general sampled-decoder formula, geometric nodal
weight, and final real specialization then give the full Gaussian
q-Pochhammer prefactor times the same finite even-moment sum.

Those algebraic identities are total at zero and colliding nodes because the
Lagrange basis uses totalized inversion; at collisions they are not cardinal
interpolation statements.  The manuscript application retains `c>0`,
`0<q<1`, the dyadic nonzero mesh, degree, and interval hypotheses required by
the separate synthesis theorems.  In composition with
`normalized_sum_Ioo_rvachevDeconvolvedPolynomial_mul_shifted_rvachevUp` and
the generic Lagrange--Rvachev synthesis theorem, the new formulas make both
`gq:prop:q-Appell-falling` and `gq:thm:gaussian-Appell-decoder` Exact.  The
coefficients `rvachevReciprocalMomentRat` are a formal reciprocal-moment
sequence; no convergence of an analytic reciprocal MGF is asserted.  Atom
reconstruction remains owned by the separate synthesis API, and there is no
new larger matrix right-inverse or decoder-optimality theorem.

The resulting Appell/fixed-column checkpoint was 910 modules and 11,525
public declarations, with no missing module header or declaration comment.

#### Nodes-only Lagrange--Rvachev amplitude tranche

`RvachevLagrangeNodesOnly.lean` adds one definition,
`rvachevDeconvolvedPolynomialRat`, and exactly fourteen theorems:
`map_rvachevDeconvolvedPolynomialRat`,
`rvachevDeconvolvedPolynomial_eq_sum_appell`,
`eval_rvachevDeconvolvedPolynomial_eq_sum_even_iterateDerivative`,
`rvachevDeconvolvedPolynomial_prod_X_sub_C_eq_sum_appell`,
`eval_rvachevDeconvolvedPolynomial_lagrangeBasis_eq_sum_even_iterateDerivative`,
`eval_rvachevDeconvolvedPolynomial_lagrangeBasis_eq_nodalWeight_mul_sum_appell`,
`lagrangeRvachevDecoder_eq_nodalWeight_mul_sum_appell`,
`map_lagrangeBasis_ratCast`,
`map_rvachevDeconvolvedPolynomialRat_lagrangeBasis`,
`lagrangeRvachevDecoder_eq_ratCast`,
`rvachevRawMomentRat_eq_centeredRvachevFullMoment`,
`momentCumulant_rvachevRawMomentRat_eq_centeredRvachevFullCumulant`,
`momentCumulant_rvachevRawMomentRat_even_eq_bernoulliMersenne`, and
`rvachevReciprocalMomentRat_eq_completeBellPolynomial_neg_centeredCumulant`.

By composition these declarations give `cor:lag-nodes-only` an
**Exact/Complete** Lean counterpart; no single wrapper theorem is claimed.
The ordinary-derivative Lagrange form assumes `Set.InjOn v s`, matching
distinct nodes, while the raw omitted-node elementary-symmetric/Appell form
uses `Lagrange.nodalWeight`.  Rational nodes produce a polynomial over `ℚ`
whose coefficientwise real cast is the real decoder polynomial.  Rational
values are consequently asserted only at rational evaluation points, notably
the lattice points `k/M`, not at arbitrary irrational real points.  The
lattice identity is total when `M=0`; actual reconstruction retains its
separate nonzero and admissible-mesh hypotheses.  The complete-Bell identity
is formal coefficient-sequence algebra, not analytic reciprocal-MGF
convergence, and odd-cumulant vanishing uses the pre-existing centered-parity
theorem.  Independently, the exact decoder and atom-coefficient synthesis
declarations in `LagrangeRvachevSynthesis` make `thm:lag-cardinal`
**Exact/Complete by assembly**.  The larger compound
`thm:lag-right-inverse`, global atom synthesis, and decoder optimality remain
unpromoted.

#### Algebraic geometric-uniform moment-polynomial tranche

`GeometricUniformMomentPolynomial.lean` adds one source module and nine public
declarations.  Concurrently, the one-definition/fourteen-theorem
`RvachevLagrangeNodesOnly.lean` and zero-definition/two-theorem
`GaussianBinomialGreaterOneAsymptotics.lean` leaves moved the 910/11,525
checkpoint to 912/11,542; the moment-polynomial leaf brought that checkpoint
to 913/11,551.  Its exhaustive 1+8 surface is the definition
`geometricUniformMomentPolynomial` and the theorems
`geometricUniformMomentPolynomial_zero`,
`geometricUniformMomentPolynomial_succ`,
`geometricUniformMomentPolynomial_natDegree_le`,
`geometricUniformMomentPolynomial_eval_zero`,
`geometricUniformMomentPolynomial_one`,
`geometricUniformMomentPolynomial_two`,
`geometricUniformMomentPolynomial_three`, and
`geometricUniformMomentPolynomial_four`.  Two documented residual-product
helpers are private and therefore excluded from the public count.

The recursive family is total over `ℚ[X]`.  Its zero and successor theorems
give `P_0=1` and the residual finite q-Pochhammer recurrence; the degree theorem
gives `natDegree P_n ≤ n.choose 2`; evaluation at zero gives
`P_n(0)=1/(n+1)!`; and the four final theorems give the displayed values
`P_1` through `P_4`.  These exactly close the algebraic clauses of monograph
label `thm:qF-moment-polynomial`, including the `q=0` boundary.  At this
checkpoint the canonical label moved from None to **Partial**, because its
analytic coefficient normalization had not yet been identified with the
recursive Lean family.

#### Real-MGF normalization bridge

`GeometricUniformMomentPolynomialBridge.lean` adds one source module and one
public theorem to the immediately preceding 914/11,555 scaled-geometric
checkpoint, bringing that checkpoint to 915/11,556.  Its exhaustive 0+1 surface is
`geometricUniformMomentPolynomial_eval₂_eq_mgf_taylorCoefficient`; every helper
declaration in the module is private and excluded from the public count.

For every real `q` with `|q| < 1` and every natural index, the theorem identifies
evaluation of the recursive rational polynomial by the exact formula
`P_n(q)=((q;q)_n/(1-q)^n)·(iteratedDeriv n M_q 0/n!)`, where `M_q` is the genuine
geometric-uniform MGF.  The sharp domain includes `q=0` and negative
contractions.  This supplies the
analytic normalization in frontier label `p7:thm:Pn` throughout its real
probability-law regime.  At this historical 905/11,458 checkpoint that label
still remained **Partial**, because its leading-coefficient formula and
consequent strict odd-degree drop had not yet been formalized.

#### Inner complex-product normalization bridge

`GeometricUniformComplexMomentProduct.lean` adds one source module and three
public declarations to the historical 905/11,458 real-bridge checkpoint,
bringing that incoming branch checkpoint to 906/11,461.  Its exhaustive 1+2
surface is the
definition `geometricUniformComplexMomentProduct` and the theorems
`hasProdLocallyUniformly_geometricUniformComplexMomentProduct` and
`geometricUniformMomentPolynomial_eval₂_eq_complexMomentProduct_taylorCoefficient`.
Its thirteen helper declarations are private and excluded from the public
count.

For every complex `q` with `‖q‖ < 1`, including `q=0` and negative real
contractions, this leaf constructs
`A_q(z)=∏' j, complexExpm1Div ((1-q)*q^j*z)`, proves locally uniform convergence
on the whole complex plane, and identifies the recursive polynomial by
`P_n(q)=((q;q)_n/(1-q)^n)·(iteratedDeriv n A_q 0/n!)`.  For nonreal `q`, this
analytic product is not described as a probability MGF; the preceding real
0+1 theorem remains the exact probability-law MGF bridge.

The later reciprocity tranche promotes
`differentiable_geometricUniformComplexMomentProduct` to the public API.
Thus the current exhaustive surface of this module is one definition and
three theorems: `geometricUniformComplexMomentProduct`,
`hasProdLocallyUniformly_geometricUniformComplexMomentProduct`,
`differentiable_geometricUniformComplexMomentProduct`, and
`geometricUniformMomentPolynomial_eval₂_eq_complexMomentProduct_taylorCoefficient`.
The added theorem packages differentiability on all of `ℂ`, so the product
is now publicly known to be entire; the 906/11,461 count above remains the
historical checkpoint before that theorem was public.

#### Half-base q-binomial root-simplicity tranche

After the merged exact-closure and inner-complex union reached the historical
918/11,568 checkpoint, `HalfQBinomialRootSimplicity.lean` added one source
module and one public declaration, giving the merged-main pre-local checkpoint
919 modules and 11,569 public declarations.  Its exhaustive 0+1 surface is
`halfQBinomial_sum_rootMultiplicity_two_pow`.

For every `j < n`, the theorem proves over `ℚ` that the coefficientwise
half-base q-binomial polynomial
`∑_{k≤n} (-1)^k (1/2)^(k.choose 2) halfQBinomial n k · X^k` has root
multiplicity exactly one at `2^j`.  Together with the existing complete
rational root classification, every root in that half-base locus is simple.
No arbitrary-base, arbitrary-field, or general cyclotomic simplicity claim is
made.

#### Exterior complex reciprocal-germ normalization bridge

`GeometricUniformExteriorComplexMomentGerm.lean` adds one source module and
three public declarations to the merged-main pre-local 919/11,569 checkpoint,
bringing the merged exterior checkpoint to 920/11,572.  Its
exhaustive 1+2 surface is the definition
`geometricUniformExteriorComplexMomentGerm` and the
theorems `analyticAt_geometricUniformExteriorComplexMomentGerm` and
`geometricUniformMomentPolynomial_eval₂_eq_exteriorComplexMomentGerm_taylorCoefficient`.
Its twelve helper declarations are private and excluded from the public
count.

For every complex `q` with `1 < ‖q‖`, the leaf defines the manuscript's actual
reciprocal germ `M_q(z)=(A_{q⁻¹}(-z))⁻¹`, proves that it is analytic at zero,
and identifies the recursive polynomial by
`P_n(q)=((q;q)_n/(1-q)^n)·(iteratedDeriv n M_q 0/n!)`.  The definition is a
total Lean inverse, but its analytic claim is deliberately local at the
origin.  It asserts no global holomorphy across poles, pole divisor, boundary
case `‖q‖=1`, or rational-function continuation in the parameter.

The inner-disc product, exterior reciprocal germ, and both Taylor-coefficient
normalizations are therefore exact.  At this historical exterior checkpoint,
monograph label `thm:qF-moment-polynomial` was still **Partial** because no
named global `RatFunc` identified those regime-wise coefficients as one
rational parameter object.  The later RatFunc tranche below closes exactly
that assembly boundary.  Label `thm:geometric-uniform-mgf` remains
**Partial**: coefficient rationality and the `q=1` specialization are now
packaged, but no public theorem packages the product's dilation/Mahler law,
normalization, formal uniqueness, exact pole data, or
direct equality of the complex product with the real MGF or characteristic
function.  Frontier label `p7:thm:Pn` and proposition
`prop:qF-P-degree-sharp` are accounted for by the following sharp-degree
tranche.

#### Sharp geometric-uniform coefficients and exact degree

`GeometricUniformMomentPolynomialDegree.lean` adds one source module and three
public declarations to the 920/11,572 exterior checkpoint, giving the
historical sharp checkpoint 921 modules and 11,575 public declarations.  Its
exhaustive 0+3 surface is
`coeff_geometricUniformMomentPolynomial_choose_two`,
`coeff_geometricUniformMomentPolynomial_choose_two_sub_one`, and
`geometricUniformMomentPolynomial_natDegree_eq`.

For every natural `n`, the first theorem identifies the coefficient at the
triangular bound with `bernoulli' n / n!`, equivalently `(-1)^n B_n/n!` in the
manuscript convention.  For `n ≥ 2`, the second gives the coefficient one
below that bound as
`-bernoulli' n/n! + bernoulli' (n-1)/(2*(n-1)!)`.  The third proves exact
natural degree `n.choose 2` for `n=1` and even `n`, including `n=0`, and
`n.choose 2-1` for odd `n>1`.  Thus `prop:qF-P-degree-sharp` is **Exact**;
together with the algebraic recurrence and boundary tranche, the represented
frontier theorem `p7:thm:Pn` is **Exact**.  The separate real bridge keeps
`p7:eq:Pn-def` Exact on real `|q|<1`.  This
purely algebraic leaf adds no analytic continuation or root-of-unity claim.
At this historical sharp checkpoint, `thm:qF-moment-polynomial` therefore
remained **Partial**; the later global RatFunc leaf promotes it by assembly.

That algebraic source checkpoint was 913 modules and 11,551 public declarations, with
no missing module header or declaration comment.  Its then-current canonical
`thm:qF-moment-polynomial` status was **Partial** exactly as stated above.

#### Thue--Morse Gamma-tower differential tranche

`ThueMorseGammaTowerDifferential.lean` adds no definitions and exactly three
theorems: `hasDerivAt_mellin_mellinKernel_parameter`,
`hasDerivAt_thueMorseGammaLog_succ`, and
`iteratedDeriv_thueMorseGammaLog`.  For every complex Mellin exponent and
positive real damping parameter, the first differentiates under the integral
and shifts `s` to `s+1`; the other two give
`L_(r+1)'(a)=(r+1)L_r(a)` and the falling-factorial iterated law through
exactly `k ≤ r`.  With the existing Gamma-tower Mellin, integral, dyadic, and
ratio results, this makes `p2:thm:gamma-tower` **Exact** on the stated `0 < a`
domain.  These theorems concern the chosen `thueMorseGammaLog` coordinate,
not a proved branch or principal-`Complex.log` identity, and assert no
nonpositive-parameter extension.

The strengthened `GeometricResidualMoments.lean` surface has no public
definitions and exactly nine public theorems.  Its new
`sum_geometricLagrangeWeight_mul_eval_scaled_geometric` theorem works over
every field under exactly
`Set.InjOn (fun k : ℕ ↦ q ^ k) (Finset.range (p + 1))`, and reproduces
`P.eval 0` for every polynomial with `P.natDegree ≤ p` and every scale `c`,
including zero.  Together with
`sum_geometricLagrangeWeight_mul_scaled_geometric_pow_of_pos`, this makes
`cor:scaled-geometric-moments` **Exact** by composition and strengthens the
manuscript's `c ≠ 0` hypothesis.

The resulting bridge-stage inventory was 915 modules and 11,556 public declarations,
with no missing module header or declaration comment.

#### Finite-functional, local-corner, and central-Legendre closure tranche

The final exact-closure tranche adds two modules and nine public declarations
to the 915/11,556 bridge checkpoint.  That exact-closure checkpoint was
therefore 917 modules and 11,565 public declarations.  With the subsequent
inner complex-product union, the next historical checkpoint was 918 modules
and 11,568 public declarations.  The half-base root-simplicity leaf gave the
merged-main pre-local checkpoint 919/11,569; the exterior reciprocal-germ leaf
then gave 920/11,572; and the sharp coefficient-and-degree leaf gave the
historical 921/11,575 checkpoint.  `RvachevLaurentLeading.lean` then gave
922/11,582, `FinitePrefixAppellRecovery.lean` gave the historical pre-RatFunc
checkpoint 923/11,610, and `GeometricUniformMomentRatFunc.lean` gave the
historical RatFunc checkpoint 924/11,615.  The two new
`ProbabilityLaplaceMoments.lean` theorems gave 924/11,617, and
`RvachevLegendreBiorthogonality.lean` gave the historical facade inventory 925
modules and 11,619 public declarations, with no missing module header or public
declaration comment at that checkpoint.  Later merged work reached the
pre-reciprocity 930/11,678 checkpoint; reciprocity then gave the historical
931/11,685 checkpoint, and the dyadic-boundary and finite-prefix-collapse
leaves gave the historical 933/11,695 checkpoint.  The incoming base-two
Prouhet bridge and the strengthened dyadic-boundary and Newman APIs described
below give the historical 934/11,709 inventory.  The subsequent nine-module
series/transseries tranche (72 explicit declarations), together with six
concurrent declarations outside that tranche, gave the historical 943/11,787
inventory.  The later nine-module/90-declaration transseries tranche and four
new declarations in `TransseriesDifferentialBlock.lean` gave the historical
incoming 952/11,881 inventory.  The subsequent three-theorem exactness overlay
gives the live 952/11,884 inventory, again with no missing module header or
public declaration comment.

`FinitePolynomialFunctional.lean` remains a zero-definition module and now has
exactly sixteen public theorems:
`sum_weight_mul_eval₂_eq_sum_coeff_mul_moment`,
`sum_weight_mul_eval₂_eq_eval₂_of_moments`,
`sum_weight_mul_eval₂_eq_coeff_mul_moment`,
`sum_weight_mul_eval₂_eq_topCoeff_mul_moment`,
`sum_weight_mul_eval₂_eq_constantCoeff_mul_sum`,
`sum_weight_mul_eval₂_eq_constantCoeff`,
`sum_weight_mul_eval₂_eq_map_coeff_mul_of_moments`,
`sum_weight_mul_eval₂_eq_map_coeff_mul_top_moment`,
`sum_weight_mul_eval₂_eq_zero_of_degree_lt`,
`sum_weight_mul_eval₂_congr_of_map_coeff_eq`,
`sum_weight_mul_eval_eq_eval_of_moments`,
`sum_weight_mul_eval_eq_coeff_mul_of_moments`,
`sum_weight_mul_eval_eq_coeff_mul_top_moment`,
`sum_weight_mul_eval_eq_zero_of_degree_lt`,
`sum_weight_mul_eval_congr_of_coeff_eq`, and
`sum_weight_mul_eval_affine_of_topCoeff_extractor`.
The first ten are scalar-extension results from an arbitrary semiring to a
commutative semiring; the five same-ring conveniences and the affine theorem
need only a commutative semiring.  The common proof expands `eval₂` into its
finite coefficient sum, swaps the two finite sums, and inserts the prescribed
moments.  For affine transport, apply the supplied extractor to
`p.comp (C b * X + C a)` and compute its degree-`n` coefficient as
`p.coeff n * b^n`; a separate zero-scale argument retains `b=0` and `n=0`.
No distinctness, nonzero scale, subtraction, or nonzero surviving moment is
assumed.  Composing the affine theorem with
`halfQBinomial_negativeDyadic_polynomial_sum_eq_mersenne` makes
`cor:geometric-prouhet-affine` **Exact** under the existing rational-polynomial
convention.

`ThueMorseCornerIntegral.lean` has one public definition,
`centeredBoxIntegral`, and exactly four public theorems:
`centeredBoxIntegral_zero`, `centeredBoxIntegral_succ`,
`symmetricMixedDifference_range_eq_centeredBoxIntegral`, and
`symmetricMixedDifference_univ_eq_centeredBoxIntegral`.
For nonnegative half-steps, an open order-connected set `I`,
`ContDiffOn ℝ N g I`, and containment of the full symmetric segment
`[x-∑i<N,a i,x+∑i<N,a i]` in `I`, the last two theorems identify the range and
`Fin N` corner sums with the centered nested integral of `iteratedDeriv N g`.
The induction peels the final mixed difference, applies the local interval FTC
at every powerset corner, moves the finite sum through the outer integral, and
recurses on `deriv g`.  These are genuinely local hypotheses, not a global
`ContDiff` replacement.  Zero half-steps and `N=0` are included, strengthening
the printed positive-step domain; arbitrary signed half-steps are not claimed.
Together with `ThueMorseSymmetricDifference.lean`, this makes
`thm:TM-corner` **Exact**.  The following Walsh conditional-expectation
corollary remains outside the surface.

`RvachevLegendreCentralSum.lean` has no public definitions and exactly three
public theorems: `eval_legendrePolynomial_even_zero`,
`eval_rvachevLegendreDeconvolutionPolynomial_even`, and
`rvachevLegendreCentralSum`.  The last theorem assumes
`F : BoundedFabius`, `IsFabius F`, and `n : ℕ`, sets the exact mesh
`M=4^n`, and proves the printed finite central-binomial cancellation, including
`n=0`.  Its proof evaluates the existing even-mode synthesis at zero, truncates
the open block from `|k|<2M` to `|k|<M` by compact support, pairs the remaining
nonzero nodes using the two evenness facts, clears `M`, and inserts the exact
central value of `P_(2n)`.  Hence `cor:leg-central-sum` is **Exact/Complete**.
No Jacobi closed form, all-degree decoder parity or rationality, reverse
spectral closure, mesh minimality, or larger Lagrange right-inverse statement
is inferred.

#### Half-base roots, Laurent-leading, and finite-prefix Appell recovery tranche

The half-base root leaf first raised the historical 918/11,568 complex-product
checkpoint to 919/11,569.  After the exterior and sharp-degree leaves produced
920/11,572 and the historical sharp checkpoint 921/11,575, the two subsequent
upstream leaves add exactly two modules and 35 public declarations:
`RvachevLaurentLeading.lean` gives 922/11,582, and
`FinitePrefixAppellRecovery.lean` gives the historical pre-RatFunc checkpoint
923 modules and 11,610 public declarations.  The subsequent global RatFunc
leaf gives the historical 924 modules and 11,615 public declarations; the
post-RatFunc probability and finite-biorthogonality additions below gave the
historical 925 modules and 11,619 public declarations, with no missing module
header or public declaration comment at that checkpoint.  Later source work
and reciprocity gave the historical 931/11,685 checkpoint; the dyadic-boundary
and finite-prefix-collapse leaves then gave the historical 933/11,695
checkpoint.  The incoming one-module/fourteen-declaration tranche gives the
historical 934/11,709 inventory.  The first series/transseries tranche and six
concurrent declarations then gave the
historical 943/11,787 checkpoint.  The later nine-module transseries tranche
and four integer-exponent differential-block declarations gave the historical
incoming 952/11,881 inventory; the three-theorem exactness overlay gives the
current 952/11,884 inventory, with no documentation gaps.

`HalfQBinomialRootSimplicity.lean` has no public definitions and exactly one
public theorem, `halfQBinomial_sum_rootMultiplicity_two_pow`.  Over `ℚ`, for
every `j<n`, it proves root multiplicity one at `2^j` for the coefficientwise
half-base q-binomial polynomial.  The proof differentiates the finite product:
at `2^j` every product-rule term except the deleted-`j` factor vanishes, and
the remaining product is nonzero.  Together with
`halfQBinomial_sum_eq_zero_iff` and
`gaussianBinomial_half_eq_halfQBinomial`, this supplies exactly the manuscript
polynomial's roots `1,2,…,2^(n-1)`, proves that all are simple, and excludes
all other rational roots.  Thus `cor:halfbase-root-locus` is **Exact by
composition**.  No arbitrary-characteristic simplicity statement or
arbitrary-base root classification is inferred.

`RvachevLaurentLeading.lean` adds one definition,
`rvachevCenteredMGF`, and exactly six theorems:
`rvachevCenteredMGF_eq_rvachevFourierProduct`,
`rvachevCenteredMGF_pi_mul_I_int`,
`rvachevCenteredMGF_pi_mul_I_int_ne_zero_of_odd`,
`tendsto_sub_pow_mul_inv_rvachevFourierProduct_int`,
`tendsto_rvachevCenteredMGF_laurent_int`, and
`tendsto_rvachevCenteredMGF_laurent_two_pow_mul_odd`.
The definition corrects for the existing generating function's half-scale by
setting `M(t)=centeredComplexGeneratingFunction F (2*t)`; the first theorem
then proves the exact rotation `M(t)=Φ(i*t/(2π))`.  The generic limit cancels
the order `padicValNat 2 |m|+1` of every nonzero integer zero of `Φ` and tends
to the inverse analytic cofactor.  Transport through the rotation gives the
integer centered-MGF limit.  Finally, if `n=2^v*u` with `u` an odd signed
integer, the manuscript-normalized wrapper proves pole order `v+1` and
leading coefficient `-T_n^(v+1)/M(π*i*u)` at `T_n=2π*i*n`; the preceding
odd-core theorem proves the displayed denominator nonzero.  Every reciprocal
limit is taken through `𝓝[≠]`, not the full neighborhood: Lean's inverse is
totalized by `0⁻¹=0` at the pole.  This makes
`is:p2:thm:Laurent-leading` **Exact** without asserting lower Laurent
coefficients, pole-shell summation, or Appell-coefficient asymptotics.

`FinitePrefixAppellRecovery.lean` adds eleven definitions:
`unitUniformRawMomentRat`, `centeredUnitUniformRawMomentRat`,
`dyadicPrefixScaleRat`, `dyadicPrefixMomentRat`,
`uncenteredDyadicPrefixMomentRat`, `centeredDyadicPrefixMomentRat`,
`kabayaIriAppellPolynomialRat`,
`uncenteredDyadicPrefixAppellPolynomialRat`,
`centeredDyadicPrefixAppellPolynomialRat`,
`uncenteredDyadicPrefixAppellScalePolynomialRat`, and
`centeredDyadicPrefixAppellScalePolynomialRat`.  Its exactly seventeen public
theorems are `Appell.poly_binomialConv`, `Appell.binomialConv_dilate`,
`Appell.dilate_dilate`, `dyadicPrefixMomentRat_zero`,
`uncenteredDyadicPrefixMomentRat_zero`,
`centeredDyadicPrefixMomentRat_zero`,
`dyadicPrefixMomentRat_binomialConv_tail`,
`binomialConv_uncenteredDyadicPrefixMomentRat_tail`,
`binomialConv_centeredDyadicPrefixMomentRat_tail`,
`uncenteredDyadicPrefixAppellPolynomialRat_eq_sum`,
`centeredDyadicPrefixAppellPolynomialRat_eq_sum_even`,
`uncenteredDyadicPrefixAppellPolynomialRat_eq_eval_scale`,
`centeredDyadicPrefixAppellPolynomialRat_eq_eval_scale`,
`natDegree_uncenteredDyadicPrefixAppellScalePolynomialRat`,
`natDegree_centeredDyadicPrefixAppellScalePolynomialRat`,
`kabayaIriAppellPolynomialRat_eq_sum_prefix`, and
`rvachevAppellPolynomialRat_eq_sum_prefix`.

The prefix moments are constructed independently by finite binomial
convolution of scaled uniform digits.  The one-step full-moment recurrences
give exact tail factorizations, reciprocal uniqueness reverses them, and the
generic Appell transform gives the complete uncentered expansion in powers of
`2^-N` and the centered even expansion in powers of `4^-N`.  As elements of
`Polynomial (Polynomial ℚ)`, their outer degrees are exactly `n` and
`⌊n/2⌋`.  That qualifier is essential: evaluating the inner polynomial at a
fixed `x` can lower the outer degree, and in the centered odd case the top
inner coefficient vanishes at `x=0`.  The final two theorems evaluate these
scale polynomials at zero with the existing geometric Lagrange rows.  From any
starting depth `N`, they recover the full Kabaya--Iri polynomial from the
`n+1` prefixes `N,…,N+n` at base `1/2`, and the full centered
Rvachev--Appell polynomial from the `⌊n/2⌋+1` prefixes
`N,…,N+⌊n/2⌋` at base `1/4`.  These are finite exact rational identities,
not limits.  Accordingly both `is:p2:thm:finite-prefix-expansion` and
`is:p2:thm:exact-recovery` are **Exact**.  No analytic MGF convergence or
universal fixed-`x` degree statement is added.

#### Global geometric-uniform moment RatFunc bridge

`GeometricUniformMomentRatFunc.lean` adds one source module and five public
declarations to the historical pre-RatFunc 923/11,610 checkpoint, giving the
historical RatFunc checkpoint 924 modules and 11,615 public declarations.  Its
exhaustive 1+4 surface
is the definition `geometricUniformMomentRatFunc` and the theorems
`qFactorial_mul_geometricUniformMomentRatFunc`,
`eval_geometricUniformMomentRatFunc_eq_complexMomentProduct_taylorCoefficient`,
`eval_geometricUniformMomentRatFunc_eq_exteriorComplexMomentGerm_taylorCoefficient`,
and `eval_geometricUniformMomentRatFunc_one`.  All supporting declarations are
private and excluded from the public count.

The definition packages the single rational coefficient
`a_n(X)=P_n(X)/[n]_X!` in `RatFunc ℚ`.  Its global theorem proves the safe
pole-clearing identity `[n]_X!·a_n=P_n`.  Safe evaluation of this same object
is the inner complex-product Taylor coefficient for every `‖q‖<1`, including
`q=0` and `n=0`, and the exterior reciprocal-germ Taylor coefficient for every
`1<‖q‖`.  At `q=1`, where `[n]_1!=n!`, the final theorem gives the removable
specialization `a_n(1)=P_n(1)/n!`.  Together with the algebraic, inner, and
exterior tranches, this makes canonical `thm:qF-moment-polynomial` **Exact by
assembly**.  Evaluation remains conditional on denominator nonvanishing: no
value is assigned at a genuine pole, and no exact pole divisor or pole-order
theorem, analytic continuation through `‖q‖=1`, or global holomorphy of the
exterior reciprocal is claimed.  Label `thm:geometric-uniform-mgf` remains
**Partial** under the boundary stated above.

#### Complex moment-product entireness and germ reciprocity

Merged upstream additions reached the immediate pre-reciprocity checkpoint
930 modules and 11,678 public declarations.  The reciprocity tranche promotes
one theorem in the existing complex-product module and adds the new
`GeometricUniformMomentReciprocity.lean` module with one definition and five
theorems.  It therefore adds one source module and seven public declarations
in total, giving the historical reciprocity checkpoint 931/11,685.

The current exhaustive 1+3 surface of
`GeometricUniformComplexMomentProduct.lean` is the definition
`geometricUniformComplexMomentProduct` and the theorems
`hasProdLocallyUniformly_geometricUniformComplexMomentProduct`,
`differentiable_geometricUniformComplexMomentProduct`, and
`geometricUniformMomentPolynomial_eval₂_eq_complexMomentProduct_taylorCoefficient`.
The promoted differentiability theorem is global on `ℂ`, so the locally
uniform product is publicly packaged as an entire function.

The reciprocity leaf's exhaustive 1+5 surface is the definition
`geometricUniformComplexMomentGerm` and the theorems
`geometricUniformComplexMomentGerm_of_norm_lt_one`,
`geometricUniformComplexMomentGerm_of_one_lt_norm`,
`analyticAt_geometricUniformComplexMomentGerm`,
`geometricUniformComplexMomentGerm_reciprocity`, and
`geometricUniformComplexMomentGerm_moment_convolution`.  The combined function
is the inner product when `‖q‖<1`, the exterior reciprocal when `1<‖q‖`, and
is analytic at zero whenever `‖q‖≠1`.  Under exactly `q≠0` and `‖q‖≠1`,
the reciprocity theorem proves
`M_q(z) * M_{q⁻¹}(-z) = 1` locally as an `EventuallyEq` in `𝒩 0`, and
the convolution theorem proves for every order `n` the exact binomial
iterated-derivative convolution with value `if n=0 then 1 else 0`.  The germ
boundary is deliberate: the inner product can have remote zeros and Lean's
inverse is total, so no global pointwise reciprocal identity or unit-circle
continuation is asserted.  This makes canonical `thm:qF-reciprocity`
**Exact**.

#### Dyadic-boundary and finite-prefix Thue--Morse-collapse census overlay

Two subsequently merged zero-definition leaves add two source modules and ten
public theorems to the historical reciprocity checkpoint 931/11,685, giving
the historical 933/11,695 inventory.

At that checkpoint, `DyadicBoundaryIdentity.lean` had exactly two public theorems,
`prod_complexSinc_prefix_mul_rvachevFourierProduct` and
`rvachevFourierProduct_dyadic_boundary`.  The first clears the finite sinc
prefix against the rescaled Rvachev product.  The second composes that identity
with the integer-zero factorization to give the denominator-cleared
dyadic-boundary equality for every natural shell and complex displacement,
without a nonvanishing hypothesis.  A quotient formulation still requires the
denominator to be nonzero.

`FinitePrefixThueMorseCollapse.lean` has exactly eight public theorems:
`Appell.sum_thueMorseSign_mul_eval_poly`,
`sum_thueMorseSign_mul_uncenteredDyadicPrefixAppellPolynomialRat`,
`sum_thueMorseSign_mul_uncenteredDyadicPrefixAppellPolynomialRat_of_lt`,
`sum_thueMorseSign_mul_uncenteredDyadicPrefixAppellPolynomialRat_self`,
`sum_thueMorseSign_mul_centeredDyadicPrefixAppellPolynomialRat`,
`sum_thueMorseSign_mul_centeredDyadicPrefixAppellPolynomialRat_succ`,
`sum_thueMorseSign_mul_centeredDyadicPrefixAppellPolynomialRat_of_lt`, and
`sum_thueMorseSign_mul_centeredDyadicPrefixAppellPolynomialRat_self`.  The
general Appell theorem reduces a complete signed block to its Thue--Morse
power moments; the rational prefix specializations are total at depth zero,
with lower-degree cancellation and first-surviving-response corollaries.
These are finite coefficient identities rather than analytic convergence
statements.  This overlay records the merged APIs and changes no source-result
coverage status.

#### Closed-tail moments and finite Legendre--Rvachev biorthogonality

The post-RatFunc union first adds exactly two public theorems to the existing
`ProbabilityLaplaceMoments.lean` module, taking the historical 924/11,615
RatFunc checkpoint to 924/11,617.  The exhaustive added surface is
`weightedSumDistribution_real_Ici_eq_rvachevUp_of_nonneg` and
`integral_pow_weightedSumDistribution_eq_mul_intervalIntegral_rvachevUp`,
both in `Fabius.ProbabilityRepresentation`.  For `F : BoundedFabius`,
`IsFabius F`, and real `t ≥ 0`, the first theorem identifies the closed tail
of `weightedSumDistribution` with `rvachevUp F t`; atomlessness is what passes
from the previously formalized strict tail to the closed tail, via
`weightedSumDistribution_singleton`.  For every
natural `n ≥ 1`, the second identifies the full-line expectation of `x^n`
with `n * ∫ t in (0)..1, t^(n-1) * rvachevUp F t`.  Together with the existing
global distribution and integrability results, including
`rvachevUp_eq_fabiusReal_one_sub_abs` and
`rvachevUp_eq_one_sub_fabiusReal_of_nonneg`, these make every clause of
`prop:up-tail` and `cor:up-moments` **Exact** on domains at least as strong as
printed.  These are full-line identities for the canonical law representing
the manuscript's `X`, not a new arbitrary-random-variable wrapper.  The moment
theorem does not assert the `n=0` case.

`RvachevLegendreBiorthogonality.lean` then adds one source module and exactly
one definition plus one theorem, giving the historical 925/11,619 checkpoint.  Its
exhaustive public surface is `rvachevLegendreAnalysisKernel` and
`rvachevLegendreBiorthogonality`, both in `Fabius`.  For
clarity, the former is literally the normalized kernel
`((2*m+1)/2) * integral_(-1)^1 up(x-c) P_m(x) dx`.  For
`F : BoundedFabius`, `IsFabius F`, `M : ℕ`, `M ≠ 0`, and
`l ≤ padicValNat 2 M`, the theorem proves the exact normalized
analysis/synthesis pairing over the finite open block
`Finset.Ioo (-(2*M)) (2*M)` (equivalently `|k| < 2M`): the result is
`if m = l then 1 else 0`.  Thus `thm:leg-biorthogonality` is **Exact**.
The broader `thm:leg-Lambda` remains incomplete because the kernel's support,
smoothness, parity, origin values, Fourier--Bessel formula, and dyadic
rationality are not all formalized; `cor:leg-biorthogonal-matrices` remains
incomplete because no bundled matrix projector or reverse spectral closure is
provided.

#### Merged support leaves, reciprocity, and finite-prefix Thue--Morse collapse

Relative to the historical 925/11,619 checkpoint, five merged support modules
and consolidation of existing surfaces first added five modules and fifty-nine
public declarations, reaching the immediate pre-reciprocity 930/11,678
checkpoint.  The five modules account for thirty declarations:
`QPochhammerLambertForm.lean` is 0+5,
`CentralQVandermondeInfinite.lean` is 0+4,
`ThueMorseNewmanSelfSimilarity.lean` is 1+12,
`TriangularPowerProduct.lean` is 0+2, and `MeanValueBracket.lean` is 0+6.
Respectively, these expose the complex and
real Lambert exponential forms of the infinite q-Pochhammer symbol; the
central q-Vandermonde limit and its `HasSum`/`Summable`/`tsum` forms; exact
base-four Newman amplification, geometric-ray ratios, and nonconvergence; two
commutative-monoid triangular exponent products; and two-sided mean-value and
residual-to-error brackets.  Consolidation of existing source surfaces gives
the remaining net twenty-nine declarations.  The reciprocity tranche then
added one module and seven public declarations, giving the historical
931/11,685 checkpoint.  `DyadicBoundaryIdentity.lean` 0+2 and the finite-prefix
collapse leaf below added two modules and ten declarations, giving the
historical 933/11,695 checkpoint.
This census accounting records the merged public API and by itself assigns no
new frontier status to those support results.

`FinitePrefixThueMorseCollapse.lean` accounts for eight of those ten final
declarations.  It has no public definitions and exactly eight
public theorems.  The generic theorem
`Appell.sum_thueMorseSign_mul_eval_poly` states, for an arbitrary rational
Appell sequence, that the signed block on the grid `x+k*h` is the coefficient
sum with factors `(n.choose r) * h^r * thueMorsePowerSum N r` and lower Appell
polynomial `n-r`.

The uncentered main theorem
`Fabius.sum_thueMorseSign_mul_uncenteredDyadicPrefixAppellPolynomialRat`
uses `thueMorseSign k` on the exact grid `x+k/2^N` and returns
`(-1)^N * 2^{-((N+1).choose 2)} * n.descFactorial N * x^(n-N)`.
`Fabius.sum_thueMorseSign_mul_uncenteredDyadicPrefixAppellPolynomialRat_of_lt`
specializes this to zero for `n<N`, while
`Fabius.sum_thueMorseSign_mul_uncenteredDyadicPrefixAppellPolynomialRat_self`
gives the first response
`(-1)^N * N! * 2^{-((N+1).choose 2)}`.

The centered main theorem
`Fabius.sum_thueMorseSign_mul_centeredDyadicPrefixAppellPolynomialRat`
uses the total grid `x+(1-2^-N)-2k/2^N` and returns the sign-free response
`2^{-(N.choose 2)} * n.descFactorial N * x^(n-N)`.
`Fabius.sum_thueMorseSign_mul_centeredDyadicPrefixAppellPolynomialRat_succ`
rewrites the positive depth as `N=m+1` and uses the manuscript's literal grid
`x+(1-2^{-(m+1)})-k/2^m` with the same scale.
`Fabius.sum_thueMorseSign_mul_centeredDyadicPrefixAppellPolynomialRat_of_lt`
gives zero for `n<N`, and
`Fabius.sum_thueMorseSign_mul_centeredDyadicPrefixAppellPolynomialRat_self`
gives `N! * 2^{-(N.choose 2)}`.  The two primary theorems and both first-response
corollaries include `N=0`; only the literal-grid successor wrapper is
positive-depth-indexed.

Consequently the uncentered main theorem supplies the exact compositional
closure of `is:p2:thm:TM-uncentered`; its `_of_lt` and `_self` corollaries give
the exact Prouhet cancellation and first surviving value required by
`is:p2:cor:Prouhet-canonical`; and the centered `_succ` theorem supplies the
exact printed grid for `is:p2:thm:TM-centered`, strengthened at `N=0` by the
total centered theorem.  This is rational coefficient-model algebra only.  It
introduces no random variable or `HasLaw` theorem and proves no analytic MGF or
Barnes-function identification.

#### Base-two Prouhet, printed dyadic boundary, and Newman oscillation overlay

The incoming tranche adds one module and fourteen public declarations to the
historical 933/11,695 checkpoint, giving the historical 934/11,709 inventory.  The
delta is the union of the new zero-definition/six-theorem
`ProuhetBaseTwoBridge.lean` leaf, one theorem added to
`DyadicBoundaryIdentity.lean`, and seven theorems added to
`ThueMorseNewmanSelfSimilarity.lean`; it is not fourteen declarations in the
new module alone.

The exhaustive `ProuhetBaseTwoBridge.lean` surface is
`thueMorseSign_cast_eq_neg_one_pow_digits_sum`,
`digitPowerSum_neg_one_two`, `sum_range_two_neg_one_pow`,
`digitPowerSum_neg_one_two_eq_zero_of_lt`,
`digitPowerSum_neg_one_two_self`, and
`sub_one_pow_mul_thueMorsePowerSumRing_self`.  Over every commutative ring it
identifies the base-two digit-weighted sum at `ζ=-1` with the Thue--Morse power
sum, obtains strict-low-degree Prouhet cancellation from the general digit
machine, and gives both the closed sharp moment
`(-1)^m * 2^(m.choose 2) * m!` and its division-free general-machine form.

`DyadicBoundaryIdentity.lean` is now 0+3.  Its added theorem,
`norm_rvachevFourierProduct_dyadic_boundary`, states the printed norm-quotient
identity on exactly `0 < z < 2^k`; central-lobe positivity proves that the
divided product is nonzero.  The existing prefix-product and denominator-free
entire identities remain unchanged.

`ThueMorseNewmanSelfSimilarity.lean` is now 1+19.  Its seven added theorems are
`eight_rpow_logb_four_three`,
`sqrt_three_div_three_lt_two_div_three`, `newman_ratio_eight`,
`newman_ratio_eight_lt_two_div_three`,
`frequently_newmanRatio_eq_two_div_three`,
`frequently_newmanRatio_eq_sqrt_three_div_three`, and
`newmanRatio_oscillates`.  They identify the second recurrent ratio as
`sqrt 3 / 3`, compare it strictly with `2/3`, prove both values recur
frequently at `atTop`, and package the resulting explicit oscillation.  This
overlay preserves the incoming API descriptions and makes no additional
source-result status move.

#### Series and transseries exactness overlay

The next source-only overlay consists of nine facade-reachable modules with 72
lexically explicit public declarations.  `TransseriesWellBased.lean` also
generates two additive names with `to_additive`; those names are part of the
usable API but, consistently with the audit's documented lexical scope, are
not included in the 11,787 declaration count.  Six further declarations from
concurrent merged work account for the rest of the change from the historical
934/11,709 checkpoint.  This produced the now-historical 943-module/11,787-
declaration checkpoint, with zero missing module headers and zero missing
declaration comments.  The later overlays documented below establish the
authoritative current census of 952 modules and 11,884 explicit public
declarations, again with zero documentation gaps.

`UnitSeriesBellCoefficients.lean` has no public definitions and exactly sixteen
public theorems:
`ordPartialBell_eq_factorialRatio_partialBell`,
`factorial_mul_ordPartialBell_eq_factorial_mul_partialBell`,
`coeff_fallingSeries_subst_eq_sum_ordPartialBell`,
`coeff_fallingSeries_subst_eq_sum_ordPartialBell_of_pos`,
`coeff_fallingSeries_subst_eq_sum_partialBell`,
`coeff_negBinomSeries_subst_eq_sum_ordPartialBell`,
`coeff_negBinomSeries_subst_eq_sum_ordPartialBell_of_pos`,
`coeff_logOf_eq_sum_ordPartialBell`,
`egfA_factorialDenormalize_coeff_eq`,
`bellWeightSeries_factorialDenormalize_coeff_eq`,
`coeff_logOf_eq_sum_partialBell`, `coeff_exp_subst_eq_completeBell`,
`coeff_exp_subst_eq_partitionExpSum`,
`coeff_exp_subst_eq_sum_weightedPartitions`,
`coeff_exp_subst_eq_sum_div_weightedPartitions`, and
`coeff_exp_subst_recurrence`.  They make `p0:lem:bell-conversion`,
`p0:lem:power-log`, and `p0:cor:exp-log-jets` **Exact**, including stronger
all-index forms where the types permit.  The scope is formal power-series
coefficient algebra over the indicated commutative rational algebras or
fields.  No analytic convergence or analytic logarithm-branch assertion is
made.

`TransseriesWellBased.lean` has no public definitions and seven explicitly
written public theorems: `dickson_isPWO`, `dickson_antichain_finite`,
`dickson_isPWO_pi`, `neumann_isPWO`, and
`neumann_finite_factorizations`, together with
`neumann_isPWO_orderDual` and `neumann_finite_factorizations_orderDual`.  Its
attributes additionally generate
`neumann_add_isPWO` and `neumann_finite_decompositions`.  Thus
`q0:lem:dickson` and `q0:lem:neumann` are **Exact**; the explicit wrappers
state the latter directly in the dual order.  In a total order this matches the
manuscript's reverse-well-order/no-strict-growth convention, while for a
merely partial order the precise statement is `Set.IsPWO` on `OrderDual α`,
not a greatest-element characterization.  The
Neumann API works in an ordered cancel commutative monoid; it proves the
well-based product and finite-factorization mechanism, not a new Hahn-series
type.

`TransseriesHeight.lean` has no public definitions and exactly three theorems:
`isLittleO_log_pow_rpow`, `isLittleO_log_pow_id`, and
`isLittleO_pow_mul_log_pow_exp`.  They make both printed real `atTop`
comparisons in `q0:prop:height` **Exact**, under their natural-power and
positive-real-exponent hypotheses.  They do not define a recursive global
height/depth relation on arbitrary nested transmonomials.

`TransseriesScale.lean` has one public structure, one public definition, and
three public theorems: `IsAsymptoticScale`, `IsPoincareExpansion`,
`IsPoincareExpansion.isLittleO_succ_remainder`,
`IsPoincareExpansion.tendsto_coeff`, and
`IsPoincareExpansion.coeff_unique`.  These make the sequence-indexed content
of `q0:def:scale`, `q0:def:poincare`, and `q0:prop:uniqueness` **Exact** over
an arbitrary filter and normed field.  The uniqueness theorem requires
`[l.NeBot]`, and the definition fixes the first-omitted-term remainder
convention.  It gives neither convergence nor recovery modulo flat functions,
and it does not package the manuscript's unordered-set or maximal-scale
notion.

`TransseriesScaleDominance.lean` has one public definition, `plMonomial`, and
seven public theorems: `tendsto_plMonomial_atTop_zero`,
`plMonomial_div_eventuallyEq`, `tendsto_plMonomial_div_atTop_zero`,
`tendsto_plMonomial_div_atTop_one`, `plMonomial_pos`,
`tendsto_plMonomial_div_atTop`, and
`plMonomial_generators_dominance`.  The analytic zero/one/`atTop`
lexicographic trichotomy and the integer-generator equivalence in
`plt:lem:mot-dominance` are **Exact**.  The result does not alone establish the
full unordered set or maximal-expansion package.

`TransseriesPolyLogScale.lean` has no public definitions and four public
theorems: `isLittleO_plMonomial`, `isAsymptoticScale_plMonomial`,
`isAsymptoticScale_plMonomial_pow`, and
`isAsymptoticScale_plMonomial_log`.  It proves the exact sequence-indexed
scale corollary for strictly lexicographically decreasing exponent pairs and
the two standard inverse-power and fixed-power/logarithmic ladders.  It does
not formalize the full unordered-set or finite-maximal clause of
`plt:def:mot-scale`.

`TransseriesBlockAntiderivative.lean` has three public definitions,
`blockOperator`, `blockAntiderivative`, and `resonantAntiderivative`, and
twelve public theorems: `sum_sub_sum_shift`, `blockOperator_zero`,
`blockOperator_sub`, `blockOperator_blockAntiderivative`,
`blockOperator_surjective`, `natDegree_C_mul_of_ne_zero`,
`natDegree_blockOperator`, `blockOperator_injective`,
`blockOperator_bijective`, `derivative_resonantAntiderivative`,
`derivative_surjective`, and `natDegree_resonantAntiderivative`.  This makes
the polynomial-operator dichotomy of `plt:lem:mot-block-antiderivative`
**Exact**: for nonzero `c`, the explicit finite inverse to `∂_L-c` is
degree-preserving on nonzero polynomials; at `c=0`, the explicit primitive is
surjective and raises degree by one.  The theorem is about `K[L]`; it does not
construct the full Laurent ambient ring `K[t,t⁻¹][L]`.

`TransseriesDifferentialBlock.lean` has no public definitions and exactly nine
theorems.  Its prior natural-exponent surface is `derivation_pow_t`,
`derivation_block`, `exists_block_primitive`, `derivation_block_zero`, and
`exists_block_primitive_resonant`; the incoming integer-exponent extension is
`derivation_val_inv`, `derivation_pow_inv`, `derivation_zpow_t`, and
`derivation_block_zpow`.  For a commutative algebra with a derivation satisfying
`d(t)=-t²` and `d(L)=t`, the first five bridge the polynomial operator to
blocks `t^n p(L)` and supply natural-exponent primitives.  When `t` is the
value of a unit, the final four prove the inverse-power, integer-power, and
integer-block derivative laws, making the displayed
`plt:eq:mot-block-derivative` exact for every integer exponent in that abstract
model.  The larger `plt:prop:dif-block` remains **Partial**: this module does
not construct the concrete Laurent ring, and primitive existence is still
exposed only for natural exponents.

`QuadraticCoreCatalan.lean` has three public definitions, `quadHalf`,
`halfBinom`, and `quadCoef`, and eight public theorems: `catalan_two_step`,
`quadHalf_zero`, `quadHalf_antidiagonal`, `halfBinom_step`, `quadHalf_rat`,
`quadCoef_rat`, `quadCoef_zero`, and `quadCoef_rec`.  The Catalan closed form
and convolution make `p6:prop:quadratic-core-catalan` **Exact** over fields of
characteristic zero.  `p6:lem:quadratic-core` is only **Partial**: the module
proves the coefficient family and coefficientwise recursion, but not a
packaged formal-power-series existence/uniqueness statement, square-root
identity, or exact denominator-exponent clause.  `p6:thm:deepest-pole` is
**Absent**: there is no formal Gamma/Barnes identification.  The finite
Catalan recurrence itself uses no analytic convergence.

#### Later transseries formalization tranche

The later incoming tranche adds nine facade-reachable modules with fifteen
definitions and seventy-five theorems, hence 90 lexically explicit public
declarations.  Four further theorems extend the existing
`TransseriesDifferentialBlock.lean` surface from 0+5 to 0+9.  Relative to the
historical 943/11,787 checkpoint, the exact delta is therefore nine modules
and 94 explicit declarations, giving the historical incoming census of 952
modules and 11,881 explicit public declarations.  The two OrderDual wrappers
and Wright-omega analyticity theorem keep 952 modules and give the
authoritative current census of 11,884 explicit public declarations.  The audit reports zero
missing module headers and zero missing declaration comments.  The two
`to_additive`-generated Neumann declarations remain usable API outside this
lexical total, exactly as at the preceding checkpoint.

`DerangementNearestInteger.lean` has one public definition,
`subfactorialDefect`, and seven public theorems:
`subfactorialDefect_zero`, `subfactorialDefect_succ`,
`subfactorialDefect_pos`, `subfactorialDefect_lt`,
`numDerangements_sub_eq`, `abs_numDerangements_sub_lt_half`, and
`round_factorial_mul_exp_neg_one`.  It proves the defect integral and its
recursion, the exact signed difference between `numDerangements n` and
`n! * exp (-1)`, the strict integer-argument defect bounds, and the
nearest-integer conclusion for every `n ≥ 1`.  That numerical conclusion of
`p8:cor:nearest-integer` is **Exact**.  The full surrounding result remains
**Partial**: the bound for arbitrary real `x > -1`, the branch-splitting
theorem, and the interpolation family are not formalized.

`LinLogCoreInversion.lean` has four public definitions:
`linLogCoreArg`, `linLogCoreRoot`, `linLogCoreThreshold`, and
`linLogCoreRootLower`.  Its eighteen public theorems are
`linLogCore_eq_iff`, `principalLambertW_linLogCoreArg_pos`,
`linLogCoreRoot_pos`, `linLogCore_linLogCoreRoot`,
`strictMonoOn_linLogCore`, `linLogCoreRoot_unique`,
`hasDerivAt_linLogCore`, `linLogCore_slope_eq`, `linLogCore_critical`,
`linLogCoreArg_mem_Ioo_iff`, `principalLambertW_linLogCoreArg_neg`,
`linLogCoreRoot_pos_of_neg`, `linLogCoreRootLower_pos`,
`linLogCore_linLogCoreRoot_of_neg`,
`linLogCore_linLogCoreRootLower`, `linLogCoreRoot_lt_critical`,
`critical_lt_linLogCoreRootLower`, and
`linLogCoreRoot_ne_linLogCoreRootLower`.  They give the branch-free Lambert
equivalence, the unique positive principal root when `b > 0`, the sharp
threshold and two separated real roots when `b < 0`, and the slope identities.
These real algebraic and branch clauses of `p0:thm:lambert-core` are **Exact**;
the theorem remains **Partial** only at its large-`L` asymptotic and complex
general-branch clauses.

`OrdinaryPartialBell.lean` has two public definitions, `ordinarySeries` and
`ordinaryPartialBell`, and four public theorems:
`ordinaryPartialBell_pow`, `bellWeightSeries_eq_ordinarySeries`,
`factorial_mul_ordinaryPartialBell`, and
`ordinaryPartialBell_eq_zero_of_lt`.  It gives the ordinary generating-series
characterization, the exact factorial bridge to the exponential partial Bell
family, and the above-diagonal vanishing law over commutative rational
algebras.  This closes the generating-series and normalization-bridge content
of `plt:lem:bell-normalizations`.  The full printed lemma is still **Partial**:
the explicit multinomial-sum presentation and the final identification with
the manuscript's convolution polynomial are not separately formalized.  No
additional diagonal-boundary declaration is counted or advertised.

`PowerLogCoreInversion.lean` has three public definitions, `powerLogCore`,
`powerLogCoreArg`, and `powerLogCoreRoot`, and six public theorems:
`powerLogCore_exp`, `log_powerLogCoreRoot_sub`,
`powerLogCore_of_lambert`, `powerLogCore_powerLogCoreRoot`,
`hasDerivAt_powerLogCore`, and `hasDerivAt_powerLogCore_root`.  It makes the
real `r = 1` substitution, solve law, and slope identity of
`p6:eq:core-r1` **Exact**, including a branch-independent lemma for any real
solution of the Lambert equation and the principal-branch corollary.  The full
`p6:lem:core` remains **Partial** because general `r`, its root determination,
and a complex `W_k` reading are absent.

`RemainderTransport.lean` has no public definitions and exactly three public
theorems: `lipschitzOn_of_abs_deriv_le`, `transport_bound_mul`, and
`transport_bound`.  The derivative-to-Lipschitz bridge and both forms of
`p0:eq:transport-bound` are **Exact**.  The statements preserve the essential
asymmetry between a one-sided derivative floor for the core and a two-sided
derivative bound for the perturbation.  Part (2) of
`p0:thm:remainder-transport`, the first-order law with an explicit
second-order error, remains unformalized, so the whole two-part theorem is
**Partial**.

`StaircaseInversion.lean` has no public definitions and exactly seven public
theorems: `isLeast_ceil`, `staircase_ceil`, `staircase_separation`,
`staircase_separation_fails`, `staircase_round`,
`isLeast_residue_class`, and `exists_half_error_of_jump`.  These prove all
five order-theoretic recovery clauses of `p0:thm:staircase` under the exact
strict-monotonicity and inverse-value hypotheses used, including the
residue-class formula, the half-error obstruction at a jump, and an explicit
proof that the separation hypothesis is not removable.  Those recovery
clauses are **Exact**.  The analytic construction of admissible
interpolations and the Fourier expansion of the periodic layer remain
unformalized.

`TransseriesFlat.lean` has four public definitions: `IsFlat`,
`flatSubmodule`, `AbsorbsScale`, and `powScale`.  Its sixteen public theorems
are `isFlat_zero`, `IsFlat.add`, `IsFlat.neg`, `IsFlat.sub`,
`IsFlat.const_smul`, `mem_flatSubmodule_iff`,
`IsFlat.mul_absorbsScale`, `absorbsScale_const`,
`IsPoincareExpansion.add_isFlat`,
`isFlat_sub_of_isPoincareExpansion`,
`isPoincareExpansion_iff_isFlat_sub`,
`isPoincareExpansion_zero_iff`, `powScale_eq_rpow`,
`absorbsScale_of_isBigO_pow`, `isFlat_exp_neg`, and
`isPoincareExpansion_add_exp_neg`.  They make `q0:def:flat` and all three
clauses of `q0:prop:invisible` **Exact** for the abstract scale, with
invisibility sharpened to an iff.  The concrete power-scale theorems prove
that fixed polynomial growth is an `AbsorbsScale` multiplier and that
`exp (-x)` is flat; no informal closure assumption is silently substituted.

`TransseriesHarmonicIncrement.lean` has no public definitions and exactly two
public theorems: `tendsto_div_atTop_of_tendsto_sub` and
`tendsto_div_atTop_of_harmonic_increment`.  They make the generic
Stolz--Cesàro step and the leading conclusion `w_n / n → c₀` **Exact**.
The larger `plt:lem:mot-harmonic` remains **Partial**: its logarithmic
correction, limiting constant, and final `o(1)` remainder are not formalized.

`WrightOmega.lean` has one public definition, `wrightOmega`, and thirteen
public theorems: `analyticAt_wrightOmega`, `wrightOmega_pos`, `wrightOmega_add_log`,
`principalLambertW_eq_wrightOmega_log`, `wrightOmega_leftInverse`,
`wrightOmega_strictMono`, `wrightOmega_one`, `one_le_wrightOmega`,
`wrightOmega_le_self`, `sub_log_le_wrightOmega`, `wrightOmega_envelope`,
`add_one_div_two_le_wrightOmega`, and `tendsto_wrightOmega_atTop`.  These make
the defining equation, inverse law, positivity, monotonicity, anchor,
Lambert relation, envelope, and divergence clauses of
`plt:prop:mot-omega-basic` **Exact** over the reals.  Its analyticity clause is
the pointwise statement `AnalyticAt ℝ wrightOmega X` for every real `X`; no
complex branch or complex-holomorphic Wright-omega claim is made.

Finally, the four declarations added to `TransseriesDifferentialBlock.lean`
are exactly `derivation_val_inv`, `derivation_pow_inv`,
`derivation_zpow_t`, and `derivation_block_zpow`.  Together with the five
previously inventoried natural-exponent theorems, they make the displayed
integer block law `plt:eq:mot-block-derivative` **Exact** whenever `t` is
represented by a unit.  They do not construct the concrete Laurent ambient
ring, and the module's primitive-existence results remain natural-exponent
statements; the larger `plt:prop:dif-block` therefore remains **Partial**.

The one-definition/eight-theorem
`RvachevSuperconvergentSynthesis.lean` leaf contributes
`IsRvachevSuperconvergentPhase`,
`isRvachevSuperconvergentPhase_two_pow_iff`,
`tsum_quarter_monomial_eq_integral_of_even_deg`,
`tsum_three_quarters_monomial_eq_integral_of_even_deg`,
`tsum_shifted_monomial_eq_integral_superconvergent`,
`tsum_shifted_polynomial_eq_integral_superconvergent`,
`integral_polynomial_mul_rvachevUp_eq_normalized_tsum_superconvergent`,
`normalized_tsum_shifted_rvachevDeconvolvedPolynomial_mul_rvachevUp_superconvergent`,
and
`normalized_tsum_shifted_rvachevAppellPolynomial_mul_rvachevUp_superconvergent`.
It proves the stronger arbitrary-nonzero-`M` degree-`v₂(M)+1` result at the
selected exact phase representatives; it does not classify phases modulo
integers or prove maximality, positivity, or rationality.  The prime-power and
outer-product tranches
account for one module and six declarations: the zero-definition/three-theorem
`GeometricPochhammerNormalConvergence.lean` leaf and three additional theorems
in `PrimePowerBinomialValuation.lean`.  The q-polish adds two theorems to
`QPochhammerInfinite.lean`, the three-module effective-inverse union
contributes seventeen declarations, the first six q-calculus modules contribute
36 declarations, and four later leaves originally contributed 38 declarations
and now expose 40 after the two Gaussian additions.
Those leaves are `GaussianBinomialPalindromic.lean` 0+14,
`JacksonIntegral.lean` 1+7, `QExponential.lean` 3+8, and
`ThetaQuasiPeriodicity.lean` 1+6: five definitions and thirty-five theorems.
Four still newer q-series leaves contribute twenty theorems and no definitions:
`GaussianBinomialPolynomialStructure.lean` 0+5, `JacobiCubic.lean` 0+2,
`QPochhammerLogDerivative.lean` 0+10, and
`QPochhammerOrderDerivative.lean` 0+3.
The two newest algebra leaves add thirteen theorems and no definitions:
`CentralQBinomialReduction.lean` 0+6 and
`CyclotomicFactorization.lean` 0+7.
The two added Gaussian linear-coefficient theorems and the eight-declaration
`EffectiveGapInverse.lean` leaf account for ten declarations and
one module.
The finite-q tranche adds four modules and 25 declarations:
`PrimitiveRootBlock.lean` 0+3, `QLucas.lean` 0+7,
`CyclotomicDivisibility.lean` 0+3, and `QCatalan.lean` 1+11.  They add the carry criterion,
primitive-root block formula, q-Lucas theorem, and integral q-Catalan API.
The interpolation/q-beta pair now contributes four definitions and twenty-seven theorems:
`QBetaIntegral.lean` 1+8 and `NewtonInterpolation.lean` 3+19.  The former
evaluates the Jackson q-beta integral as both an infinite-product quotient and
a q-gamma quotient, with positivity, symmetry, and successor recurrences; the
latter supplies triangular Newton coefficients and the node-qualified polynomial,
interpolation and uniqueness, divided differences, the geometric-grid specialization,
and seven compatibility declarations for the `newtonInterpolant` family.
The integer/complex-upper and q-Pfaff--Saalschuetz modules contribute two definitions and eighteen theorems:
`GaussianBinomialInteger.lean` 1+10,
`GaussianBinomialComplexOrder.lean` 1+5, and
`QPfaffSaalschutz.lean` 0+3.  They extend Gaussian coefficients to integer
and principal-branch complex upper parameters, derive the associated finite
and reciprocal q-binomial series, and prove the terminating balanced
q-Pfaff--Saalschuetz summation over a field.  Their nonzero-nome,
strict-contraction, and finite-product nonvanishing hypotheses remain explicit.
`QuantumMultinomial.lean` has no definitions and exactly five
theorems.  It decomposes natural tuple antidiagonals, transports Gaussian
symmetry to arbitrary semirings, proves q-multinomial coefficient commutation,
and establishes the ordered noncommutative q-multinomial expansion from the
displayed pairwise q-commutation laws.  The API is finite and division-free.
`GaussianBinomialBounds.lean` has no definitions and exactly
six theorems: `gaussianBinomial_inv`, `one_le_gaussianBinomial`,
`finiteQPochhammerIn_pow_le_one`,
`gaussianBinomial_le_inv_qPochhammerInfIn`,
`pow_le_gaussianBinomial_of_one_lt`, and
`gaussianBinomial_le_pow_div_of_one_lt`.  They give evaluated field
reciprocity, the nonnegative strict-contraction bounds, and the resulting
dimension-dominant real bounds for `Q > 1`, with `k ≤ n` and all nonzero and
order hypotheses explicit.  The module reuses the stronger ordered-field
`finiteQPochhammerIn_self_pos` theorem from `GeneralQConditionNumber.lean`
rather than exporting a duplicate.
The older 622/8,472, 623/8,476, 629/8,546, 630/8,552,
641/8,650, and 643/8,661 values below are historical checkpoints, not
descriptions of the live tree.  The earlier additions and q-series tranches are
itemized below.  The branch-point geometry and
asymptotics leaves contribute 17 declarations for the one-sided vertical
tangents and leading signed square-root laws of both real Lambert branches.
The two Legendre--Gaunt modules contribute 25: four definitions and twelve
theorems in `LegendreGaunt.lean`, and one definition and eight theorems in
`FabiusLegendreGaunt.lean`.  They add the executable rational triple-product
and finite product-linearization core, then specialize it to full and even
Rvachev coefficient sums for rational and real Legendre Gram entries.  The
remaining twenty declarations are three generalized spectral q-Pochhammer
APIs, four density-diagnostic theorems, the locally uniform real-frequency
phase-prefix theorem and its compact-set uniform corollary in
`GeometricSincCharacteristicFunction.lean`, and eleven inverse-modulus
strictness and equality refinements.  `GeometricUniformMultisection.lean`
contributes two coordinate definitions and three fixed half/quarter
multisection theorems.  `GaussianBinomialAtNegOneDerivative.lean` supplies four
declarations: two first-derivative formulas at `q = -1` and two simple-root
multiplicity theorems.  Three signed-power moment theorems in
`RvachevDerivativeDistribution.lean` give the exact Boolean-cube formula and
its even-moment and positive-order odd-moment corollaries.  The same module's
two additional positive-order signed-distribution theorems give the sharply
normalized half-mixture law under exactly `0<n`:
`intervalIntegral_comp_normalized_iteratedDeriv_rvachev` is the continuous-test
half-mixture into any real Banach space, and
`map_normalized_iteratedDeriv_rvachev_restrict_Icc` is the corresponding Borel
pushforward identity for Lebesgue measure restricted to the closed interval
`[-1,1]`.  Order zero instead has the unsymmetrized original `rvachevUp` law.
The remaining declaration is the all-depth
`generalizedRvachevProduct_two_pow_mul` shift--refinement theorem in
`WeightLinearityProducts.lean`.  The final nine declarations are the two
definitions and seven theorems of `LagrangeRvachevSynthesis.lean`: the generic
finite-node decoder and atom coefficient, degree bounds, cardinal synthesis,
componentwise biorthogonality, linear coefficient identity, exact finite
interpolation loop, and unit row mass.  This inventory claim does not extend to
a geometric Gaussian closed-form decoder, a matrix wrapper, or an
optimal/minimum-variation decoder theorem.

The subsequent `LagrangeRvachevMatrix.lean` leaf is exhaustively 4+6.  Its
definitions and abbreviation are `rvachevAtomIndexSet`, `RvachevAtomIndex`,
`lagrangeRvachevEncoderMatrix`, and `lagrangeRvachevDecoderMatrix`; its
theorems are `lagrangeRvachevEncoderMatrix_nonneg`,
`sum_lagrangeRvachevEncoderMatrix_row_eq_one`,
`sum_lagrangeRvachevDecoderMatrix_row_eq_one`,
`lagrangeRvachevEncoderMatrix_mul_decoderMatrix`,
`exists_neg_entry_of_rightInverse_of_row_overlap`, and
`exists_lagrangeRvachevDecoderMatrix_entry_neg_of_row_overlap`.  It packages
the exact lattice block `Ioo (-(2*M)) (2*M)`, the normalized nonnegative
encoder and row-unital decoder, and the right-inverse equation under exactly
distinct in-range nodes, `M ≠ 0`, and `s.card - 1 ≤ padicValNat 2 M`.  The
generic sign theorem needs only encoder nonnegativity, decoder row unitality,
the right-inverse equation, and one strictly positive column in two distinct
rows; its Rvachev specialization remains conditional on that overlap.  It
asserts no `decoder * encoder` projector range/kernel, rank, trace,
characteristic-polynomial, Cauchy--Binet, geometric closed-form, or decoder
optimality result.

Two further declarations close the barycenter layer:
`ProbabilityRepresentation.integral_id_weightedUniformDistribution` gives
`(1 / 2) • ∑' n, w n` for norm-summable weights in every complete Borel real
normed space without sign, order, or termwise-integration hypotheses, and
`ProbabilityRepresentation.integral_id_geometricUniformDistribution_eq_one_half`
specializes it to mean `1 / 2` under exactly `|q| < 1`, including `q = 0` and
negative `q`.  Accordingly `GeometricUniformLaw.lean` now has 24 public
declarations.  The subsequent
`integral_polynomial_mul_rvachevUp_eq_dyadic_tsum` theorem in
`PolynomialCombExactness.lean` packages the polynomial-times-Rvachev integral
as the corresponding dyadic shifted-polynomial sum and contributes one further
declaration.  The subsequent centered Appell/deconvolution and arbitrary-phase
polynomial-reproduction tranche contributes four declarations: three in
`RvachevMomentAppell.lean` and one in `RvachevPolynomialSynthesis.lean`.
The new `QPochhammerEntire.lean` leaf retains five compatibility theorems:
locally uniform convergence of the defining products for every strict complex
contraction, complex differentiability in the free parameter, the exact
factor-zero classification (including the `q = 0` boundary), its reciprocal-
power spelling for a nonzero nome, and simple zeros expressed as analytic order
one.  Together with the branch-only four-theorem
Gaussian `q = -1` first-jet leaf, both q-series modules remain facade-reachable.
The two subsequent general q-Pochhammer modules contribute thirty-two further
declarations.  `QPochhammerDissection.lean` adds two finite residue-class
dissection theorems over an arbitrary commutative ring: the exact-multiple form
is total in `r`, and the remainder form assumes exactly `u <= r`.
`QPochhammerInfinite.lean` adds the general infinite symbol and twenty-nine
theorems covering summability and convergence for a strict norm contraction,
finite-prefix and residue-class factorizations, exact factor-zero criteria,
locally uniform parameter convergence and continuity, complex entirety,
explicit derivatives at factor zeros, derivative nonvanishing at every raw
factor zero, analytic order one at every zero, and nonvanishing of the
displayed derivative coefficient at every inverse-power zero for a nonzero nome.  Its
algebraic cofactor
identity needs only a field and a nonzero nome; its infinite dissection assumes
exactly `0 < r`, `[NormedCommRing R] [NormOneClass R] [CompleteSpace R]`, and
the strict contraction.  These are regularity statements in the free parameter
`a`, not a joint analyticity or continuation theorem in the nome `q`.

The subsequent `GeneralizedRvachevIdentifiability.lean` leaf contributes no
definitions and exactly six theorems:
`weightSequence_eq_of_weightedScaleMultiplicity_base_pow_eq`,
`analyticOrderAt_generalizedRvachevProduct_two_pow`,
`exponent_zero_eq_toNat_analyticOrderAt_generalizedRvachevProduct`,
`exponent_succ_eq_toNat_analyticOrderAt_generalizedRvachevProduct`,
`exponentSequence_eq_of_analyticOrderAt_two_pow_eq`, and
`generalizedRvachevProduct_eq_iff`.  They recover an exponent sequence from
weighted multiplicities at base powers or, under the exact summability
hypotheses, from analytic orders at `1, 2, 4, ...`, and make equality of two
admissible entire products equivalent to equality of their exponent
sequences.  The input is the multiplicity/order divisor: a bare zero set or
the product values at its zero points does not distinguish, for example, a
sequence from its double.  Spectral-zeta, cumulant-sample, and generalized
probability-law identifiability are not included.
The merged q-series leaves are inventoried below from the live source tree;
those counts supersede the intermediate pre-union q-series subtotal.
The valuation tranche's new leaf
`PrimePowerBinomialValuation.lean` contributes no definitions and exactly six
theorems.  `primePowerChoose_padicValNat_add` and
`primePowerChoose_padicValNat` are the additive and subtraction forms for row
`p^m`, including the positive right endpoint and `m=0`.
`primePowerSubOneChoose_padicValNat` says every column `j<p^m` in row
`p^m-1` is a `p`-adic unit, while
`primePowerSubTwoChoose_padicValNat` proves
`v_p(C(p^m-2,j-1))=v_p(j)` for exactly `0<j<p^m`.
`twoPowChoose_padicValNat` and `twoPowSubTwoChoose_padicValNat` are the two
strict-interior dyadic-comb wrappers.  The upper companion boundary is
necessarily excluded because at `j=p^m` the binomial coefficient is zero.
The compatibility leaf, `QPochhammerEntire.lean`, contributes no definitions
and retains exactly five theorems:
`hasProdLocallyUniformly_complexQPochhammerInf`,
`complexQPochhammerInf_differentiable`,
`complexQPochhammerInf_eq_zero_iff`,
`complexQPochhammerInf_eq_zero_iff_eq_inv_pow`, and
`analyticOrderAt_complexQPochhammerInf_of_eq_zero`.  For each fixed complex
strict contraction `q`, they give locally uniform convergence on the whole
complex `a`-plane, entireness in `a`, the raw factor-zero locus (including
`q = 0`), its reciprocal-power spelling under `q ≠ 0`, and analytic order one
at every zero.  They assert neither joint holomorphy in `q` nor a global
growth/order/type claim.  Outer spectral-product local uniformity belongs to
the separate three-theorem module recorded below.
`GeometricPochhammerNormalConvergence.lean` contributes no definitions and
exactly three theorems:
`hasProdLocallyUniformly_geometricSincProduct_complexQPochhammerInf`,
`hasProdLocallyUniformly_rvachevFourierProduct_complexQPochhammerInf`, and
`hasProdLocallyUniformly_rvachevFourier_complexQPochhammerInf`.  For every
complex `q` satisfying exactly `‖q‖<1`, including `q=0`, the first gives the
locally uniform outer product on the whole complex `z`-plane with limit
`geometricSincProduct q`; the other two are the nome-`1/4` Rvachev-product and
bounded-Fabius specializations.  This promotes only the locally-uniform/normal-
convergence clause.  The compound `qF` spectral theorem remains partial:
centered characteristic-function/MGF packaging, the outside-disk reciprocal
formula, the pole divisor, and the zero--pole exchange remain absent.
The two subsequent q-Pochhammer leaves contribute thirty-two declarations.
`QPochhammerDissection.lean` has no definitions and exactly two theorems,
`finiteQPochhammerIn_dissection` and
`finiteQPochhammerIn_dissection_remainder`; both are finite identities over
every commutative ring, with the remainder theorem assuming exactly `u ≤ r`.
`QPochhammerInfinite.lean` has one definition, `qPochhammerInfIn`, and exactly
twenty-nine theorems:
`qPochhammerInfIn_eq_tprod`, `summable_norm_mul_pow`,
`one_sub_ne_zero_of_norm_lt_one`, `norm_mul_pow_self_lt_one`,
`finiteQPochhammerIn_self_ne_zero`,
`multipliable_one_sub_mul_pow_of_norm_lt_one`,
`hasProd_qPochhammerInfIn`,
`tendsto_finiteQPochhammerIn_qPochhammerInfIn`,
`qPochhammerInfIn_eq_finite_mul_shift`, `qPochhammerInfIn_succ_shift`,
`qPochhammerInfIn_eq_factor_mul`, `qPochhammerInfIn_dissection`,
`qPochhammerInfIn_ne_zero`, `qPochhammerInfIn_eq_zero_iff`,
`qPochhammerInfIn_self_ne_zero`, `qPochhammerInfIn_eq_tprod_smul`,
`summable_norm_pow_of_norm_lt_one`, `isBigO_one_sub_sub_one`,
`differentiable_finiteQPochhammerIn`,
`qPochhammerInfIn_eq_zero_iff_exists_inv_pow`,
`hasProdLocallyUniformly_qPochhammerInfIn`,
`continuous_qPochhammerInfIn`,
`pow_sq_mul_finiteQPochhammerIn_inv_pow_self`,
`differentiable_qPochhammerInfIn`,
`hasDerivAt_qPochhammerInfIn_of_mul_pow_eq_one`,
`hasDerivAt_qPochhammerInfIn_inv_pow`,
`deriv_qPochhammerInfIn_inv_pow_ne_zero`,
`deriv_qPochhammerInfIn_ne_zero_of_mul_pow_eq_one`, and
`analyticOrderAt_qPochhammerInfIn_of_eq_zero`.  These stratify the total
topological-ring definition, strict-contraction complete-normed-ring
product/shift/dissection and multiplicative-norm zero API, complete-field
inverse-power zeros, locally compact field local uniformity and continuity,
and complex entire, nonzero-derivative, and analytic-order-one formulas,
including the raw-factor statements at `q=0`.  They make no joint-nome
holomorphy or global asymptotic claim; the separate five-theorem
`QPochhammerEntire.lean` API retains the compatibility names for
`complexQPochhammerInf`, adds the nonzero-nome reciprocal-power spelling, and
includes analytic order one at `q=0`; no public equality bridge between the
two product definitions is counted.
The final incoming seven-module increment consists of the four-theorem
`GaussianBinomialAtNegOneDerivative.lean` leaf described above and six further
q-series modules contributing exactly sixty-nine declarations.
`QBinomialTheoremInfinite.lean` contributes one definition and twenty-two
theorems: real comparison products and Gaussian majorants, fixed-column
convergence, Tannery transfer, Euler's product and reciprocal expansions, and
the infinite q-binomial theorem over complete normed fields under the stated
strict nome and series-variable contractions.  The reused theorem
`finiteQPochhammerIn_zero_left` remains canonically owned by
`GaussianBinomialAtOne.lean` and is not counted in this module.
`JacobiTripleProduct.lean`
contributes two definitions and twenty-five theorems: the exact finite
polynomial identity over commutative rings, its Laurent field form, the
complete-normed-field Jacobi sums for nonzero Laurent variable and strict
nome, and Euler's pentagonal specialization.  `QPascalSummation.lean` adds
four theorems for the two finite q-Pascal row splittings and Gaussian
coefficient commutation; `GaussianBinomialContinuity.lean` adds three for
topological-semiring continuity, the limit at one, and the field quotient
form with its nonzero denominator; and `QuantumBinomial.lean` adds the two
noncommutative-semiring quantum-plane identities under exactly the displayed
commutation hypotheses.  Finally, `RogersSzegoPolynomial.lean` contributes
one definition and nine theorems: finite commutative-(semi)ring boundary and
recurrence laws, plus the complete-normed-field generating series under
`‖q‖ < 1`, `‖t‖ < 1`, and `‖z*t‖ < 1`.  These six module counts sum to
69, and with the four q=-1 derivative declarations give the deduplicated
73-name incoming increment.  The two subsequent
`QPochhammerInfinite.lean` theorems brought that historical feature snapshot
from 622/8,472 to 629/8,547, a seven-module/75-declaration change.  The two
inverse-computability modules then brought that feature snapshot to 631/8,556,
a nine-module/84-declaration change.  The six further incoming q-calculus
leaves contribute 36 declarations and brought the intermediate audit to
649/8,697.  The four subsequent leaves contribute 38 declarations and bring
that audit to 653/8,735.  The next four leaves contribute twenty declarations
and bring that audit to 657/8,755.  The final two algebra leaves contribute
thirteen declarations and brought the audit to 659/8,768.  Two Gaussian
linear-coefficient theorems then brought it to 659/8,770, and the
eight-declaration `EffectiveGapInverse.lean` leaf brought the audit to
660/8,778.  The superconvergent synthesis leaf adds one module and nine
declarations, yielding 661/8,787.  The four root-of-unity/q-Catalan modules
add twenty-six declarations, yielding 665/8,813.  The original Jackson
q-beta/Newton pair adds twenty-four declarations, yielding 667/8,837; the
integer/complex upper Gaussian and q-Pfaff--Saalschuetz leaves add twenty,
yielding 670/8,857; and the noncommutative q-multinomial leaf adds five,
yielding 671/8,862.  `GaussianBinomialBounds.lean` adds six theorems,
yielding 672/8,868, and the seven collision-free Newton compatibility names
yield the intermediate 672/8,875 census.  The 5+14
`BinaryWordInversions.lean`, 2+8 `BoxPartitions.lean`, and 0+5
`TelescopingCertificate.lean` leaves then add three modules and thirty-four
declarations, yielding that historical 675/8,909 census.

`GaussianBinomialPalindromic.lean` is an exhaustive zero-definition,
fourteen-theorem leaf: `Fabius.reflect_add_of_natDegree_le`,
`Fabius.reflect_one'`, `Fabius.gaussianBinomial_natDegree_le`,
`Fabius.gaussianBinomial_zero_left`, `Fabius.gaussianBinomial_diag'`,
`Fabius.reflect_gaussianBinomial`,
`Fabius.coeff_gaussianBinomial_reflect`,
`Fabius.coeff_gaussianBinomial_zero`,
`Fabius.coeff_gaussianBinomial_top`, `Fabius.gaussianBinomial_natDegree`,
`Fabius.gaussianBinomial_monic`,
`Fabius.two_mul_derivative_gaussianBinomial_eval_one`,
`Fabius.coeff_gaussianBinomial_one_of_pos_of_lt`, and
`Fabius.coeff_gaussianBinomial_one`.  Over every
commutative semiring it supplies generic reflection helpers, the Gaussian
degree bound, zero and diagonal values, exact reflection in degree `k*(n-k)`,
constant and top coefficients one, bounded-index coefficient symmetry, and
the division-free derivative-at-one mean identity.  The interior linear
coefficient is one under exactly `0 < k` and `k < n`; the total classifier is
`if 0 < k ∧ k < n then 1 else 0`, so the boundary cases `k = 0`, `k = n`,
and `n < k` are explicit.  Both coefficient theorems hold over every
commutative semiring; exact degree and monicity alone require nontriviality.

That increment is exhaustively counted as
`QPochhammerInfiniteBounds.lean` 0+5, `HeineTransformation.lean` 2+5,
`QGaussSummation.lean` 0+2, `QPochhammerComplexOrder.lean` 1+4,
`BasicHypergeometricSeries.lean` 2+5, and `QMultinomial.lean` 1+9: six
definitions and thirty theorems.  It adds finite-prefix bounds, the Heine and
q-Gauss identities, a ratio-defined complex-order q-Pochhammer API, general
basic-hypergeometric terms and summability, and the division-free recursive
q-multinomial interface.  The displayed contraction, nonvanishing, and
denominator hypotheses remain part of these APIs.
The four-module increment is now exhaustively counted as
`GaussianBinomialPalindromic.lean` 0+14, `JacksonIntegral.lean` 1+7,
`QExponential.lean` 3+8, and `ThetaQuasiPeriodicity.lean` 1+6.  It adds the
degree, monicity, coefficient-reversal, division-free mean theory, and total
linear-coefficient classifier of the
Gaussian polynomial; q-exponentials and their q-derivative laws; Jackson's
fundamental theorem and integration by parts; and the bilateral theta product,
quasi-periodicity, and zero criterion.  Their analytic declarations keep the
displayed strict-contraction, nonzero-variable, convergence, and nonvanishing
hypotheses.

The still newer four-module increment is exhaustively counted as
`GaussianBinomialPolynomialStructure.lean` 0+5, `JacobiCubic.lean` 0+2,
`QPochhammerLogDerivative.lean` 0+10, and
`QPochhammerOrderDerivative.lean` 0+3.  Its twenty theorems add universal
Gaussian polynomial structure over `ℕ[X]`, Jacobi's cubic identity, the
q-Pochhammer logarithmic derivative and Lambert-series form on the unit disc,
and the derivative with respect to complex order.  The strict-contraction,
unit-disc, nonzero-nome, and shifted-argument hypotheses remain explicit.

The final two-module increment is exhaustively counted as
`CentralQBinomialReduction.lean` 0+6 and
`CyclotomicFactorization.lean` 0+7.  It adds finite q-Pochhammer sign pairing,
even--odd dissection and ring-hom naturality; the division-free central
Gaussian reduction and its conditional quotient form; and the cyclotomic
factorizations of `(X;X)_n` and `[n,k]_X`.  The quotient theorem retains both
nonzero-denominator hypotheses, and the Gaussian cyclotomic factorization
retains its integral-domain assumption.

The source-only q-algebra increment adds `CentralQBinomialReduction.lean`
0+6: `finiteQPochhammerIn_mul_neg`, `finiteQPochhammerIn_two_mul`,
`finiteQPochhammerIn_map_ringHom`, `central_gaussianBinomial_sq_mul_int`,
`central_gaussianBinomial_sq_mul`, and `central_gaussianBinomial_sq_div`;
and `CyclotomicFactorization.lean` 0+7: `div_add_div_le_div`,
`div_le_div_add_div_add_one`, `mem_range_and_mem_divisors_iff`,
`finiteQPochhammerIn_X_eq_prod_cyclotomic`,
`finiteQPochhammerIn_X_eq_gaussianBinomial_mul`,
`prod_cyclotomic_pow_div_extend`, and
`gaussianBinomial_X_eq_prod_cyclotomic`.  The first module gives the
division-free central squared-base reduction over commutative rings and a
field quotient under two nonvanishing hypotheses.  The second gives the
finite-product cyclotomic factorization over commutative rings and the final
Gaussian factorization over an integral domain.

The latest finite-q tranche is exhaustive.  `PrimitiveRootBlock.lean` is
0+3: `Fabius.gaussianBinomial_isPrimitiveRoot_eq_zero`,
`Fabius.neg_one_pow_mul_pow_choose_two`, and
`Fabius.finiteQPochhammerIn_isPrimitiveRoot`.  In a commutative integral
domain, a primitive `d`-th root `ζ` kills `[d,k]_ζ` for `0 < k < d`; for
`0 < d`, the top phase is `(-1)^d * ζ^(choose d 2) = -1` and the complete
block is `(y;ζ)_d = 1-y^d`.

`QLucas.lean` is 0+7: `Fabius.add_mul_add_sub_one`, `Fabius.choose_two_add`,
`Fabius.coeff_finiteQPochhammerIn_neg_X`,
`Fabius.finiteQPochhammerIn_neg_X_block`, `Fabius.coeff_block_pow_mul`,
`Fabius.pow_choose_two_add_mul_eq`, and
`Fabius.gaussianBinomial_q_lucas`.  The first two are natural-number
quadratic identities.  The coefficient, block, and phase lemmas prove
`[a*d+b,r*d+s]_ζ = choose(a,r) * [b,s]_ζ` when `0 < d`, `ζ` is a primitive
`d`-th root in a commutative integral domain, and `b,s < d`.  Its local
`two_mul_choose_two` helper is private; the unique public theorem of that name
belongs to `QChuVandermonde.lean`.

`JacobiTwoSquareCount.lean` is 0+4:
`Fabius.sumSqRep_two_eq_four_mul_twoSquareDivisorSum`,
`Fabius.sumSqRep_two_eq_four_mul_prod`,
`Fabius.theta_sq_eq_chi4_lambert`, and
`Fabius.theta_sq_eq_odd_lambert`.  It closes the nonzero two-square count and
instantiates both parameterized Lambert kernels from `TwoSquareTheorem.lean`.
The product theorem retains the even-valuation condition at every prime
divisor congruent to three modulo four; both Lambert identities are
unconditional over a complete normed field under `‖q‖ < 1`.

`CyclotomicDivisibility.lean` is 0+3:
`Fabius.cyclotomic_exponent_eq_one_iff`,
`Fabius.cyclotomic_dvd_gaussianBinomial_iff`, and
`Fabius.gaussianBinomial_mul_isPrimitiveRoot`.  For `k ≤ n` and `0 < d`, the
Gaussian cyclotomic exponent equals one exactly when `n % d < k % d`; over
`ℚ[X]` that is exactly the criterion for `Φ_d` to divide `[n,k]_X`.  In a
commutative integral domain, a primitive `n`-th root with `0 < n` gives
`[a*n,b*n]_ζ = choose(a,b)`.

`QCatalan.lean` is 1+11.  Its definition is `Fabius.qCatalan`; its theorems
are `Fabius.map_qInt`, `Fabius.qInt_X_monic`, `Fabius.qInt_X_natDegree`,
`Fabius.X_sub_one_mul_qInt`, `Fabius.qInt_X_eq_prod_cyclotomic`,
`Fabius.qInt_X_dvd_gaussianBinomial_rat`,
`Fabius.qInt_X_dvd_gaussianBinomial_int`,
`Fabius.qInt_X_mul_qCatalan`, `Fabius.qCatalan_natDegree`,
`Fabius.qCatalan_eval_one_mul`, and `Fabius.qCatalan_eval_one`.  Semiring
naturality and the commutative-ring q-integer identities yield
`[n+1]_X ∣ [2*n,n]_X` over `ℚ[X]` and `ℤ[X]`; the integral quotient has degree
`n*(n-1)`, satisfies `(n+1) C_n(1) = choose(2*n,n)`, and evaluates to the
ordinary Catalan number.

`NewtonInterpolation.lean` is 3+19.  Its definitions are
`Fabius.newtonCoeff`, `Fabius.nodeNewtonPoly`, and the compatibility alias
`Fabius.newtonInterpolant`; its theorems are
`Fabius.newtonCoeff_eq`, `Fabius.newtonCoeff_zero`,
`Fabius.newtonCoeff_mul_prod`, `Fabius.nodeNewtonPoly_succ`,
`Fabius.eval_nodeNewtonPoly`, `Fabius.degree_nodeNewtonPoly_lt`,
`Fabius.nodeNewtonPoly_eq_interpolate`,
`Fabius.eq_nodeNewtonPoly_of_eval_eq`,
`Fabius.coeff_nodeNewtonPoly_self`, `Fabius.newtonCoeff_eq_sum`,
`Fabius.nodal_range_pow`, `Fabius.prod_erase_pow_sub_pow`, and
`Fabius.newtonCoeff_pow_eq_sum`, together with compatibility forms
`Fabius.newtonPoly_succ`, `Fabius.eval_newtonPoly`,
`Fabius.degree_newtonPoly_lt`, `Fabius.newtonPoly_eq_interpolate`,
`Fabius.eq_newtonPoly_of_eval_eq`, and `Fabius.coeff_newtonPoly_self`.
Over a field these give triangular Newton
reconstruction, finite-node interpolation and uniqueness, divided differences,
and the geometric-power-node specialization, retaining each finite-node
injectivity, nonzero-product, `q ≠ 0`, and index hypothesis.  The node-qualified
family remains collision-free with `NewtonBasisGeneratingFunction.newtonPoly`;
the compatibility family is definitionally identical.

`QBetaIntegral.lean` is 1+8.  Its definition is `Fabius.qBeta`; its theorems
are `Fabius.qNumber_pos`, `Fabius.qBeta_term_eq`, `Fabius.qBeta_eq_prod`,
`Fabius.qBeta_eq_qGamma`, `Fabius.qBeta_comm`, `Fabius.qBeta_pos`,
`Fabius.qBeta_add_one_left`, and `Fabius.qBeta_add_one_right`.  Under
`0 < q < 1` and the displayed positive real arguments, they evaluate the
Jackson q-beta integral as an infinite-product and q-Gamma quotient and prove
symmetry, positivity, and both recurrences.

`GaussianBinomialBounds.lean` is 0+6.  Its exhaustive theorem surface is
`Fabius.gaussianBinomial_inv`, `Fabius.one_le_gaussianBinomial`,
`Fabius.finiteQPochhammerIn_pow_le_one`,
`Fabius.gaussianBinomial_le_inv_qPochhammerInfIn`,
`Fabius.pow_le_gaussianBinomial_of_one_lt`, and
`Fabius.gaussianBinomial_le_pow_div_of_one_lt`.  It evaluates Gaussian
palindromicity as field reciprocity, bounds coefficients uniformly for
`0 ≤ q < 1`, and transfers those bounds to the dimension-dominant regime
`Q > 1`; every nonzero-base, index, and order hypothesis remains explicit.
The proof reuses the stronger generic `Fabius.finiteQPochhammerIn_self_pos`
from `GeneralQConditionNumber.lean` rather than exporting a duplicate.

`EffectiveMonotoneInverse.lean` has exactly two public definitions,
`Fabius.SequentiallyComputableOn` and `Fabius.unitClamp`, and exactly six
public theorems: `Fabius.unitClamp_sequentiallyComputable`,
`Fabius.tolerantDifference_error`, `Fabius.tolerantDifference_safe_updates`,
`Fabius.tolerantDifference_inconclusive`,
`Fabius.tolerantBisection_correct`, and
`Fabius.effectiveInversionOn_Icc`.  Its natural-number controller performs
exactly `p` dyadic halvings at requested precision `p`; certified signed-code
comparisons update the bracket, while the third, inconclusive branch certifies
the current midpoint.  Doubling an accepted numerator through remaining
depths and using the final left endpoint in the no-hit case yield a uniform
dyadic name at denominator `2^p` with error at most `2^-p`.  The abstract Lean
theorem consumes a computable positive reciprocal inverse modulus.  The
adjacent `EffectiveGapInverse.lean` module constructs one from computable
positive rational dyadic-gap lower bounds and also derives effective uniform
continuity.

`EffectiveGapInverse.lean` has exactly eight public declarations:
`Fabius.EffectivelyUniformContinuousOn`, the structure
`Fabius.ComputablePositiveRationalSequence`,
`Fabius.ComputablePositiveRationalSequence.value`,
`Fabius.ComputablePositiveRationalSequence.reciprocalDenominator`,
`Fabius.ComputablePositiveRationalSequence.reciprocalDenominator_spec`,
`Fabius.inverseModulus_of_positiveRationalGap`,
`Fabius.effectiveInversionOn_Icc_of_computablePositiveRationalGap`, and
`Fabius.clampedEffectiveInversion_of_computablePositiveRationalGap`.  The
structure packages computable positive natural numerators and denominators.
Its reciprocal denominator is `denominator p / numerator p + 1`, whose
reciprocal lies strictly below the represented rational value.  For a strict
increasing inverse pair on `[0,1]`, the hypothesis is the uniform dyadic-gap
lower bound `α.value p ≤ f (x + 2^-p) - f x` for every
`x ∈ [0,1-2^-p]`.  With a computable dyadic oracle for `f` and interval maps
for both functions, the module proves sequential computability and effective
uniform continuity of `g` on `[0,1]`.  Its total computable-real-function
conclusion is exactly `fun x => g (unitClamp x)`: it agrees with `g` on the
unit interval but asserts nothing about the unclamped values of `g` outside it.

`FabiusInverseComputable.lean` has zero public definitions and exactly one
public theorem, `Fabius.fabiusInv_isComputableRealFunction`.  It instantiates
the generic realizer with the centered-spline dyadic oracle for `fabiusReal`
and `inverseFabiusDeltaDenominator`, clamps arbitrary input names without
changing the totalized inverse, and combines total sequential computability
with the logarithmic-Delta effective-uniform-continuity witness.  This closes
the total inverse computability certificate without asserting a practical
running-time or input-bit complexity bound.

The closed-form Gaunt leaf `LegendreGauntClosedForm.lean` contributes two definitions and
twenty-five theorems: the total integer zero-row Wigner-square datum, its exact
central-binomial and factorial forms, the all-degree Gaunt identification,
sharp support, positivity and vanishing criteria, and the product-linearization
coefficient bridge.  It makes no signed-symbol, phase, half-integer,
nonzero-magnetic-index, or general Wigner recoupling claim.  The baseline
also includes the three finite rational-entry, rational-matrix, and real-matrix
Wigner-square sum corollaries in `FabiusLegendreGauntClosedForm.lean`.  These
two new leaves therefore contribute thirty declarations in total.  The
two definitions are `legendreGauntAdmissible` and
`legendreWignerThreeJZeroSqRat`.  In source order, the twenty-five core theorem
names are `legendreGauntAdmissible_iff_exists_pairwise_add`,
`legendreGauntAdmissible_pairwise_add`,
`legendreWignerThreeJZeroSqRat_pairwise_add`,
`legendreWignerThreeJZeroSqRat_pairwise_add_factorial`,
`legendreWignerThreeJZeroSqRat_eq_factorial_of_halfSum`,
`legendreWignerThreeJZeroSqRat_eq_zero_of_not_admissible`,
`legendreGauntRat_add_boundary`,
`legendreGauntRat_add_boundary_eq_two_mul_wignerThreeJZeroSqRat`,
`legendreGauntRat_zero_left`,
`legendreGauntRat_zero_left_eq_two_mul_wignerThreeJZeroSqRat`,
`legendreGauntRat_pairwise_add_eq_two_mul_wignerThreeJZeroSqRat`,
`legendreGauntRat_eq_zero_of_not_admissible`,
`legendreGauntRat_eq_two_mul_wignerThreeJZeroSqRat`,
`legendreGaunt_eq_two_mul_wignerThreeJZeroSqRat`,
`legendreWignerThreeJZeroSqRat_pos_iff_admissible`,
`legendreWignerThreeJZeroSqRat_nonneg`,
`legendreWignerThreeJZeroSqRat_eq_zero_iff_not_admissible`,
`legendreGauntRat_pos_iff_admissible`,
`legendreGauntRat_eq_zero_iff_not_admissible`,
`legendreGaunt_pos_iff_admissible`,
`legendreGaunt_eq_zero_iff_not_admissible`, `legendreGauntRat_nonneg`,
`legendreGaunt_nonneg`,
`legendreProductLinearizationCoeffRat_eq_mul_wignerThreeJZeroSqRat`, and
`legendreProductLinearizationCoeffRat_pos_iff_admissible`.  The three wrapper
names are `rvachevLegendreGramEntryRat_eq_two_mul_sum_wignerThreeJZeroSqRat`,
`rvachevLegendreGramMatrixRat_apply_eq_two_mul_sum_wignerThreeJZeroSqRat`, and
`upLegendreGramMatrix_apply_eq_two_mul_sum_wignerThreeJZeroSqRat`.

The new `QPochhammerEntire.lean` leaf contributes no public definitions and
five public theorems:
`hasProdLocallyUniformly_complexQPochhammerInf`,
`complexQPochhammerInf_differentiable`,
`complexQPochhammerInf_eq_zero_iff`,
`complexQPochhammerInf_eq_zero_iff_eq_inv_pow`, and
`analyticOrderAt_complexQPochhammerInf_of_eq_zero`.  For a fixed complex
strict contraction `q`, they give locally uniform convergence in the symbol
variable, entireness, the division-free factor-zero criterion, the exact
reciprocal-power zero lattice when `q ≠ 0`, and analytic order one at every
zero.  The raw factor criterion includes `q = 0`; no joint holomorphy,
outside-disk reciprocal formula, or centered characteristic-function/MGF
package is counted in this leaf.  The separately counted
`GeometricPochhammerNormalConvergence.lean` leaf is 0+3 and supplies the
outer spectral-product locally uniform theorem and its dyadic/Fabius
specializations, but none of those remaining compound spectral clauses.

The same merged tree adds the complementary general q-product leaves.
`QPochhammerDissection.lean` contributes no definitions and two theorems,
`finiteQPochhammerIn_dissection` and
`finiteQPochhammerIn_dissection_remainder`, for exact full-period and remainder
residue-class decompositions over an arbitrary commutative ring.
`QPochhammerInfinite.lean` contributes one definition and twenty-nine
theorems.  Its surface includes convergence and finite-prefix limits in
complete normed commutative rings, concatenation and residue-class dissection,
factor and reciprocal-power zero criteria, locally uniform parameter
convergence and continuity over complete locally compact normed fields, and
entireness with explicit nonzero derivatives and analytic order one at every
factor zero over `ℂ`, including `q=0`.  These two leaves therefore contribute
thirty-two declarations.  Their
generic `qPochhammerInfIn` is distinct from the older
`complexQPochhammerInf`; the five-theorem `QPochhammerEntire` API above remains
the analytic-order layer for the latter symbol, and no named equality bridge
between the two definitions is counted.

The synchronized q-series API also retains the full `origin/main` theorem
inventory.  `GaussianBinomialAtNegOneDerivative.lean` is 0+5, including the
commutative-semiring evaluation theorem `gaussianBinomial_X_eval`, and
`GaussianBinomialContinuity.lean` is 0+3:
`continuous_gaussianBinomial`, `tendsto_gaussianBinomial_nhds_one`, and
`gaussianBinomial_eq_finiteQPochhammerIn_div`.
`GaussianBinomialPalindromic.lean` is 0+14:
`reflect_add_of_natDegree_le`, `reflect_one'`,
`gaussianBinomial_natDegree_le`, `gaussianBinomial_zero_left`,
`gaussianBinomial_diag'`, `reflect_gaussianBinomial`,
`coeff_gaussianBinomial_reflect`, `coeff_gaussianBinomial_zero`,
`coeff_gaussianBinomial_top`, `gaussianBinomial_natDegree`,
`gaussianBinomial_monic`, `two_mul_derivative_gaussianBinomial_eval_one`,
`coeff_gaussianBinomial_one_of_pos_of_lt`, and
`coeff_gaussianBinomial_one`.
`GaussianBinomialPolynomialStructure.lean` is 0+5:
`natDegree_gaussianBinomial_universal`,
`gaussianBinomial_universal_monic`,
`coeff_zero_gaussianBinomial_universal`,
`gaussianBinomial_universal_reflect`, and
`coeff_gaussianBinomial_universal_symm`.
`CentralQBinomialReduction.lean` is 0+6: `finiteQPochhammerIn_mul_neg`,
`finiteQPochhammerIn_two_mul`, `finiteQPochhammerIn_map_ringHom`,
`central_gaussianBinomial_sq_mul_int`, `central_gaussianBinomial_sq_mul`,
and `central_gaussianBinomial_sq_div`.  `CyclotomicFactorization.lean` is
0+7: `div_add_div_le_div`, `div_le_div_add_div_add_one`,
`mem_range_and_mem_divisors_iff`, `finiteQPochhammerIn_X_eq_prod_cyclotomic`,
`finiteQPochhammerIn_X_eq_gaussianBinomial_mul`,
`prod_cyclotomic_pow_div_extend`, and
`gaussianBinomial_X_eq_prod_cyclotomic`.  The
`PrimitiveRootBlock.lean` 0+3, `QLucas.lean` 0+7,
`CyclotomicDivisibility.lean` 0+3, and `QCatalan.lean` 1+11 surfaces are
listed exhaustively above.  The
`NewtonInterpolation.lean` 3+19 and `QBetaIntegral.lean` 1+8 surfaces are
also listed exhaustively above.  The
`JacobiTripleProduct.lean` 2-definition/25-theorem tranche contains the finite triple-product
polynomial and field identities, the bilateral Jacobi `HasSum` forms, and the
pentagonal and paired-pentagonal `HasSum` corollaries.  The
`QBinomialTheoremInfinite.lean` 1-definition/22-theorem tranche contains the real comparison and
norm bounds, fixed-column Gaussian limit, Euler product, analytic q-binomial,
and reciprocal Euler `HasSum` results.  The subsequent
`GaussianBinomialFixedColumnRate.lean` 0+10 tranche supplies the explicit
finite-product defect, nonasymptotic fixed/shifted errors, shifted limit, and
relative/additive geometric-rate results inventoried above.  `QPascalSummation.lean` is 0+4:
`sum_gaussianBinomial_succ_mul`, `sum_gaussianBinomial_succ_mul'`,
`Commute.gaussianBinomial_left`, and `Commute.gaussianBinomial_right`.
`QuantumBinomial.lean` is 0+2, namely `quantumPlane_mul_pow` and
`quantum_binomial`.  Finally, the `RogersSzegoPolynomial.lean` 1-definition/9-theorem
tranche covers the zero, row-sum, and successor laws, dilation and three-term
recurrences, the Euler antidiagonal convolution, and
`hasSum_rogersSzego_generating`.  None of these retained APIs is replaced by
the fixed-nome `QPochhammerEntire` layer.

The audited formula contract is equally exact.  Admissibility is even total
degree plus the three weak triangle inequalities, equivalently
`i=b+c`, `j=a+c`, `k=a+b`.  If `C_n=choose (2*n) n` and `s=a+b+c`, then the
square datum is zero off support and
`W²(b+c,a+c,a+b)=C_a*C_b*C_c/((2*s+1)*C_s)`; factorially this is
`s!^2*(2*a)!*(2*b)!*(2*c)!/((2*s+1)!*a!^2*b!^2*c!^2)`.  The half-sum theorem
assumes exactly `i+j+k=2*s` and `i≤s`, `j≤s`, `k≤s`.  The two named boundaries
are `G_Q(i,j,i+j)=2*C_i*C_j/((2*(i+j)+1)*C_(i+j))=2*W²(i,j,i+j)` and
`G_Q(0,j,k)=(if j=k then 2/(2*j+1) else 0)=2*W²(0,j,k)`.  At every natural
triple `G_Q=2*W²`, its real counterpart is twice the real cast, positivity is
equivalent to admissibility, vanishing is equivalent to nonadmissibility, and
all three forms are nonnegative.  The rational product coefficient is
`(2*k+1)*W²` and is positive exactly on support.  Both rational finite-Gram
wrappers are the unconditional twice-sum
`2*∑ r∈range ((i+j)/2+1), c_r*W²(i,j,2*r)`; the real wrapper has the same finite
form and assumes exactly `F : BoundedFabius` and `hF : IsFabius F`.

This square datum is not a bridge to a separately implemented general Wigner
symbol.  No signed value or phase convention, half-integer or
nonzero-magnetic-index API, general `3j`/`6j`/`9j`, orthogonality, recoupling,
or named Wigner-symmetry theorem is present.  The Gaunt factorial identity and
product-coefficient nonnegativity/zero criteria are composable but do not have
separate named wrappers.  Infinite Legendre interchange, Christoffel
reconstruction, roots/quadrature, Padé/J-fractions, infinite Jacobi theory, and
asymptotics remain open.

The New Frontiers finite Gram--Legendre crosswalk consequently has eleven modules,
twenty definitions, and 109 theorems, hence 129 public declarations; its
predecessor nine-module subtotal was `18+81=99`, and the two closed-form leaves
contribute `2+25` and `0+3`.  The integer-index zero-row square datum and finite
Wigner-square Gram route are closed, while signed/phase, half-integer,
nonzero-magnetic-index, general Wigner/recoupling, and later infinite spectral
layers remain outside this tranche.  The baseline records zero missing headers
and zero missing doc comments, so every future source addition must preserve
that invariant.  Run the script for
live numbers after merging concurrent source work.

The additional declaration in `PolynomialCombExactness.lean` is
`integral_polynomial_mul_rvachevUp_eq_dyadic_tsum`, the exact normalized
physical-coordinate self-sampling quadrature for every real polynomial whose
natural degree is at most the dyadic level and every real phase.

The effective-inverse union contributes three modules and seventeen public
declarations.  `EffectiveMonotoneInverse.lean` is exactly 2+6: the definitions
`SequentiallyComputableOn` and `unitClamp`; the clamping theorem
`unitClamp_sequentiallyComputable`; the three certified tolerant-comparison
lemmas `tolerantDifference_error`, `tolerantDifference_safe_updates`, and
`tolerantDifference_inconclusive`; and the constructive inverse results
`tolerantBisection_correct` and `effectiveInversionOn_Icc`.  The latter works
for a computably dyadically approximable strict monotone bijection of
`[0,1]` supplied with a computable positive reciprocal inverse modulus; its
three-way comparison never decides equality, because the inconclusive branch
already certifies the requested inverse error.  `FabiusInverseComputable.lean`
is exactly 0+1: `fabiusInv_isComputableRealFunction` combines that sequential
realizer with the logarithmic Delta modulus for every bounded Fabius witness.
Clamping makes the theorem about the total inverse on all real inputs.  These
results are computability certificates, not an input-bit running-time bound or
an exact least endpoint-mass denominator.  The third module,
`EffectiveGapInverse.lean`, contributes 4+4, the eight declarations listed
above, and supplies the generic rational-gap-to-modulus bridge; its clamped
extension boundary remains explicit.

`FabiusInverseExactDyadicModulus.lean` contributes two definitions and ten
theorems.  The definitions are `inverseFabiusExactDyadicDenominator` and
`inverseFabiusExactLogarithmicDenominator`.  Its exhaustive theorem surface is
`inverseFabiusExactDyadicDenominator_primrec`,
`inverseFabiusExactDyadicDenominator_pos`,
`inv_inverseFabiusExactDyadicDenominator_le_fabiusAtInverseTwoPow`,
`inverseFabiusExactDyadicDenominator_isLeast`,
`abs_fabiusInv_sub_lt_inverse_two_pow_of_lt_exactDyadicDenominator`,
`exists_fabiusInv_gap_of_lt_exactDyadicDenominator`,
`inverseFabiusExactDyadicDenominator_isLeast_strictModulus`,
`inverseFabiusExactLogarithmicDenominator_primrec`,
`inverseFabiusExactLogarithmicDenominator_of_pos`, and
`abs_fabiusInv_sub_lt_inv_nat_of_lt_exactLogarithmicDenominator`.  The first
denominator is least only for a fixed dyadic output target; the logarithmic
`1/n` conclusion is a witness, not a leastness theorem.  Its value at zero is
the convention `d(0)=1`, with no zero-input modulus conclusion.  The two
named `Primrec` theorems close the recursive-denominator clause without
asserting an input-bit running-time bound.

The retained comb-interpolation synthesis PDF is a validated 158-page A4
historical receipt: the current source includes a post-render update to its
additive-dyadic chapter, so a fresh parity build remains pending.  The rebuilt
Integration-and-Transform master retains a historical 377-page PDF.  The canonical
q-series synthesis is a validated 389-page historical receipt synchronized to
the immediately preceding source checkpoint.  The current source adds the
twelve-declaration terminating q-Chu/reversal closure, so final parity is
again pending.  The retained 183-page primary, 130-page walkthrough, 257-page
canonical frontier, 301-page Representation Frontiers, 41-page New Frontiers,
and 88-page notation-catalogue artifacts likewise predate their current merged
sources.  Their package notices treat those PDFs as historical validation
receipts, not parity claims, until fresh uninterrupted three-pass builds
complete.  The inverse-computability receipt likewise still reflects the
historical 675/8,909 census and requires refresh against the live 952/11,884
inventory.  The canonical inverse-theory publication retains a 134-page
artifact synchronized at its latest-main source checkpoint; the merged
effective-inversion and superconvergent-synthesis tranches make current parity
pending.

### What the review pass caught

Both waves paired each documenting agent with an independent auditor, and that
was not ceremony.  The recurring defect was never a wrong formula -- it was a
false claim about dependencies: "every coefficient computation below factors
through this" when one does not, "the denominator in every ratio bound here"
when it is the denominator of one, "used by X" when X re-derives it inline.
Prose asserting a dependency is much easier to get wrong than prose asserting a
statement, because the statement is on the next line and the dependency is not.

Two doc comments had silently dropped an ambient `IsFabius F`; one stated its
two interval inclusions in the wrong directions; one said an interval
restriction was necessary when the file proves no converse.

The second wave was told this in advance and instructed to write no "used by"
clause at all unless it had been grepped.  78 verified consumer clauses came
out of that, and the defect rate fell accordingly.

### Doc comments that contradicted their statements

A separate sampling pass read about 190 doc-comment/statement pairs looking
for prose that claims more, or less, than the Lean statement.  The corpus is in
good shape here; three defects were found and fixed.

1. `norm_iteratedDeriv_negativeLaplaceVerticalKernelLogFirst_le` was documented
   as holding "uniformly on every vertical strip center `|theta| <= 1`".  Its
   statement has no such hypothesis: `theta` is an arbitrary real and the
   constant does not mention it.  The prose *understated* the theorem, which
   would have sent a reader looking elsewhere for a bound this lemma already
   gives.

2. and 3. `legendrePolynomial_contDiff` and
   `contDiff_negativeLaplaceVerticalCurve` assert `ContDiff R (top)` with the
   exponent elaborated at `WithTop ℕ∞`.  In this Mathlib that is the *analytic*
   exponent `ω`, not `C^∞`:

   ```text
   Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean:118
     scoped[ContDiff] notation3 "ω" => (⊤ : WithTop ℕ∞)
   Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean:120
     scoped[ContDiff] notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)
   ```

   Both were documented as merely "smooth".  The corpus writes `ContDiff ℝ ∞`
   in 66 places and `ContDiff ℝ ⊤` in only these two, so the distinction is
   deliberate everywhere else.

   This distinction is worth policing in this corpus in particular.  Its
   central regularity result is that the Fabius function is `C^∞` everywhere
   and analytic exactly off `[0,1]`; a doc comment that says "smooth" over an
   `ω` statement is the one confusion the library exists to prevent.

## Suggested order of work

1. Any new file: header and doc comments at the time of writing.  The ratchet
   gate makes this cheap to enforce.
2. The five worst files.  Clearing them removes about a quarter of the
   backlog.
3. Doc comments on public declarations that appear in `PAPER_COVERAGE.md`,
   since those are the ones an outside reader reaches first.
4. The long interior estimate chains, one module at a time, ideally by the
   agent that most recently worked in the module and still has its structure
   in mind.

Adding a doc comment cannot change elaboration, so this work needs no build
slot.  On a machine where a full rebuild costs the better part of a day, that
makes it unusually good value.
