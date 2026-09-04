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
pass scans 952 facade-reachable modules and 11,884 public declarations.  It
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
`FinitePrefixThueMorseCollapse.lean`, `ProuhetBaseTwoBridge.lean` leaves,
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
the historical 925/11,619 checkpoint. Later merged source work contributes
the zero-definition leaves `QPochhammerLambertForm` 0+5,
`CentralQVandermondeInfinite` 0+4, `TriangularPowerProduct` 0+2,
and `MeanValueBracket` 0+6; the 1+12 `ThueMorseNewmanSelfSimilarity` leaf; and
a net twenty-nine further declarations in existing modules. These changes
reached the pre-reciprocity 930/11,678 checkpoint. Reciprocity then gave the
historical 931/11,685 checkpoint, and the dyadic-boundary and finite-prefix
leaves gave 933/11,695. The base-two Prouhet tranche gave the historical
934/11,709 checkpoint. Later upstream work reaches 952/11,881; the three
unique local q-binomial compatibility wrappers give the exact-name-deduplicated
live 952/11,884 union. On the earlier
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
historical checkpoint was 902 modules and 11,440 public declarations.  The
three Gaussian second-moment declarations recorded next give checkpoint
`71c908e` at 902/11,443.  The first four theorems of the new
Lambert--Bernoulli leaf then give the exact-radius 903/11,447 checkpoint, and
its fifth theorem gives completed Lambert checkpoint `217a6b9` at
903/11,448.  The five fixed-column declarations give local checkpoint
`581bf17` at 903/11,453.  Independently, the nine-declaration moment-polynomial
leaf gives parallel upstream-only checkpoint `3b6396d` at 904/11,457; merging
the two branches gave the historical 904/11,462 local union.  Its three definitions are
`geometricRichardsonKernel`, `qPochhammerNormalizedDataSeries`, and
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
and exactly eight theorems after the two shared declarations remain
canonically upstream:
`norm_finiteQPochhammerIn_pow_sub_one_le`,
`norm_finiteQPochhammerIn_self_mul_gaussianBinomial_sub_one_le`,
`norm_gaussianBinomial_sub_inv_finiteQPochhammerIn_le`,
`norm_gaussianBinomial_add_sub_inv_finiteQPochhammerIn_le`,
`gaussianBinomial_fixedColumn_relativeError_isBigO`,
`gaussianBinomial_shifted_fixedColumn_relativeError_isBigO`,
`gaussianBinomial_fixedColumn_error_isBigO`, and
`gaussianBinomial_shifted_fixedColumn_error_isBigO`.

The upstream `norm_finiteQPochhammerIn_pow_sub_one_le_exp` and the first local
estimate hold in every normed commutative ring with normalized multiplicative
norm when `‖q‖ ≤ 1`: they bound `‖(q^m;q)_k-1‖` first by
`exp(k‖q‖^m)-1` and then by `(k exp k)‖q‖^m`.  Under `k≤n`, the next local theorem gives the denominator-free relative
bound `‖(q;q)_k[n,k]_q-1‖ ≤ (k exp k)‖q‖^(n-k+1)`, which remains meaningful at
roots of unity.  Over any normed field, `‖q‖<1` suffices for the fixed and
shifted nonasymptotic additive bounds and all four relative/additive `IsBigO`
results at the rates `q^(n-k+1)` and `q^(n+1)`.  The shifted
`tendsto_gaussianBinomial_add_atTop` theorem is reused from the upstream module.
There is no completeness or `q≠0` hypothesis, and the displayed constant is
elementary rather than sharp.  Together with the pre-existing
`tendsto_gaussianBinomial_atTop`, the shifted limit and two relative-error
theorems discharge every clause of `thm:fixed-column-limit`; the two additive
theorems are stronger companion estimates.

Together with the prior 905/11,474 branch inventory and the three-declaration
Lambert leaf, the geometric-uniform and regular-central leaves, the incoming
pre-dedup ten-theorem version gave the historical fixed-column checkpoint of
909 modules and 11,508 public declarations.  Canonical upstream ownership of
the two shared names changes the per-module split, not that historical branch
census.

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
`RvachevLegendreBiorthogonality.lean` gave the historical facade inventory
925/11,619. Later merged work reached the pre-reciprocity 930/11,678 checkpoint;
reciprocity gave 931/11,685, and the dyadic-boundary and finite-prefix-collapse
leaves gave 933/11,695. The base-two Prouhet tranche gave 934/11,709. Later
upstream work reaches 952/11,881, and the three unique local q-binomial
compatibility wrappers give the live 952/11,884 inventory, with no missing
module header or public declaration comment.

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
historical 925/11,619 checkpoint. Later source work and reciprocity gave
931/11,685; the dyadic-boundary and finite-prefix-collapse leaves then gave
933/11,695, and the base-two Prouhet tranche gave 934/11,709. Later upstream
work reaches 952/11,881; the three unique local q-binomial compatibility
wrappers give the live 952/11,884 inventory, with no documentation gaps.

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
one definition plus one theorem, giving the historical 925/11,619 checkpoint.
The live inventory after all later upstream work and exact-name deduplication is
952/11,884. Its
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

The base-two Prouhet tranche adds one module and fourteen public declarations to
the historical 933/11,695 checkpoint, giving the historical 934/11,709
inventory. Later upstream work reaches 952/11,881, and the three unique local
q-binomial compatibility wrappers give the live 952/11,884 inventory. The delta
is the union of the new zero-definition/six-theorem
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

The combined 282-result q-series forward ledger is 182 Exact / 78 Partial /
14 None / 8 interface rows, and its source concordance is 95 Lean-proved /
383 human-proved frontier / 60 not-applicable / 9 conjecture rows. In
particular, `GeometricUniformMomentRatFunc.lean` 1+4 makes
`thm:qF-moment-polynomial` **Exact by assembly**; the broader
`thm:geometric-uniform-mgf` remains **Partial**.

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
At that checkpoint, `QBinomialTheoremInfinite.lean` contributed one definition
and twenty-two theorems: real comparison products and Gaussian majorants,
fixed-column convergence, Tannery transfer, Euler's product and reciprocal expansions, and
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
73-name incoming increment.  Those 1+22, 69, and 73 counts are historical;
the current-tip expansion of `QBinomialTheoremInfinite.lean` is recorded in
the synchronized inventory below.  The two subsequent
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
declarations, yielding 661/8,787.  At that checkpoint the four
root-of-unity/q-Catalan modules were recorded as a twenty-six-declaration
tranche, yielding 665/8,813.  After the later `QLucas` correction, their
current exhaustive total is twenty-five declarations (0+3, 0+3, 1+11,
and 0+7).  The original Jackson
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
`QBinomialTheoremInfinite.lean` 1-definition/27-theorem tranche contains the real comparison and
norm bounds, effective finite-product convergence, fixed-column Gaussian limits
and geometric rates, Euler product, analytic q-binomial, and reciprocal Euler
`HasSum` results.  Its five newest declarations are
`norm_finiteQPochhammerIn_pow_sub_one_le_exp`,
`isBigO_finiteQPochhammerIn_pow_sub_one`,
`tendsto_gaussianBinomial_add_atTop`,
`isBigO_gaussianBinomial_sub_inv`, and
`isBigO_gaussianBinomial_add_sub_inv`.  The fixed-column limit and rates are
Exact: the Lean rate statements use additive `IsBigO`, which is equivalent to
the manuscript's multiplicative form after multiplying by the fixed nonzero
denominator `(q;q)_k`; the unshifted and `k`-shifted errors are respectively
`O(q^(n-k+1))` and `O(q^(n+1))`.
`GaussianBinomialFixedColumnRate.lean` is the 0+8 companion tranche after its
two shared declarations remain canonically in `QBinomialTheoremInfinite.lean`;
it supplies the elementary finite-product defect, nonasymptotic fixed/shifted
errors, and relative/additive geometric-rate results inventoried above.
`QPascalSummation.lean` is 0+4:
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

The comb-interpolation synthesis receipt remains the accepted current 160-page A4
build recorded below. Its former 158-page artifact remains an
explicit historical receipt. The rebuilt
Integration-and-Transform master retains a historical 377-page PDF.  The
five source/PDF pairs synchronized by commit
`581bf177f8e784ab5d4836acc2b4a47e285e6ce0` are now historical because merging
the parallel upstream-only moment-polynomial checkpoint
`3b6396deb6056523d944d79602d1bf7ecf18ec10` changes all five TeX sources and the
independently published standalone geometric-q root.

**Historical first-merge publication receipts (10/10 accepted at their recorded source snapshots).** Primary:
root `14628L/733516B/39d1b0b87cabbd75622b2c882db34bc842f9057561efa8d8a93918acaa97d7ea`;
two-file aggregate
`14912L/745351B/2f56e31a0545297886fd0b9f2c9005053f6d902a99f3b1b965b5d659277c71b2`;
passes `197/199/199`; PDF
`199pp/1645695B/fe3a27d09c19404a0b0827b047e57ed3d688c465487bf7054e10ca18c7f78cef`;
log `1315L/52885B/d6e65808a1bd2bc9e3305154e883a2e4f892d4508b63b6da4b27f83b382e1800`.
Walkthrough: root
`7135L/514216B/0e726220d274add480fedd771af140d2d5da77497b64fba4bf14294c72817fa5`;
two-file aggregate
`7419L/526051B/9599230f56ce10be66991a4c7f2923a91806a988426053dfed69d01fa8c9830f`;
passes `166/171/171`; PDF
`171pp/1250845B/e731f6af11f4f00b65b827a7a713794010c0cdf846621df91254b9e2ff2fa0f5`;
log `1311L/52881B/730df857bc56dab609d1599b66ac3710382b54331754b529a0b987c14d44a41f`.
Canonical: root
`18680L/851566B/8e0f799dead1a3d7d7df6a33d1b4cbe61a3fafcfc39bd68e6fb7f4fc6f63f31a`;
two-file aggregate
`18964L/863401B/07c65c06d64e0230f68cc644c4594bb47bc1f77fa43e35f04a5d4327124317d8`;
passes `265/273/273`; PDF
`273pp/1938114B/ad2362be615a8592a308abe920de982121b58e670409d3bc725e506dcae0a765`;
log `3123L/105692B/1bedd5ffae49c5ad85f5ce2de3069fb7e7da432ec7d5095475376982fe6437d6`.
Lambert: root
`4961L/183269B/83301b4c66660713a70974263b6f191ea01f9ed8f5ae228495f644887b616568`;
two-file aggregate
`5245L/195104B/25141b9ee818b20ddf8349d88ec4f2dc977ff0ab35ca34e62cd62da64c2cf06a`;
passes `68/70/70`; PDF
`70pp/966637B/6c150ff18889030345de3e1a8581d5ea0ac75789a9720c1d5164ed4e7ec4b7fb`;
log `1574L/57800B/9f995a50e3ab25256083edee745a1889027787194e3b3c6d1f12f60bf687145c`.
q series: root
`16812L/840316B/64dc18dedbd1966624162b64129128b24b51ca88d8a9e496c661cc1a46a24ba6`;
15-file aggregate
`26593L/1198416B/762e6d6ca441de51db9679f95d6a01d8353e8044639f99803734719b8a65a5f8`;
passes `393/401/401` plus three clean `makeindex` runs (`164/0/254/0`);
PDF `401pp/2500131B/fd54459baf10845b5a89cc8b204f59ea33a0665b434ad270e738884072a1e6e1`;
log `1230L/44401B/37dca6371ea8bf9285e5f104d550bd584a290f4aa92fcf5679b028c9dfd3079d`.
Inverse: root
`293L/11514B/92fab1fae38bbcf86a45b51bfe7ff34e2801361df9d2f3d6aa3de4dc966eaa3c`;
14-file aggregate
`10909L/438542B/24bdab6491f5ca84fbb9e716f92c7923e8961b6acbc793d9aa5e0faa68852444`;
passes `132/137/137`; PDF
`137pp/2045463B/ca403c74e2b46923ce9ac1eda547ab1bcb5e71039b35c8ee394acdd2014c4f8e`;
log `1569L/64081B/d4aa25579c958e11c59d914c74dfca331fc2bbccf7bba4715dcd18fa050e771f`;
then-current source-only 23-input closure digest
`e07cb51f4fe072cd79a014cc891cb8cede62880593d7659b17da9377a21099bc`.
Comb: root
`187L/6724B/a4c1e33165ff7291682cd890f23fe4af98e9f11f7ad1d9a7f8b68c78d53f9a56`;
nine-file aggregate
`12773L/483551B/cef466ee56f6bb864faaac2244bccf1dbc2fd4032a717b6c81604551c0427309`;
passes `153/160/160`; PDF
`160pp/2468109B/bb714c8be4b82de2a888e0302da3aaf957b9e885f2c5f59466b3ea5d659e3f71`;
log `1370L/58773B/8df53a7db51c85b7a046c5f58587319095b3d28c61b0091861bdeb1f43b342e3`.
Up: root
`2385L/99806B/81f3ba09894aca8331ae33c77e2a56f78c107fa3b04072878cff8ad60e815b5a`;
five-file aggregate
`11bd62d880f5ba4c63d872fb0ba5d801d10ba2a2337ef5d098643383639086dd`;
passes `61/63/63`; PDF
`63pp/1077921B/0903f2920d21f0ea8182822c31338e0be268d4d77bc8ddb7a2ff861ba2a6aa5f`;
log `964L/38999B/52bd9d03864853f1ee31fa682fa96806345bb355582831c55fcc152c1acb2e7d`.
Thue--Morse: root
`10557L/482022B/8cef828c3d92a0017e22463ac90878a5e3a98e1138059d5f4793d47c04a88404`;
two-file aggregate
`10841L/493857B/79a43711c6989336166d6b2ed1faa306cc985b8d70557025ab139791d455723c`;
passes `139/144/144`; PDF
`144pp/1740015B/deb63fe66fc8f020bb072acbc4301e9b7c9f0559b165cbae2c076f261405c5be`;
log `1503L/59417B/1219dbc87bc4f9920c40b24659182220b14e7908a45a9eb33d0f19390148c64b`.
Geometric-q: root
`27624L/1273010B/0839b42a3fb055d860b8e8a3d1ff5e84c2f4addce314d04707c5a067e81553d9`;
seven-file aggregate
`27997L/1288647B/18c4c6607e9b7564909ca7e647152a26e517f54d5007e157265b3f61adf8e4f0`;
passes `387/404/404`; PDF
`404pp/8341830B/a083b130a1568dc37af824294b033485f82c97dbeb30a4c4de4d463d04e99530`;
log `2557L/114343B/4de474675a2dcde519c36ff1ac7067717c64b60b92bd40b999d0d117ba1f8df6`.
All ten passed every recorded prohibited-log, A4/rotation, PDF 1.5,
encryption, font/subsetting, Libertinus, Type-3, and visual gate; the q index
was clean. For geometric-q, all 404 pages are A4 at rotation zero, the PDF is
unencrypted PDF 1.5, all 43 font rows are embedded and subset, Libertinus has
11 rows, Type-3 has zero rows, and checksum basenames and PDF/source references
are absent.

The following six accepted receipts are retained only as explicit history for
their recorded pre-merge source snapshots:

- primary exposition: source 13,748 lines / 686,081 bytes / SHA-256
  `661ebb4e337f2ce79e8c3d5ca823bcdcce519fe220ff4b02d9dd5aef08d42cf9`;
  passes 185/187/187; PDF 187 A4 pages / 1,581,617 bytes / SHA-256
  `41e95844c6e5dc04933cc7256d285346c10eb29ff7eadf5a4165c472fa453eab`;
  final log 1,309 lines / 52,641 bytes / SHA-256
  `f177cb91c161f4dfc60017ddfd5efed1586ef28a4c80c68a9ae78cf19cf75da6`.
- Lean walkthrough: source 6,638 lines / 460,643 bytes / SHA-256
  `c44ab7ab38da46f8959a63916437b3d8ded628a3930f81dfa1a87996c7c66b8d`;
  passes 146/151/151; PDF 151 A4 pages / 1,188,993 bytes / SHA-256
  `907b3d2dbfc66192b63b86ada1015779229636855734815402ae5af9ea9bf015`;
  final log 1,296 lines / 52,126 bytes / SHA-256
  `0962c255aeb75bce3bcee89cbc1db9defe369e8c79ee6b6aa0435befdca410cf`.
- canonical frontier: source 17,983 lines / 806,798 bytes / SHA-256
  `a1cb1c0db2784116ca1f1d6fd1ce7e8b29afc52c64c93e7001bbffb91f775039`;
  passes 252/260/260; PDF 260 A4 pages / 1,877,420 bytes / SHA-256
  `78c19b361da06836c20c62fa5bd50131eb8fa47d3e89d37a7f089a51568953b3`;
  final log 2,990 lines / 101,866 bytes / SHA-256
  `4854a89ba1a3bb41248b9428cfed572f6ed593125b5a8fb43d5625d8d392dc0f`.
- Lambert Guide: source 4,873 lines / 177,465 bytes / SHA-256
  `90413f46373415edef411e9ea3b2d94006f7342bd2fa3ea931ca975d7f64b97e`;
  passes 67/69/69; PDF 69 A4 pages / 958,516 bytes / SHA-256
  `b159cd41f5b3e53060fa85fcfc4812d504cc1fff8400c03ecb7ef4018f37cd2c`;
  final log 1,574 lines / 57,795 bytes / SHA-256
  `5c81cd6b8dc2cf070c4b1995c98c0d046c54d28f0e682b78b5ad9e16c0a8caa7`.
- q-Pochhammer/q-binomial monograph: master 16,448 lines / 816,185 bytes /
  SHA-256 `a463abef7bb3c70e12a568a46fc192aac88a8ce240f8f781fff2b018a4aa086d`;
  full graph 26,114 lines / 1,168,039 bytes / aggregate SHA-256
  `d4c5b84cc07f6abb99279c5bba4fdf7404326426cbe81f4b33b72ba01e62739c`;
  passes 383/391/391 with `makeindex` after each pass (164 accepted, 0 rejected,
  0 warnings); PDF 391 A4 pages / 2,464,712 bytes / SHA-256
  `a52eb90dec7b874cc29dea891a107b9eb2d55e6727eb8bd8943d0aab609c58a6`;
  final log 1,231 lines / 44,343 bytes / SHA-256
  `fb74b0c4cbd75d9022c78c1df5c1d567120bd67728d5b418697ddc5a2aa8f450`.
- standalone geometric-q root: source 27,520 lines / 1,266,515 bytes /
  SHA-256 `8292f10862334cb809139259eeb4906bb14f517d41b9600c9b7ad53bb21525b1`;
  passes 385/402/402; PDF 402 A4 pages / 8,332,886 bytes / SHA-256
  `d47431e4d3e721fccf12f90226db77f1898e44b477878954acca3a6e90127cf4`;
  final log 2,557 lines / 114,331 bytes / SHA-256
  `4d6f8c7974def4a3f9e6bc8ccdffefc3eef7ca8cb7c2f0145a075f95b82ff45e`.

At those recorded source snapshots, all six passed the documented log, A4
page, font, Type-3, extraction, and visual gates; the Lambert clipping defect
and canonical page-176 running-head collision were repaired before acceptance.
The following `581bf` pairs remain explicit
historical receipts.  The canonical q-series checkpoint is a 391-page,
2,464,122-byte A4 receipt with SHA-256
`c0a00720685f40e0684b4858e7ce18ce134701529898fd4574d09b6c090e0e91`,
which matched its 16,433-line, 815,194-byte master with SHA-256
`f2aae6ddc3d7a399f9ed47806a0abe6458cbcab37bf2aac9f55ad3913b5a0e2d`.
The preceding 389-page artifact remains a historical receipt.  The primary
checkpoint is a 187-page, 1,578,751-byte A4 PDF with SHA-256
`7a93d9c47c22c62dc50cda6a64d030bfad5f44a9ef4cc5568b3b8b16b014bc8f`,
which matched its 13,720-line, 684,413-byte source with SHA-256
`7efb8d2294a15cf6b150bb0b04b35db74cf68db3f3cdb4bc5d765b7738504019`.
The Lean-walkthrough checkpoint is a 150-page, 1,185,846-byte A4 PDF with
SHA-256
`8a5416061addfb480f410e8306340994fe7f5160927a928112087b6b1d5c0cf5`,
which matched its 6,603-line, 457,421-byte source with SHA-256
`4e6ea24897a31683c53e71c6cb97eb21f37eff3ae4e452add429bd9f47646ea6`.
The canonical-frontier checkpoint is a 260-page, 1,875,190-byte A4 PDF
with SHA-256
`fee3b5af21b01b16c41cf8291ba0508d1e6c613bfd098cdef457cde44ea693c2`,
which matched its 17,947-line, 804,625-byte source with SHA-256
`ac6b28fb8a98d97ed4b7a0fe7a5ba2cdfab852fb6de1ee2ecfda4aed75804371`.
The Lambert-Guide checkpoint is a 70-page, 958,713-byte A4 PDF with SHA-256
`24e8bf561283ffc5427297df6f656696a7e2538731e53d03d59e4268b50772fc`,
which matched its 4,864-line, 176,796-byte source with SHA-256
`3f3552983a73db2dab94f3625d10d054b747ee03fc2758e257af86f6216deab5`.
Their preceding 183-page, 130-page, 257-page, and 66-page artifacts remain
historical receipts.  The 301-page Representation Frontiers, 41-page New
Frontiers, 88-page notation catalogue, and 377-page Integration-and-Transform
artifacts likewise predate or are unsynchronized with their current sources;
their package notices correctly treat them as historical validation receipts
rather than parity claims.  They are not members of the exact merge-affected
set below and retain their separately recorded pending status.  The retired
inverse-computability predecessor likewise still reflects the historical
675/8,909 census and requires refresh against the live 952/11,884 inventory.

The first merge changed the source closure of exactly ten retained publications
and produced the accepted receipts above. Up and comb remain current. All
accepted current campaign receipts are centralized in the [draft
manifest](semi-formalized-research-frontiers/drafts/MANIFEST.md#current-post-merge-publication-receipts).
All nine campaign roots now have current source/PDF parity. The incoming
Transseries PDF remains a historical pre-merge checkpoint; its new 704-page
render is current but retains 114 overfull boxes and 11 duplicate Hyperref
targets for a later layout-repair pass.

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
