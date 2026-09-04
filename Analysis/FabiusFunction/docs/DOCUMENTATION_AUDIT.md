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

The live 2026-09-04 semantic union contains 903 modules and 11,448 lexically
visible public declarations, with zero missing module headers and zero missing
doc comments; the checked JSON baseline records this clean state.  The
corresponding origin inventory has 11,447 declarations because it lacks this
tree's unique public `complexQPochhammerInf_eq_qPochhammerInfIn` bridge.  The
earlier 901/11,419 local semantic union remains a historical checkpoint, as
does the post-merge 2026-09-01 inventory of 675 modules and 8,909 declarations.
Relative to the 610/8,318 activation checkpoint, that tree added sixty-five
modules and 591 declarations, and relative to the earlier 630/8,552 merged checkpoint it added
forty-five modules and 357 declarations.

#### Terminating `₂φ₁` reversal and q-Chu--Vandermonde tranche

In the origin progression, that public API growth left the module count
unchanged and added twelve declarations to the immediately preceding
901/11,418 inventory.
`TwoPhiOneReversal.lean` grows from 1+6 to 2+12 (one definition and six
theorems added), and `QChuVandermonde.lean` grows from 0+5 to 0+10 (five
theorems added).  The resulting origin q-Chu checkpoint was therefore exactly
901 modules and 11,430 public declarations; carrying the unique local bridge
gives 11,431.  The generating-function tranche below is the subsequent live
increment.

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

`GeometricRichardsonGenerating.lean` adds one source module and exactly ten
public declarations to the origin 901/11,430 q-Chu checkpoint, giving the
origin 902/11,440 inventory and the authoritative local 902/11,441 union after
the unique public bridge is retained.  Its three definitions
are `geometricRichardsonKernel`, `qPochhammerNormalizedDataSeries`, and
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
module left the module count at 902 and added three public theorems, bringing
the origin census to 11,443 public declarations and, with the retained public
q-Pochhammer bridge, that historical local checkpoint to 11,444.  The module's
exhaustive public
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
public declarations.  The incoming d8b delta contributes thirteen declarations
across this final surface.  The seven pairing theorems are
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

`LambertWBranchGapBernoulli.lean` adds one source module and exactly four
public theorems to the historical 902/11,443 checkpoint, giving the live
origin census of 903/11,447 and the authoritative local union of 903/11,448.
Its exhaustive public surface is
`summable_norm_bernoulli_mul_pow_div_factorial`,
`summable_bernoulli_mul_pow_div_factorial_iff`,
`hasSum_bernoulli_mul_pow_div_factorial`, and
`principalLambertW_lowerLambertW_eq_bernoulliSeries`; five private majorant,
coefficient-transport, norm-transport, zeta-lower-bound, and even-term helpers
are excluded from the public count.  Together with the three finite
branch-coordinate modules, this makes the four-module Lambert union four
definitions and 36 theorems, 40 declarations.

The first theorem proves absolute convergence of the real Bernoulli
exponential generating series for `|z| < 2π`.  The second proves for every
complex `z` that the series is summable exactly when `‖z‖ < 2π`; consequently
every boundary and exterior point diverges, and its proof exhibits an
even-indexed subsequence whose term norms stay at least `2`.  The third gives the real
series its actual `HasSum` value `z/(exp z-1)` under the additional condition
`z ≠ 0`.  The final theorem specializes this evaluation to
`x ∈ (-exp(-1),0)` and
`branchGap x < 2π`, returning both branch identities as one conjunction.  It
makes only the Lambert Guide label `eq:pair-Bernoulli-general` **Exact**.  The
complex convergence theorem includes `z=0`, but there is no complex `HasSum`
quotient evaluation on the punctured disk or separate theorem giving the
series value `1` at the removable origin.  The real quotient theorem deliberately
excludes `z=0`, while the branch theorem excludes both endpoints.  No remainder
estimate or higher/convergent Puiseux expansion is included.

#### Completed dyadic derivative filtration

`DyadicDerivativeFiltration.lean` has zero definitions and six theorems:
`rvachevUp_eq_zero_of_one_le_abs`,
`iteratedDeriv_rvachevUp_dyadic_eq_zero`,
`iteratedDeriv_rvachevUp_dyadic_critical`,
`dyadic_depth_eq_max_nonzero_iteratedDeriv`,
`iteratedDeriv_rvachevUp_eq_extendedFabius`, and
`iteratedDeriv_rvachevUp_dyadic_below`.  The first four give support
vanishing, above-depth vanishing, the signed critical-depth value, and exact
depth detection.  The final two are the new declarations: the first identifies
every up derivative at every `x<1` with the scaled signed global Fabius value,
and the second specializes it for `m<n` and `a<2^n` to the report's
denominator-`2^(n-m)` dyadic formula.

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
The rigorous forward q-monograph ledger is 165 Exact, 91 Partial, 18 None,
and 8 interface rows; its source concordance is 86 Lean, 392 human, 60 N/A,
and 9 conjecture rows, and the concordance extractor passes.
`prop:gaussian-bound` is Exact.  `thm:q-lucas` remains
Partial because the proved evaluated primitive-root identity is weaker than
the manuscript's polynomial congruence modulo `Φ_d`, and
`cor:babbage-derivative` remains Partial because only its value is formalized.
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
optimal/minimum-variation decoder theorem.  The subsequent
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
declarations, yielding the historical 675/8,909 checkpoint.

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

An earlier retained six-module increment is exhaustively counted as
`QPochhammerInfiniteBounds.lean` 0+5, `HeineTransformation.lean` 2+5,
`QGaussSummation.lean` 0+2, `QPochhammerComplexOrder.lean` 1+4,
`BasicHypergeometricSeries.lean` 2+5, and `QMultinomial.lean` 1+9: six
definitions and thirty theorems.  It adds finite-prefix bounds, the Heine and
q-Gauss identities, a ratio-defined complex-order q-Pochhammer API, general
basic-hypergeometric terms and summability, and the division-free recursive
q-multinomial interface.  In that interface, `qMultinomial`,
`qMultinomial_nil`, and `qMultinomial_cons` need only `Semiring`; the
diagonal, singleton, pair, naturality, and universal laws use `CommSemiring`,
the factorial law uses `CommRing`, and the field quotient assumes exactly
`(q;q)_(sum l) ≠ 0`.  The displayed contraction, nonvanishing, and other
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

The following two-module increment is exhaustively counted as
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
`d`-th root in a commutative integral domain, and `b,s < d`.
The local `two_mul_choose_two` helper is private; its public owner is
`QChuVandermonde.lean`.

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

The five-module q-calculus increment is exhaustively accounted for as follows.
`PolynomialQDerivative.lean` has the two definitions `qInt` and `qDerivative`
and the seventeen theorems `qInt_zero`, `qInt_one`, `qInt_succ`, `qInt_succ'`,
`qInt_add`, `qInt_one_left`, `one_sub_mul_qInt`, `qDerivative_apply`,
`qDerivative_monomial`, `qDerivative_C`, `qDerivative_X_pow`, `qDerivative_X`,
`qDerivative_C_mul_X_pow`, `eval_qDerivative_mul`,
`qDerivative_comp_C_mul_X`, `qDerivative_mul`, and `qDerivative_mul'`.
The q-integer definition and its first six laws need only a semiring;
`one_sub_mul_qInt` and the division-free evaluation identity use a commutative
ring; the coefficientwise linear map, monomial/scaling laws, and both product
rules use a commutative semiring.  Every nome is allowed, including zero and
one; there is no analytic-function or limiting derivative claim.

`PolynomialQLeibniz.lean` has no definition and the four theorems
`comp_C_mul_X_comp_C_mul_X`, `qDerivative_C_mul`,
`qDerivative_iterate_comp_C_mul_X`, and `qDerivative_iterate_mul`.  Every one
holds over an arbitrary commutative semiring, for arbitrary nome and every
natural iteration order including zero, with no division, topology, or
nonvanishing assumption.

`QPochhammerDerivative.lean` has no definition and the three theorems
`hasDerivAt_finiteQPochhammerIn`,
`hasDerivAt_finiteQPochhammerIn_of_ne_zero`, and
`hasDerivAt_finiteQPochhammerIn_comp`.  They work over every nontrivially
normed field with arbitrary nome and finite order.  The cofactor formula is
unconditional; the logarithmic rewrite assumes exactly that every displayed
factor is nonzero; the chain rule assumes exactly the supplied pointwise
`HasDerivAt`.  No infinite-product derivative is added.

`LambertSeriesLog.lean` has no definition and the four theorems
`one_le_norm_natCast_add_one`, `summable_lambert_series`,
`hasSum_lambert_log_complex`, and
`exp_neg_tsum_lambert_eq_qPochhammerInfIn`.  Apart from the unconditional
natural-cast norm helper, they assume exactly complex `a,q` with `‖a‖ < 1`
and `‖q‖ < 1`; they give absolute summability, the `HasSum` against principal
factor logarithms, and the branch-free exponential product identity.  They do
not assert a principal logarithm of the product, a norm-one boundary, or
analytic continuation.

`QGamma.lean` has the two total real definitions `qGamma` and `qNumber` and
the ten theorems `norm_lt_one_of_pos_of_lt_one`,
`qPochhammerInfIn_rpow_pos`, `qPochhammerInfIn_self_pos`, `qGamma_pos`,
`qGamma_one`, `qGamma_add_one`, `qGamma_nat_succ`, `qNumber_natCast`,
`qGamma_mul_qGamma_one_sub`, and `hasSum_theta_qGamma_reflection`.
Positivity, the value at one, recurrence, and natural factorial product use
`0 < q < 1`, with `0 < x` additionally where displayed.  The natural-cast
q-number bridge assumes only `q ≠ 1`; the totalized algebraic reflection
product assumes only `q < 1` and arbitrary real `x`; its theta `HasSum` form
assumes `0 < q < 1` and `0 < x < 1`.  This module supplies no complex
continuation, classical-gamma limit, pole, log-convexity, uniqueness, or
digamma result.

The valuation leaf `PrimePowerBinomialValuation.lean` now contributes no
definitions and exactly six theorems: `primePowerChoose_padicValNat_add`,
`primePowerChoose_padicValNat`, `primePowerSubOneChoose_padicValNat`,
`primePowerSubTwoChoose_padicValNat`, `twoPowChoose_padicValNat`, and
`twoPowSubTwoChoose_padicValNat`.  The first two are the additive and
subtraction forms for an arbitrary prime-power Pascal row.  The third says
every column `j < p^m` in row `p^m-1` is a `p`-adic unit, including `m = 0`.
The fourth identifies the row-`p^m-2`, column-`j-1` valuation with `v_p(j)`
under exactly `0 < j < p^m`; the last two are the strict-interior dyadic
specializations.  No valuation-histogram count is included.
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

The canonical fixed-nome inventory is `QPochhammerEntire.lean`: no public
definitions and exactly five public theorems,
`hasProdLocallyUniformly_complexQPochhammerInf`,
`complexQPochhammerInf_differentiable`,
`complexQPochhammerInf_eq_zero_iff`,
`complexQPochhammerInf_eq_zero_iff_eq_inv_pow`,
and `analyticOrderAt_complexQPochhammerInf_of_eq_zero`.  For a fixed complex
strict contraction `q`, they give locally uniform convergence in the symbol
variable, entireness, the division-free factor-zero criterion, the exact
reciprocal-power zero lattice when `q ≠ 0`, and analytic order one at every
zero under the historical complex-product name.  The raw factor criterion and
order theorem include `q = 0`; the generic-name analytic-order theorem is
owned by `QPochhammerInfinite.lean`.  No joint holomorphy,
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
the legacy compatibility layer, while the generic analytic-order theorem is
canonically owned by `QPochhammerInfinite`.  The named equality bridge
`complexQPochhammerInf_eq_qPochhammerInfIn` is counted in the separate
one-definition/ten-theorem `RvachevPochhammerFactorization.lean` surface.

The synchronized q-series API also retains the full `origin/main` theorem
inventory.  `GaussianBinomialAtNegOneDerivative.lean` is 0+4, and
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
and reciprocal Euler `HasSum` results.  `QPascalSummation.lean` is 0+4:
`sum_gaussianBinomial_succ_mul`, `sum_gaussianBinomial_succ_mul'`,
`Commute.gaussianBinomial_left`, and `Commute.gaussianBinomial_right`.
`QuantumBinomial.lean` is 0+2, namely `quantumPlane_mul_pow` and
`quantum_binomial`.  Finally, the `RogersSzegoPolynomial.lean` 1-definition/9-theorem
tranche covers the zero, row-sum, and successor laws, dilation and three-term
recurrences, the Euler antidiagonal convolution, and
`hasSum_rogersSzego_generating`.  None of these retained APIs is replaced by
the fixed-nome `QPochhammerEntire` layer.

The eight-module increment is exhaustive and contributes 60 public
declarations.  The 0+5 `GaussianBinomialPolynomialStructure.lean` inventory is
listed immediately above.  `GaussianBinomialPalindromic.lean` is 0+14:
`reflect_add_of_natDegree_le`, `reflect_one'`,
`gaussianBinomial_natDegree_le`, `gaussianBinomial_zero_left`,
`gaussianBinomial_diag'`, `reflect_gaussianBinomial`,
`coeff_gaussianBinomial_reflect`, `coeff_gaussianBinomial_zero`,
`coeff_gaussianBinomial_top`, `gaussianBinomial_natDegree`,
`gaussianBinomial_monic`, and
`two_mul_derivative_gaussianBinomial_eval_one`,
`coeff_gaussianBinomial_one_of_pos_of_lt`, and
`coeff_gaussianBinomial_one`.  Its degree bound,
palindromicity, endpoint coefficients, and division-free mean identity hold
over a commutative semiring under exactly `k ≤ n`; coefficient reversal also
uses `j ≤ k*(n-k)`, and exact degree and monicity add `Nontrivial R`.  It does
identify the coefficient of `q` as one under exactly `0 < k < n`, with a
total if-and-only-if classifier covering both boundary and out-of-range cases.

`QExponential.lean` is 3+8.  Its definitions are `qDeriv`, `qExp`, and
`qExpBig`; its theorems are `qFactorial_mul_one_sub_pow`,
`qFactorial_ne_zero`, `qDeriv_mul`, `hasSum_qExp`, `hasSum_qExpBig`,
`qExp_mul_qExpBig_neg`, `qDeriv_qExp`, and `qDeriv_qExpBig`.  The factorial
clearing identity is ring algebra and the function product rule is total.
The series and eigenfunction laws work over a complete normed field under
`‖q‖ < 1`; the small exponential additionally uses
`‖(1-q)*x‖ < 1`, while both eigenfunction statements assume `x ≠ 0`.
`JacksonIntegral.lean` is 1+7: `jacksonIntegral`;
`qDeriv_jacksonIntegral`, `one_sub_mul_pow_mul_qDeriv`,
`tendsto_jackson_sum_qDeriv`, `jacksonIntegral_qDeriv`,
`tendsto_jackson_sum_parts`, `jackson_parts_of_tendsto`, and
`jacksonIntegral_mul_qDeriv`.  The first fundamental theorem assumes exactly
`q ≠ 1`, `x ≠ 0`, and summability of the displayed Jackson series.  The
telescoping identity is unconditional; partial-sum forms use the stated limit,
and `jacksonIntegral` forms add summability.

`ThetaQuasiPeriodicity.lean` is 1+6: `bilateralTheta`;
`thetaExponent_add_one`, `pow_thetaExponent_add_one`,
`hasSum_bilateralTheta`, `bilateralTheta_eq_prod`,
`bilateralTheta_mul_left`, and `bilateralTheta_eq_zero_iff`.  Its sum and
product require a complete normed field, `‖q‖ < 1`, and `z ≠ 0`;
quasi-periodicity and the exact lattice `z = -q^m` additionally require
`q ≠ 0`.  `JacobiCubic.lean` is 0+2:
`two_mul_add_one_le_three_pow` and `hasSum_jacobi_cubic`; the second gives the
complex cubic identity in `HasSum` form under exactly `‖q‖ < 1`.

`QPochhammerLogDerivative.lean` is 0+10:
`one_sub_le_norm_one_sub_mul_pow`,
`summable_pow_div_one_sub_mul_pow`, `summable_log_one_sub_mul_pow`,
`one_sub_mul_pow_ne_zero`, `qPochhammerInfIn_eq_cexp_tsum_log`,
`hasDerivAt_tsum_log_one_sub_mul_pow`,
`hasDerivAt_qPochhammerInfIn`, `hasDerivAt_lambert_series`,
`tsum_neg_pow_div_one_sub_mul_pow_eq`, and
`hasDerivAt_qPochhammerInfIn_lambert`.  The logarithm series is summable for
every complex `a` when `‖q‖ < 1`; reciprocal-factor summability and both final
product derivatives use `‖a‖ < 1`, with termwise differentiation established
on every disk `‖a‖ < r < 1`.  `QPochhammerOrderDerivative.lean` is 0+3:
`hasDerivAt_const_cpow'`, `hasDerivAt_qPochhammerInfIn_mul_cpow`, and
`hasDerivAt_qPochhammerC`.  The first assumes `q ≠ 0`; the latter two assume
exactly `‖q‖ < 1`, `q ≠ 0`, and `‖a*q^α‖ < 1`.  None of these derivative
leaves claims a nome derivative, boundary continuation, or branch-independent
complex-order coordinate.

The cumulative seven-module closure is also exhaustive.  The already listed
`GeneralizedRvachevIdentifiability.lean` contributes `0+6` declarations.
`GeometricPochhammerNormalConvergence.lean` contributes no definitions and
three theorems:
`hasProdLocallyUniformly_geometricSincProduct_complexQPochhammerInf`,
`hasProdLocallyUniformly_rvachevFourierProduct_complexQPochhammerInf`, and
`hasProdLocallyUniformly_rvachevFourier_complexQPochhammerInf`.  The first
assumes exactly complex `‖q‖ < 1` and proves locally uniform convergence on all
of `ℂ` of the outer Pochhammer product, including `q = 0`; the second is the
unconditional dyadic specialization and the third additionally assumes a
bounded Fabius witness and `IsFabius`.  It proves no joint normality in `(q,z)`
or boundary theorem at `‖q‖ = 1`.

`ClassicalPochhammerLimit.lean` contributes no definitions and five theorems:
`ascPochhammer_eval_eq_prod_range`,
`tendsto_one_sub_div_one_sub_of_hasDerivAt`,
`tendsto_finiteQPochhammerIn_div_pow_of_hasDerivAt`,
`tendsto_finiteQPochhammerIn_cpow_div_pow`, and
`tendsto_finiteQPochhammerIn_rpow_div_pow`.  The rising-product identity is
commutative-semiring algebra.  The generic punctured-neighborhood limit works
over every nontrivially normed field under exactly `HasDerivAt f c 1` and
`f 1 = 1`; the complex-principal-power and real-power forms are valid for
every exponent and finite order.  No rate, uniformity, infinite-product limit,
or classical-gamma limit is counted.

`GaussianBinomialUniversal.lean` contributes no definitions and exactly two
theorems, `gaussianBinomial_eq_eval₂_universal` and
`gaussianBinomial_eq_eval_map_universal`.  Over every commutative semiring and
for arbitrary `q,n,k`, they identify `[n,k]_q` with evaluation of the universal
polynomial in `ℕ[X]`, directly or after coefficient mapping.  No degree,
unimodality, log-concavity, or factorization result is added.

`PolynomialQTaylor.lean` contributes two definitions, `qFactorial` and
`qFallingPower`, and eighteen theorems: `qFactorial_zero`,
`qFactorial_succ`, `qDerivative_one`, `qDerivative_iterate_add`,
`qDerivative_iterate_C_mul`, `qDerivative_iterate_sum`,
`qDerivative_iterate_C_mul_X_pow`,
`qDerivative_iterate_eq_zero_of_natDegree_le`, `qFallingPower_zero`,
`qFallingPower_succ`, `qFallingPower_succ'`, `qFallingPower_monic`,
`qFallingPower_natDegree`, `qFallingPower_eval_self`,
`qDerivative_qFallingPower_succ`, `qDerivative_iterate_qFallingPower`,
`prod_qInt_sub_eq_qFactorial`, and `qTaylor`.  The factorial and iterator
algebra are commutative-semiring results, the falling-power layer is over a
commutative ring, and exact degree also assumes nontriviality.  The field-valued
Taylor theorem assumes exactly `[j]_q ≠ 0` for `1 ≤ j ≤ N` and
`f.natDegree ≤ N`.  It is a finite polynomial identity, not an analytic
expansion, remainder estimate, convergence theorem, or `q → 1` result.

`QPartialFractions.lean` contributes the definition `partialFractionCoeff` and
five theorems: `prod_erase_one_sub_inv_pow_mul_pow`,
`finiteQPochhammerIn_self_ne_zero_of_le`,
`partialFractionCoeff_mul_prod_eq_one`,
`sum_partialFractionCoeff_mul_prod_erase`, and
`one_div_finiteQPochhammerIn_eq_sum`.  Over a field, `(q;q)_n ≠ 0` suffices for
the polynomial identity and includes `q = 0`; the pointwise reciprocal formula
also assumes every displayed pole factor nonzero.  The two normalization
helpers state their explicit `q ≠ 0` and index hypotheses.  There is no
infinite expansion, repeated-pole theory, or convergence claim.

`QPochhammerIntegerIndex.lean` contributes the definitions `qIntervalProd` and
`finiteQPochhammerZ` and fifteen theorems: `Ico_int_eq_image_range`,
`prod_Ico_int_eq_prod_range`, `qIntervalProd_of_le`, `qIntervalProd_of_lt`,
`qIntervalProd_self`, `qIntervalProd_symm`, `qIntervalProd_trans_of_le`,
`qIntervalProd_trans`, `finiteQPochhammerZ_natCast`,
`finiteQPochhammerZ_neg_natCast`, `prod_Ico_add_zpow`,
`qIntervalProd_add_eq`, `finiteQPochhammerZ_add`,
`finiteQPochhammerZ_add_one`, and `finiteQPochhammerZ_neg_natCast_eq`.
The ordered cocycle is unconditional; the all-order cocycle assumes its two
factors nonzero.  Translation and concatenation require `q ≠ 0`, concatenation
also requires both factors nonzero, the one-step shift requires its two
displayed nonzero factors, and the closed negative-index form requires
`a ≠ 0` and `q ≠ 0`.  Empty intervals and natural/negative-natural indices are
included; no continuation in the index or root-of-unity regularization is
claimed.

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
layers remain outside this tranche.  The live baseline records zero missing
headers and zero missing doc comments.  Future source additions must preserve
both zero-gap invariants.  Run the script for live numbers after merging
concurrent source work.

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

Four direct artifact receipts record the last synchronized pre-9135 source/PDF
pairs and are now historical because the live sources include the new
q-Chu/reversal, geometric-generating, Gaussian second-moment, and Lambert
branch-gap Bernoulli APIs.  The primary receipt is a
14,037-line, 702,119-byte TeX source
(SHA-256
`6a20e02cf300c0b29ba8d175831b4f86e4b336601cc5bd5f5752d5c5889be69a`)
and a 197-page, 1,602,500-byte PDF (SHA-256
`f083cd78308aba99d23d42372786c4b0a946ea8f5d47445c44d664fccfdde5e3`).
The Lean-walkthrough receipt is a 6,598-line, 465,231-byte TeX source (SHA-256
`796dd849fa423ba07413eaf0a1f30dc608355c5a3cd877aa7409ad089c54794e`)
and a 149-page, 1,231,442-byte PDF (SHA-256
`bc6e3e716a1a10daf24a065f6c97e2d00cbc95071ada777050a95f91598db4a0`).
The canonical-frontier receipt is a 17,954-line, 813,297-byte TeX source
(SHA-256
`bcd9eefce2ead08e2cbb283e091a859aa31f36c67416543e994e10e8f9db3075`)
and a 262-page, 1,885,642-byte PDF (SHA-256
`7f7e1279e38c766a465e640638ea7e0079a942de0bc84a5c22be497af27c7bab`).
The q-series receipt is a 16,834-line, 837,715-byte TeX source (SHA-256
`4785625c1399558f3ca59481888fc76514e0a327a1faa16945c61851f874f3d5`)
and a 395-page, 2,494,961-byte PDF (SHA-256
`89159b2635f489a42d4c972fac95332808b1d637dee7921085db1ed7d6e055af`).
Their exact successful three-pass page sequences were respectively
194→197→197, 144→149→149, 254→262→262, and 386→395→395.  Primary and
walkthrough logs and publication gates are clean; the frontier retains only
expected underfull diagnostics, and the q-series master retains one harmless,
readable 32.5659 pt overfull line.  All page, metadata, font, render, text,
and representative-visual gates passed.  These receipts certify their named
pre-9135 pairs, not parity with the 903/11,448 live union; all four publications
require new final-source rebuilds.

The independently scoped Sequence publication remains current.  The Lambert
guide's last synchronized receipt is a 4,829-line, 174,423-byte TeX with SHA-256
`724dfe5b1effcda29325a5bdfb066ff970eb74ab460f650185339fefce40ebc1`;
its 69-page, 952,929-byte PDF has SHA-256
`0b5f28dbfe590658e74150e8ccff6f023ecd0b8fb4e3e978ec275d9ddd244de6`.
Its successful page sequence was 67→69→69; machine and visual gates passed,
with expected underfull diagnostics and one harmless readable 0.825 pt
internal overfull line.  The new Bernoulli-series source overlay makes that
Lambert PDF historical pending a parity rebuild.  The Sequence
inversion/transseries volume's
16,705-line, 778,477-byte TeX has SHA-256
`4aa038c10ddd931b7c1248095ddfdf0ce8769c69cc0df4f344f6365d0e45e8e1`;
its 205-page, 2,198,655-byte PDF has SHA-256
`ec1f4d2ac608786f33be97d040fdfd03b6f74494dee74f044fd2e6631217d4fb`.
Its successful page sequence was 198→205→205; corrected title/author metadata,
machine gates, and extensive visual checks passed.  The final log retains one
duplicate-page-destination notice, nine PDF-string notices, 47 overfull and
12 underfull diagnostics; sampled largest cases are clean and unclipped.

For provenance, the superseded pre-d8b pairs remain historical receipts:
primary TeX/PDF `938517a92565685ac9f7194b879cfe752ce783f258bde8b7b685aee41aed13dc` /
`bf26d78dd2cc49feb87a85413ef9c04c7a8a3dac4f793cf86e3436f7502cb2a7`
(694,350 / 1,593,577 bytes; 195 PDF pages); walkthrough
`e598aa02d4d10eda8bcfdafe3731f4a663bdcba58407f454485fae6796b41050` /
`5ff79c24fbced37dfaa5eb9c34447d0e7661b2b2bc5a0597687e43f93d7e189a`
(456,855 / 1,219,336 bytes; 145 pages); frontier
`7dd140370a0ac68522364a83a3c6423df93570741eafaef2ee8c1fac17670e2f` /
`9d38ab9d43befd6e26fd06ab9680b4a761365fb9d8a9f0de18489c243bd62d3e`
(808,185 / 1,877,159 bytes; 260 pages); and q-series
`d8f730b8eb6602d4d16112aea77a3e67dfbeadf46bcd28c1cdf3b12450b7d4fb` /
`5d25df07e6df1cd32118ee87e64c1cc54ad32da7c578a182231f98dd9fee9d5c`
(837,715 / 2,494,949 bytes; 395 pages).

The retained comb-interpolation synthesis PDF is a validated 158-page A4
historical receipt: the current source includes a post-render update to its
additive-dyadic chapter, so a fresh parity build remains pending.  The rebuilt
Integration-and-Transform master retains a historical 377-page PDF.  The canonical
q-series synthesis is a validated 389-page historical receipt synchronized to
the immediately preceding source checkpoint.  The current merged source adds
the terminating q-Chu/reversal, geometric-generating, Gaussian second-moment,
and Lambert branch-gap Bernoulli tranches, so final parity is again pending.
The retained 183-page primary, 130-page walkthrough, 257-page canonical
frontier, 69-page Lambert Guide, 301-page Representation Frontiers, 41-page
New Frontiers, and 88-page notation-catalogue artifacts likewise predate their
current merged sources.  Their package notices treat those PDFs as historical
validation receipts, not parity claims, until fresh uninterrupted three-pass
builds complete.  The inverse-computability receipt likewise still reflects
the historical 675/8,909 census and requires refresh against the live
903/11,448 inventory.  Checksum ledgers remain abolished and hardened
repository-wide; no `SHA256SUMS*` files exist or participate in validation.
The canonical inverse-theory publication retains a 134-page
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

## Ongoing documentation maintenance

1. Any new file: header and doc comments at the time of writing.  The ratchet
   gate makes this cheap to enforce.
2. Run the audit after each source tranche and update the checked baseline only
   after reviewing the reported declarations.
3. Keep comments on declarations cited by `PAPER_COVERAGE.md` synchronized
   with their exact proved strength, since those are the ones an outside reader
   reaches first.
4. Review long interior estimate chains when they change, ideally while their
   local proof structure is still fresh.

Adding a doc comment cannot change elaboration, so this work needs no build
slot.  On a machine where a full rebuild costs the better part of a day, that
makes it unusually good value.
