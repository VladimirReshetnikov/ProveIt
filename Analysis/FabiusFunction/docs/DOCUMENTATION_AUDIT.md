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

The authoritative live post-merge 2026-09-01 lexical inventory contains 659
modules and 8,769 public declarations, with zero missing module headers and
zero missing doc comments.  Relative to the 649/8,698 checkpoint, the exact
tree union adds ten modules and 71 declarations.  Relative to the 610/8,318
activation checkpoint it adds forty-nine modules and 451 declarations;
relative to the 634/8,589 q-calculus checkpoint it adds twenty-five modules and
180 declarations; relative to the 641/8,652 documentation union it adds
eighteen modules and 117 declarations; and relative to the earlier 630/8,552
merged checkpoint it adds twenty-nine modules and 217 declarations.  These are
tree-union comparisons, not claims of a single linear history.

The retained q-series surface includes the Gaussian-continuity,
Jacobi/pentagonal, infinite-q-binomial, q-Pascal, quantum-binomial,
Rogers--Szegő, polynomial Jackson/q-Leibniz, finite-Pochhammer derivative,
Lambert-series, real-q-gamma, finite/infinite Pochhammer, classical-limit,
normal-convergence, q-Taylor, q-partial-fraction, integer-index, Heine,
q-Gauss, complex-order, uniform-bound, basic-hypergeometric, q-multinomial,
generic Gaussian-palindromic, Jackson-integral, q-exponential,
bilateral-theta, Jacobi-cubic, Pochhammer-log-derivative,
Pochhammer-order-derivative, central-Gaussian-reduction, and cyclotomic
factorization modules.  The unconditional
`complexQPochhammerInf_eq_qPochhammerInfIn` bridge remains in the exhaustive
1+10 `RvachevPochhammerFactorization` surface; the generic analytic-order
theorem is canonically owned by the exhaustive 1+29
`QPochhammerInfinite` surface; `QPochhammerEntire` remains the five-theorem
legacy compatibility layer; `QMultinomial` remains 1+9; and
`GaussianBinomialPolynomialStructure` is 0+5, including its inline-attributed
constant-coefficient theorem.  The two newest algebra leaves add thirteen
theorems and no definitions: `CentralQBinomialReduction.lean` 0+6 and
`CyclotomicFactorization.lean` 0+7.  Older census values below are historical
checkpoints, not descriptions of the live tree.  The contemporaneous
`JacobiTripleProduct.thetaCoeff_pair_eq` edit only renames an unused proof
binder and changes no public declaration or count.  The branch-point geometry
and
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
leaves contribute 36 declarations and bring one historical branch to its
649/8,697 pre-union census.  The corresponding checkpoint in the current
audited tree union is 649/8,698.  The four subsequent leaves contribute 38
declarations and bring that union to 653/8,736; the next four contribute twenty
and bring it to 657/8,756; and the final two contribute thirteen and give the
live 659/8,769 census recorded above.

That increment is exhaustively counted as
`QPochhammerInfiniteBounds.lean` 0+5, `HeineTransformation.lean` 2+5,
`QGaussSummation.lean` 0+2, `QPochhammerComplexOrder.lean` 1+4,
`BasicHypergeometricSeries.lean` 2+5, and `QMultinomial.lean` 1+9: six
definitions and thirty theorems.  It adds finite-prefix bounds, the Heine and
q-Gauss identities, a ratio-defined complex-order q-Pochhammer API, general
basic-hypergeometric terms and summability, and the division-free recursive
q-multinomial interface.  The displayed contraction, nonvanishing, and
denominator hypotheses remain part of these APIs.
The final four-module increment is exhaustively counted as
`GaussianBinomialPalindromic.lean` 0+12, `JacksonIntegral.lean` 1+7,
`QExponential.lean` 3+8, and `ThetaQuasiPeriodicity.lean` 1+6.  It adds the
degree, monicity, coefficient-reversal, and division-free mean theory of the
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

The exhaustive six-theorem `CentralQBinomialReduction.lean` surface is
`finiteQPochhammerIn_mul_neg`, `finiteQPochhammerIn_two_mul`,
`finiteQPochhammerIn_map_ringHom`,
`central_gaussianBinomial_sq_mul_int`,
`central_gaussianBinomial_sq_mul`, and
`central_gaussianBinomial_sq_div`.  The first three and the division-free
central identity hold over commutative rings with no nonvanishing, division,
positivity, or nontriviality premise, so the zero ring and the boundaries
`n=0`, `k=0`, and `q=0` are included.  The cancellation proof is first made in
`ℤ[X]` and then transported by the ring-hom naturality theorem.  Only the
quotient form moves to a field and assumes exactly
`finiteQPochhammerIn (-q) q (2*k) ≠ 0` and
`finiteQPochhammerIn (q^2) (q^2) k ≠ 0`.  This finite algebra supplies no
infinite-product, convergence, root-of-unity regularization, or asymptotic
claim.

The exhaustive seven-theorem `CyclotomicFactorization.lean` surface is
`div_add_div_le_div`, `div_le_div_add_div_add_one`,
`mem_range_and_mem_divisors_iff`,
`finiteQPochhammerIn_X_eq_prod_cyclotomic`,
`finiteQPochhammerIn_X_eq_gaussianBinomial_mul`,
`prod_cyclotomic_pow_div_extend`, and
`gaussianBinomial_X_eq_prod_cyclotomic`.  The two floor-division bounds assume
exactly `k ≤ n` and `0 < d` and bound each Gaussian cyclotomic exponent between
zero and one; the range/divisor exchange is total in `n,j,d`.  The shifted
factorial factorization holds over every commutative ring, including the zero
ring and `n=0`; the factorial/Gaussian bridge assumes exactly `k ≤ n`, and the
product extension exactly `m ≤ n`.  The terminal Gaussian factorization
assumes exactly `k ≤ n` and `[IsDomain R]`.  It makes no statement for `k>n`,
at a specialized root of unity, about coefficient unimodality, or about
asymptotics.

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
theorem assumes a computable positive reciprocal inverse modulus.  It does not
formalize the canonical report's stronger gap-to-modulus theorem, which starts
from a computable positive gap sequence and also derives effective uniform
continuity.

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
`GaussianBinomialPalindromic.lean` is 0+12:
`reflect_add_of_natDegree_le`, `reflect_one'`,
`gaussianBinomial_natDegree_le`, `gaussianBinomial_zero_left`,
`gaussianBinomial_diag'`, `reflect_gaussianBinomial`,
`coeff_gaussianBinomial_reflect`, `coeff_gaussianBinomial_zero`,
`coeff_gaussianBinomial_top`, `gaussianBinomial_natDegree`,
`gaussianBinomial_monic`, and
`two_mul_derivative_gaussianBinomial_eval_one`.
`GaussianBinomialPolynomialStructure.lean` is 0+5:
`natDegree_gaussianBinomial_universal`,
`gaussianBinomial_universal_monic`,
`coeff_zero_gaussianBinomial_universal`,
`gaussianBinomial_universal_reflect`, and
`coeff_gaussianBinomial_universal_symm`; the count includes the inline
`@[simp] theorem` declaration `coeff_zero_gaussianBinomial_universal`.  The
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

The final eight-module increment is exhaustive and contributes 58 public
declarations.  The 0+5 `GaussianBinomialPolynomialStructure.lean` inventory is
listed immediately above.  `GaussianBinomialPalindromic.lean` is 0+12:
`reflect_add_of_natDegree_le`, `reflect_one'`,
`gaussianBinomial_natDegree_le`, `gaussianBinomial_zero_left`,
`gaussianBinomial_diag'`, `reflect_gaussianBinomial`,
`coeff_gaussianBinomial_reflect`, `coeff_gaussianBinomial_zero`,
`coeff_gaussianBinomial_top`, `gaussianBinomial_natDegree`,
`gaussianBinomial_monic`, and
`two_mul_derivative_gaussianBinomial_eval_one`.  Its degree bound,
palindromicity, endpoint coefficients, and division-free mean identity hold
over a commutative semiring under exactly `k ≤ n`; exact degree and monicity
add `Nontrivial R`.

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
layers remain outside this tranche.  The baseline records zero missing headers
and zero missing doc comments, so every future source addition must preserve
that invariant.  Run the script for
live numbers after merging concurrent source work.

The additional declaration in `PolynomialCombExactness.lean` is
`integral_polynomial_mul_rvachevUp_eq_dyadic_tsum`, the exact normalized
physical-coordinate self-sampling quadrature for every real polynomial whose
natural degree is at most the dyadic level and every real phase.

The effective-inverse tranche contributes two modules and nine public
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
an exact least endpoint-mass denominator.

Every committed PDF in this documentation family is a historical validation
receipt and remains rebuild-pending.  Package-local page counts describe
artifacts rendered at earlier source checkpoints; none is a parity claim for
the present 659-module, 8,769-declaration union.  This applies to the retained
comb-interpolation, Integration-and-Transform, canonical q-series, primary,
walkthrough, canonical-frontier, Representation Frontiers, New Frontiers,
notation-catalogue, inverse-computability, and inverse-theory artifacts.  Fresh
uninterrupted three-pass parity builds are required after the merged q-series,
q-calculus, Pochhammer-limit, normal-convergence, integer-index,
partial-fraction, identifiability, valuation, Heine, q-Gauss, complex-order,
basic-hypergeometric, q-multinomial, Gaussian-palindromic, Jackson-integral,
q-exponential, theta, Jacobi-cubic, Pochhammer-derivative, central-Gaussian,
cyclotomic, and effective-inversion updates.

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
