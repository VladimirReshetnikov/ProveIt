# Finite-demand source-claim audit

This audit covers all 17 theorem, lemma, proposition and corollary environments
in [`foundations/ipra_finite_demand`](../docs/proofs/foundations/ipra_finite_demand/).
It records actual object-theory results and remaining mathematical obligations,
alongside the full [packet progress index](PROGRESS.md). The delivered packet
is preserved.

**Checked** means that the displayed scope has a genuine `Prf PRAAx` derivation.
An externally fixed formula or PR program is a proof-generator parameter;
ordinary numerical inputs remain object-language variables. Conditional
derivations retain their hypotheses. **Partial** identifies useful proved
components without crediting the whole source claim. **Open** means that no
completed object endpoint for that claim is identified here. Native Lean
lemmas, target propositions, executable examples and successful compilation of
an unproved target are distinct from object-theory derivations.

The delivered [formalization account](../docs/proofs/foundations/ipra_finite_demand/sections/06_formalization.tex)
already makes this distinction: its native scheduling/Hausdorff proofs and its
aggregate/root/norm target definitions describe the archive, not the current
ordinary iPRA implementation.

## Every theorem environment

Implementation links are relative to `Lean/IPRADerivations`. Names have prefix
`LeanProofs.IPRA.Foundations` unless another area is specified.

| Source label and location | Current exact scope | Remaining mathematical work |
| --- | --- | --- |
| `lem:booleanization`, [01_framework.tex](../docs/proofs/foundations/ipra_finite_demand/sections/01_framework.tex) | **Checked fixed-syntax family.** [BoundedSyntax](Lean/IPRADerivations/Foundations/BoundedSyntax.lean) provides arity-indexed `BFm n`, literal `formula`, capture-avoiding `formula_subst`, an actual n-ary `bitF`, `compile_correct`, arbitrary-term/context `bounded_reflection`, `bit_zero_iff`, `bounded_decidable`, and closed `boolean_reflection_closed`/`boolean_program_closed`. [BoundedFormulas](Lean/IPRADerivations/Foundations/BoundedFormulas.lean) supplies the checked packed fold/search backend. | No mathematical remainder for the implemented bounded grammar. Application-specific source syntax and code representations need their own interpretation, rather than an internal universal evaluator. |
| `thm:backward-transfer`, [02_backward_induction.tex](../docs/proofs/foundations/ipra_finite_demand/sections/02_backward_induction.tex) | **Checked conditional object family.** [BackwardDemand](Lean/IPRADerivations/Foundations/BackwardDemand.lean) constructs `backwardF`, `backward`, `horizon`; proves `backward_zero`, `backward_succ`, `horizon_final`, `horizon_step`; and proves `transfer` and closed `backward_transfer`. A single initial observation and the genuine local-step contract yield the terminal observation, without monotonicity or cap assumptions. | No mathematical remainder for fixed bounded observations in the packed representation. Translate other observation representations explicitly. |
| `cor:observational-induction`, [02_backward_induction.tex](../docs/proofs/foundations/ipra_finite_demand/sections/02_backward_induction.tex) | **Checked conditional object family.** `BackwardDemand.observational_induction` and `observational_induction_closed` derive all numerical stages/demands from global base and local-step contracts. | The client must prove those contracts. They are not silently inferred from the existence of an intended represented object. |
| `thm:parameter-changing-recursion`, [02_backward_induction.tex](../docs/proofs/foundations/ipra_finite_demand/sections/02_backward_induction.tex) | **Checked actual PR construction.** [ParameterChangingRecursion](Lean/IPRADerivations/Foundations/ParameterChangingRecursion.lean) defines the two-pass evaluator and explicit `compiledF : PR 3`. `backward_coherence`, `horizon_coherence`, `forward_coherence`, `compiled_program_zero`, `compiled_program_succ`, and closed `zero_equation`/`successor_equation` prove the actual changing-parameter equations. | No mathematical remainder for fixed predetermined PR `b`, `D`, `F`. Adaptive unbounded recursion whose next demand depends on an uncomputed output is outside this theorem. |
| `cor:finite-query-induction`, [02_backward_induction.tex](../docs/proofs/foundations/ipra_finite_demand/sections/02_backward_induction.tex) | **Checked actual envelope and object induction.** [FiniteQueryDemand](Lean/IPRADerivations/Foundations/FiniteQueryDemand.lean) constructs the nested PR maximum, proves `query_le_envelope` and closed `finite_query_envelope`, derives the actual bounded-prefix translation/local step, and proves `finite_query_induction_closed` for the original arity-indexed source observation. Query counts and upper limits are internal and may be nonmonotone; empty maxima are zero. | No mathematical remainder for the stated fixed-program/bounded-observation schema. Concrete applications must prove their actual global base and multiple-query local contracts. |
| `thm:nonlinear-name-validity`, [02_backward_induction.tex](../docs/proofs/foundations/ipra_finite_demand/sections/02_backward_induction.tex) | **Checked actual rational iteration.** [Analysis/LogisticName](Lean/IPRADerivations/Analysis/LogisticName.lean) proves clipping nonexpansiveness, logistic range/Lipschitz4, positive denominators, actual PR5 program linkage, closed `parameter_shift_closed`, `nonlinear_name_validity_closed` and `globally_regular_output_closed`. The finite input premise is exactly bounded observations through `K+2N`; parameter `A/B` is internal with `B>0`, `A≤4B`. | No mathematical remainder for the finite source theorem and its global-regularity corollary in the declared signed rational coding. Completed-real interpretation and different external name encodings need their own adapters. |
| `lem:aggregate-calculus`, [03_aggregates.tex](../docs/proofs/foundations/ipra_finite_demand/sections/03_aggregates.tex) | **Checked all five finite estimates in the original rational-coordinate coding.** [Analysis/RationalHausdorff](Lean/IPRADerivations/Analysis/RationalHausdorff.lean) supplies the actual independent-denominator values, original-coordinate cover equivalence and PR checker, using [RationalSupMetric](Lean/IPRADerivations/Analysis/RationalSupMetric.lean) normalization. [Triangle](Lean/IPRADerivations/Analysis/RationalHausdorffTriangle.lean), [Concat](Lean/IPRADerivations/Analysis/RationalHausdorffConcat.lean), [Product](Lean/IPRADerivations/Analysis/RationalHausdorffProduct.lean), [Image](Lean/IPRADerivations/Analysis/RationalHausdorffImage.lean) and [PointDistanceVariation](Lean/IPRADerivations/Analysis/RationalPointDistanceVariation.lean) prove the five literal source estimates, from actual constructors/nearest witnesses, and acceptance of the output checkers. Product factors and the output retain their independent scales; images use only the genuine finite cross-pair Lipschitz law. | No mathematical remainder for these five estimates in this coding. Cartesian products retain the legitimate bounded stored point-length guards for the two runtime factor dimensions; other arithmetic uses the documented total first-d/e decoder. Image evaluators are fixed PR schemas; all dimensions, Lipschitz numerators/positive denominators and persistent parameters are internal. Other external coding formats need their own explicit adapters. This does not assert an internal universal interpreter for arbitrary PR metric or map codes. |
| `thm:aggregate-chain`, [03_aggregates.tex](../docs/proofs/foundations/ipra_finite_demand/sections/03_aggregates.tex) | **Checked actual rational point constructor.** [Analysis/RationalNearest](Lean/IPRADerivations/Analysis/RationalNearest.lean) supplies the actual least original-list neighbor. [Analysis/AggregateChain](Lean/IPRADerivations/Analysis/AggregateChain.lean) supplies PR5 index/name/distance/neighbor programs, QF membership and per-coordinate sharp-tail inductions, `aggregate_chain_closed`, `sharp_tail_closed`, `distance_regular_closed`, `chain_programs_closed` and `name_length_closed`. The actual `q_(s+t+2)` output is regular and every sample stays within `3e_s` of the seed. Its actual nearest-distance sample uses `q_(s+k+3)` against `S_(k+1)` and satisfies `8·2^k·num≤5·den`, with positive computed denominator, an actual nearest witness and derived scalar-name coherence. | No mathematical remainder for the source finite-observation theorem in this rational coding. Fixed list evaluator is external; dimension, seed/stage/precision indices and persistent data are internal. Stored dimension follows from the legitimate input `shaped` contract; stronger arithmetic estimates use the explicitly documented total first-`d` decoder. Malformed/empty inputs inherit raw entry/nearest totalization and are not promised the packet's suggested zero-vector default. Completed-real interpretation and other name encodings need separate adapters; no arbitrary choice function is asserted. |
| `thm:aggregate-optimization`, [03_aggregates.tex](../docs/proofs/foundations/ipra_finite_demand/sections/03_aggregates.tex) | **Checked full finite-name construction.** [Analysis/AggregateOptimization](Lean/IPRADerivations/Analysis/AggregateOptimization.lean), with [RationalArgmin](Lean/IPRADerivations/Analysis/RationalArgmin.lean), [RationalValueBounds](Lean/IPRADerivations/Analysis/RationalValueBounds.lean), [RationalPointDistance](Lean/IPRADerivations/Analysis/RationalPointDistance.lean) and the checked chain, constructs actual signed-rational value, witness, supremum and evaluator programs. Proves minima Cauchy bounds, regularity, support and the exact `(4L+2)` budget for runtime `L=A/B`, `B≥1`. Explicit coarse PR shifts discharge all shift-existence obligations. Arbitrary-support distance bounds and a final computed-precision integer-gap step prove literal `LeNamed0`; `named_bounds_closed` contains both infimum-lower and supremum-upper statements. Closed metadata and the main/coarse/supremum constructors retain all numerical data internally. | No mathematical remainder for the stated global approximate-map contract and chosen finite rational coding. List, map and competitor point evaluators are fixed PR schemas; dimension, Lipschitz data, precisions, bounds and persistent parameters are internal. Support is the actual computed point-distance zero observation predicate; it is not a supplied lower-bound law. Stored lengths use the legitimate separate input `shaped` contract. Completed-real/native-archive presentations and alternative invariant-domain contracts require their explicit adapters. No exact minimizing point or coherence across separately chosen minimizers is asserted. |
| `lem:product-stability`, [04_root_sets.tex](../docs/proofs/foundations/ipra_finite_demand/sections/04_root_sets.tex) | **Checked full original Gaussian-rational pair coding.** [GaussianRationalStability](Lean/IPRADerivations/Analysis/GaussianRationalStability.lean) `original_product_stability_closed` proves both original Euclidean covers; `original_product_checker_closed` gives actual checker acceptance and `original_product_witness_closed` certifies the PR6 returned original target entry. The actual [normalization](Lean/IPRADerivations/Analysis/GaussianRationalNormalization.lean), [radius/budget](Lean/IPRADerivations/Analysis/GaussianRationalRadius.lean), [original-cover](Lean/IPRADerivations/Analysis/GaussianRationalCover.lean), [rational metric](Lean/IPRADerivations/Analysis/GaussianRationalMetric.lean) and [Horner](Lean/IPRADerivations/Analysis/GaussianRationalHorner.lean) bridges connect independent original component denominators to the [common-D theorem](Lean/IPRADerivations/Analysis/GaussianRationalProductStability.lean). Actual [product polynomials](Lean/IPRADerivations/Analysis/GaussianRootProduct.lean), [coefficient scaling](Lean/IPRADerivations/Analysis/GaussianPolynomialScaling.lean), [perturbation](Lean/IPRADerivations/Analysis/GaussianPolynomialPerturbation.lean) and [norm/factor search](Lean/IPRADerivations/Analysis/GaussianProductNorm.lean) derive every intermediate conclusion. | No mathematical remainder for this source lemma in the explicit pair coding. All nine numerical inputs are internal: original lists, degree, radius `u/v≥1`, coefficient tolerance `A/B≥0` and output radius `P/Q≥0`. The exact source condition `Q^N N u^(N−1) A≤P^N B v^(N−1)` is retained. Repeated roots and zero tolerances are allowed; no canonical-storage, positive-tolerance, supplied factorization/evaluation/clearing, successful-search or target-cover premise is added. This proves support closeness and does not assert a multiplicity-preserving matching or root existence. |
| `thm:approx-factor`, [04_root_sets.tex](../docs/proofs/foundations/ipra_finite_demand/sections/04_root_sets.tex) | **Checked full actual uniform construction with a concrete monic instance.** [GaussianApproximateFactorization](Lean/IPRADerivations/Analysis/GaussianApproximateFactorization.lean) proves `uniform_approximate_factorization_closed`, `returned_approximate_factorization_closed` and `returned_product_evaluation_closed`. The actual PR4 returns N computed roots and the actual degree-N product coefficients, with full coefficient L1 error≤eta=p/q. Numerical C,N,p,q are internal. [Parameters](Lean/IPRADerivations/Analysis/GaussianFactorParameters.lean) computes A0 and epsilon=p/(2NLq); [stage bounds](Lean/IPRADerivations/Analysis/GaussianFactorBounds.lean) derives the whole coefficient invariant by compiled bounded induction and each root radius using the proved [monic residual-radius theorem](Lean/IPRADerivations/Analysis/GaussianMonicResidualRadius.lean). Actual [linear multiplication/error transport](Lean/IPRADerivations/Analysis/GaussianRationalDeflationError.lean), [product reconstruction](Lean/IPRADerivations/Analysis/GaussianRationalReconstruction.lean) and [weighted budgets](Lean/IPRADerivations/Analysis/GaussianWeightedErrorBudget.lean) give the complete backward QF error proof. | No mathematical remainder for this conditional theorem in the stated coding: the input is a coefficient list of length N+1 with literal canonical leading coefficient one, N≥1 and 1≤p≤q. The additional premise is precisely `GaussianFactorParameters.monicRD`, a uniform local contraction for proper monic polynomials, from which stage residuals are derived. The concrete fixed step is now constructed in [GaussianMonicRD](Lean/IPRADerivations/Analysis/GaussianMonicRD.lean), and [GaussianMonicApplications](Lean/IPRADerivations/Analysis/GaussianMonicApplications.lean) proves the actual and returned approximate-root/factorization instances with that RD premise discharged internally. The generic interface retains its step argument; the general nonmonic FTA remains separate. The [literal (TE) coefficient identity](Lean/IPRADerivations/Analysis/GaussianDeflationResidualPolynomial.lean) is also checked for the actual computed roots and residuals. The [general convolution norm bound](Lean/IPRADerivations/Analysis/GaussianRationalConvolutionNorm.lean) holds for the actual product. The alternative bounded-grid interface remains open. The coefficient-error estimate uses the actual one-step error recurrence and backward prefix-weighted induction. Root existence, desired factorization/error and global stage invariants are not premises. |
| `thm:root-support`, [04_root_sets.tex](../docs/proofs/foundations/ipra_finite_demand/sections/04_root_sets.tex) | **Checked full source construction with a concrete fixed-step instance.** [GaussianRootSupport](Lean/IPRADerivations/Analysis/GaussianRootSupport.lean) proves `collision_tolerant_root_support_closed`, the original two-cover checker and the actual PR3 root-name program. [GaussianCoefficientNameBounds](Lean/IPRADerivations/Analysis/GaussianCoefficientNameBounds.lean), [GaussianRootSchedule](Lean/IPRADerivations/Analysis/GaussianRootSchedule.lean), [GaussianRootSamples](Lean/IPRADerivations/Analysis/GaussianRootSamples.lean), [GaussianRootRadius](Lean/IPRADerivations/Analysis/GaussianRootRadius.lean) and [GaussianRootCoefficientCoherence](Lean/IPRADerivations/Analysis/GaussianRootCoefficientCoherence.lean) construct exact source A/R/b/E(t), actual sample/factor programs, final coefficient radius A, listed-root radius A+2 and coefficient discrepancy 4*2^-E(t). [GaussianRootStability](Lean/IPRADerivations/Analysis/GaussianRootStability.lean) derives both original Euclidean covers at 2^(-t-2). Numerical degree, data and all precisions are internal; only fixed PR schemas are external. | No mathematical remainder for this source result in the chosen coding. The generic interface retains the local monic RD contract; [GaussianMonicRootSupport](Lean/IPRADerivations/Analysis/GaussianMonicRootSupport.lean) discharges it using the proved fixed step and exports `concrete_root_support_closed`, actual named/returned covers and checker acceptance. Only genuine CN, positive degree and stage order remain. The original root-name PR3, coefficient errors, radii, product evaluation, listed zeros and returned fields are audited. No final radius, factorization/coherence law, root separation or cover is an input premise. |
| `prop:root-adequacy`, [04_root_sets.tex](../docs/proofs/foundations/ipra_finite_demand/sections/04_root_sets.tex) | **Checked full source proposition and concrete completed-distance instance.** [GaussianRootAdequacyTheorem](Lean/IPRADerivations/Analysis/GaussianRootAdequacyTheorem.lean) proves the single closed `root_adequacy_closed` sentence: actual P-value fastness, literal quantified Member iff actual polynomial-program zero, all-stage nonnegative fast Euclidean distance names, both sharp represented error cuts and the source PR forward stage at every precision. [SharpEvaluation](Lean/IPRADerivations/Analysis/GaussianRootSharpEvaluation.lean) proves `root-eval-error` at exact 2*C_Z/D; [SharpDistance](Lean/IPRADerivations/Analysis/GaussianRootSharpDistance.lean) proves `root-distance-residual` as the genuine two-name order cut at exact M_Z/C_R. The original Z is retained; sample disk Z+1 is derived from its represented norm bound. All degrees, data, stages and precision indices are internal. [Actual power envelopes](Lean/IPRADerivations/Analysis/GaussianRationalPowerEnvelope.lean), [rational-disk Lipschitz](Lean/IPRADerivations/Analysis/GaussianRationalHornerRadiusLipschitz.lean), [finite slack removal](Lean/IPRADerivations/Analysis/GaussianFastValueCut.lean), [distance upper cuts](Lean/IPRADerivations/Analysis/GaussianEuclideanDistanceUpperCut.lean) and [actual affine distance names](Lean/IPRADerivations/Analysis/GaussianLinearDistanceName.lean) supply derived components. | No mathematical remainder for the displayed proposition in the chosen original rational/name coding under its genuine CN/pointCN, numerical disk/degree and local RD assumptions. The later unnumbered stage-distance/zero-distance corollary is checked by [DistanceCompletion](Lean/IPRADerivations/Analysis/GaussianRootDistanceCompletion.lean) and [DistanceZero](Lean/IPRADerivations/Analysis/GaussianRootDistanceZero.lean); [CompletedAdequacy](Lean/IPRADerivations/Analysis/GaussianRootCompletedAdequacy.lean) identifies its literal zero predicate with literal P-program zero. [GaussianMonicRootAdequacy](Lean/IPRADerivations/Analysis/GaussianMonicRootAdequacy.lean) now exports the full original proposition and completed corollary with RD discharged internally, retaining original C_Z/M_Z and genuine CN/pointCN/disk/degree guards. It binds the actual PR3 root and PR2 polynomial/distance names and proves membership iff actual polynomial-name zero iff completed distance-name zero. Distance completion and its membership equivalence require only CN, pointCN and positive degree. Generic completed Gaussian-point and field realization remains separate. No desired error/coherence/order, represented minimizing root or output invariant is an input. |
| `thm:general-norm`, [05_norm_certificates.tex](../docs/proofs/foundations/ipra_finite_demand/sections/05_norm_certificates.tex) | **Checked sharp finite norm zero bound in the exact Gaussian-rational coding.** [GaussianNormFiniteZeroBound](Lean/IPRADerivations/Analysis/GaussianNormFiniteZeroBound.lean) proves `actual_finite_norm_zero_bound_closed` for the original norm and original distinct common-zero list. The only arithmetic and source guards are the monic input shape, the original point predicates and the actual nonzero coefficient flag of the returned norm. Its conclusion uses the actual computed degree. [The reconstruction theorem](Lean/IPRADerivations/Analysis/GaussianNormFiniteZeroBound.lean) derives bounded literal coefficient equality at every group prefix before applying the nonzero flag. Its two bounded inductions first transfer factors within one fiber and then reconstruct the product across the original groups. Each induction runs on a quantifier-free compiled observation. Singular and ramified fibers are included through their original exact sizes. | [GaussianHighYNormBound](Lean/IPRADerivations/Analysis/GaussianHighYNormBound.lean) also proves the original point bound from arbitrary input Y degree and the actual nonzero norm flag. [Stored division](Lean/IPRADerivations/Analysis/GaussianBivariateMonicDivisionIdentity.lean) proves the literal coefficient identity for the computed quotient and remainder. [The completed Vandermonde product](Lean/IPRADerivations/Analysis/GaussianCompletedVandermondeProduct.lean) identifies the actual fiber determinant. Additional coded fields remain open. |
| `thm:norm-degree`, [05_norm_certificates.tex](../docs/proofs/foundations/ipra_finite_demand/sections/05_norm_certificates.tex) | **Checked exact Gaussian-rational norm degree and nonvanishing.** [GaussianSuperellipticNormDegree](Lean/IPRADerivations/Analysis/GaussianSuperellipticNormDegree.lean) derives `actual_superelliptic_norm_degree_closed` for the original returned determinant. The actual nonzero coefficient flag, exact weighted degree and signed cyclic leading coefficient follow from `m≥2`, positive computed degree of the nonzero `f`, coprimality and the original nonzero reduced `G`. The proof uses the real retained cyclic rank and derives that all other successful terms have strictly smaller degree. | Other coded-field instances require their own arithmetic and polynomial contracts. |
| `cor:norm-zeros`, [05_norm_certificates.tex](../docs/proofs/foundations/ipra_finite_demand/sections/05_norm_certificates.tex) | **Checked sharp weighted finite zero count in the exact Gaussian-rational coding.** [The closed bound](Lean/IPRADerivations/Analysis/GaussianSuperellipticNormDegree.lean) consumes the original point distinctness, power equation `Y^m=f(X)` and original `G=0`. The bound uses the computed weighted degree, with the actual norm flag proved from the original input. | The Gaussian-rational proper-subspace application is checked below. Other coded-field instances remain separate. |
| `cor:norm-subspace`, [05_norm_certificates.tex](../docs/proofs/foundations/ipra_finite_demand/sections/05_norm_certificates.tex) | **Checked proper-subspace point bound for the original Gaussian-rational row span.** [GaussianRationalOriginalSpanRank](Lean/IPRADerivations/Analysis/GaussianRationalOriginalSpanRank.lean) proves that properness of the original span is equivalent to strict deficiency of the actual pivot count. In the full-count case the program produces coefficients of the original rows for every numerical target vector. The closed point bound consumes genuine properness, the original distinct curve points, and their per-point existential membership in the same matrix span. Its nonzero null vector, compiled polynomial and exact norm are derived. | [GaussianSuperellipticCoverBound](Lean/IPRADerivations/Analysis/GaussianSuperellipticCoverBound.lean) proves the subsequent count for a supplied family of at most `M` proper row spans covering the original points. It uses the exact computed original membership test. The separate finite-tuple cover construction and further coded fields remain open. |

The additional displayed equation `eq:constant-loss-budget` is checked in
[BackwardDemandBounds](Lean/IPRADerivations/Foundations/BackwardDemandBounds.lean).
`numerical_constant_schedule` quantifies the loss internally and proves
`h(t)=K+c*(N∸t)` for the actual PR schedule. The general version computes
`c=loss(x)` from persistent data and `constant_loss_transfer_closed` derives
the explicit initial budget. [BackwardDemandStageLoss](Lean/IPRADerivations/Foundations/BackwardDemandStageLoss.lean)
proves the next source formula for a fixed loss program that reads the
original stage and persistent data. A quantifier-free invariant conserves
the sum of the current backward demand and the unconsumed ascending prefix
of losses. The closed initial budget is `K + Σ(n<N) d(n)`. At every
intermediate stage the actual demand uses the shifted suffix sum, which
is empty at or past the horizon. The closed transfer uses the explicit
initial sum and the original local observation contract.


The equality convention (E) is now checked by
[Analysis/AggregateEquality](Lean/IPRADerivations/Analysis/AggregateEquality.lean).
`equivalent_reflexive_closed`, `equivalent_symmetric_closed` and
`equivalent_transitive_closed` give the exact source relation for fixed PR
list evaluators with internal dimension and persistent numerical data.
Four original-coordinate covers give `2e_k+6e_v`; at the actual precision
`v=6·2^k·D(S_k,U_k)`, integer gap removal yields `2e_k` using the endpoint
pair's own computed denominator. Equivalent aggregates now give equal actual distance names by
[Analysis/AggregateDistanceName](Lean/IPRADerivations/Analysis/AggregateDistanceName.lean).
`fixed_names_equivalent_closed` proves the source `2e_k` comparison for
actual `d(z,S_k)` samples. `moving_names_equivalent_closed` proves the
unbounded equivalence of the prescribed `d(U_(k+1),S_(k+1))` names when
both point and aggregate representations are equivalent. No Boolean
decision of program-index/name equality is asserted.

Equation (D) is checked in the same module. `fixed_regular_closed` and
`moving_regular_closed` establish the exact source regularity constants
for the actual fixed-point and shifted moving-point programs.
`observation_closed` gives the fixed observation error `e_s+e_t`;
`moving_observation_closed` gives precisely `e_k+e_p+e_s` when comparing
the actual moving-name sample at k with `d(U_p,S_s)`.
`lipschitz_closed` proves the fixed-point Lipschitz estimate at every
actual finite aggregate sample. `fixed_moving_compatibility_closed`
identifies the fixed-point and moving-point constructions when the point
name represents that rational point. Actual PR4/PR3 program metadata are
proved. The source interprets its represented-real notation through
these finite inequalities; no separate completed-real sort is introduced.

## Completed product-stability representation

`GaussianRationalStability.original_product_stability_closed` quantifies
the original two lists, degree `N`, radius `u/v`, coefficient tolerance
`A/B` and output radius `P/Q`. Its size, sign and denominator guards are
`N≥1`, `v,B,Q≥1`, `v≤u` and both original list lengths equal to `N`.
Its point bounds use the actual original Gaussian-rational squared norm.
The coefficient bounds compare the actual generated product coefficients
at descending positions `1,…,N`; actual monicity handles position zero.
The product and rational evaluation identities identify that constructor
with the source's two products, rather than assuming their factorization.

The exact source condition is
`Q^N · N · u^(pred N) · A ≤ P^N · B · v^(pred N)`.
The actual pool includes the radius as well as both point lists. Its
computed positive denominator `D` and natural radius `R` satisfy the
proved identity `vR=uD`; the proof transports both the point bounds and
this source condition without rounding. QF coefficient/Horner inductions
and positive cancellation then supply every evaluation and factor bound.

`GaussianRationalCover.close` is the two bounded forall-exists covers on
the original list codes, using actual normalized subtraction and Euclidean
squared norm. `original_product_checker_closed` proves acceptance of its
fixed PR4 checker. `original_product_witness_closed` certifies the PR6
program's valid index, literal original target-list lookup and original
rational distance bound. All degree and size arithmetic is internal;
neither root existence nor a multiplicity-preserving matching is asserted.

## Actual runtime grouping and permutation prerequisites

[FiniteFiberGrouping](Lean/IPRADerivations/Foundations/FiniteFiberGrouping.lean)
constructs first-key representatives and the actual list of original indices
in each fiber. Its returned partition total is computed by summing the actual
fiber lengths. Finite Fubini and unique-incidence laws prove this sum equals
the original length; it is not an output field defined as that length. Group
and slot lookups recover every original position. All lengths and indices
are numerical, including empty and repeated-entry cases.

[GaussianRationalValueEquality](Lean/IPRADerivations/Analysis/GaussianRationalValueEquality.lean)
proves that native cross-product field equality is equivalent to equality of
the actual canonical keys and to a zero rational difference. Its genuine QF
Horner proof transports actual evaluation across field equality.
[GaussianRationalFiberGrouping](Lean/IPRADerivations/Analysis/GaussianRationalFiberGrouping.lean)
uses that exact recoder on the original x projection, so field-equal abscissae
have exactly the same computed group even when their raw codes differ. The
partition theorem counts original positions rather than distinct codes.
Curve transport, distinct ordinates, Vandermonde independence and the sharp
fiber multiplicity/divisibility argument remain required.

[RuntimePermutationWords](Lean/IPRADerivations/Foundations/RuntimePermutationWords.lean)
constructs the actual stored scan through m^m word codes and proves numerical
word coverage and uniqueness for all in-range distinct tuples. Its inversion
and parity programs include m=0 and m=1. This supplies the runtime word list
for the determinant.
[GaussianPolynomialDeterminantTerms](Lean/IPRADerivations/Analysis/GaussianPolynomialDeterminantTerms.lean)
now constructs the signed polynomial products of the actual cells M(digit_j,j),
retaining complete coefficients. Genuine QF induction derives the independent
scalar-product evaluation from the original square-table shape. Explicit sign
branches select +1 for even parity and -1 for odd parity. Stored widths,
canonicality, coefficient recurrences, empty/singleton cases and actual PR4
fields are checked.
[GaussianPolynomialDeterminant](Lean/IPRADerivations/Analysis/GaussianPolynomialDeterminant.lean)
now folds those signed products across the actual retained word list into a
complete canonical polynomial. Separate genuine QF inductions prove its
coefficient and evaluation Leibniz formulas against independently constructed
finite sums. The literal PR3 returns this polynomial, the word list and count.
Its stored width mL+1 is an upper bound and includes zero/raw inputs, m=0/m=1
and L=0. The original multiplication-matrix norm is now composed below. Sign algebra,
multilinearity, determinant multiplication, weighted nonvanishing and sharp
fiber multiplicity remain separate obligations. It does not identify arbitrary outer tuple codes merely
because their bounded entries agree.

## Original-row norm and actual curve fibers

[GaussianPolynomialMonicNorm](Lean/IPRADerivations/Analysis/GaussianPolynomialMonicNorm.lean)
now composes the original polynomial multiplication matrix with the actual
numerical determinant. It derives every nested matrix-shape condition from
the original coefficient-row guards, returns the norm/matrix/columns/width,
and proves literal coefficient and evaluation Leibniz. Its width bound is
m(a+pred(m)c)+1; no exact nonzero degree is asserted. The same returned matrix
satisfies the source curve-action equations, including zero components at an
original common zero. [The original point root theorem](Lean/IPRADerivations/Analysis/GaussianNormFiniteZeroBound.lean)
uses the positive size of its actual abscissa group to derive norm zero.
Field-value properness transports this equality to the original abscissa code.

[GaussianRationalCurveFibers](Lean/IPRADerivations/Analysis/GaussianRationalCurveFibers.lean)
constructs the actual ordinate list of every original field-x fiber. Genuine
scalar specialization properness transports original F/G equations to its
representative x. Original pairwise field-distinctness is the negation of
simultaneous x and y equality; it is not replaced by raw-code inequality.
It derives field-distinct ordinates, actual specialized roots and t<=m for
the same generated list. The PR3 ordinate and PR6 returned certificates retain
the exact computed partition sum over all original positions. The completed
fiber matrices, local determinant divisibility and global multiplicity bound
use this same partition.

## Field transport and completed fiber-matrix prerequisites

[GaussianRationalFubini](Lean/IPRADerivations/Analysis/GaussianRationalFubini.lean)
proves equality of separately constructed row-first and column-first field
sums by genuine QF induction. Both counts are numerical and raw entries stay
under actual qadd. [GaussianRationalPermutationSum](Lean/IPRADerivations/Analysis/GaussianRationalPermutationSum.lean)
uses actual delta/incidence sums to derive bounded permutation reindexing from
local range and inverse facts, including empty domains and raw inputs.
[GaussianRationalFiniteProduct](Lean/IPRADerivations/Analysis/GaussianRationalFiniteProduct.lean)
constructs actual qone/qmul folds and derives numerical splits and bounded
entry congruence; a raw singleton is its canonical recode.

[RuntimeAdjacentPermutationSwap](Lean/IPRADerivations/Foundations/RuntimeAdjacentPermutationSwap.lean)
constructs numerical adjacent tuple/word/rank swaps and derives their real
involutions. Genuine natural sum transport proves the actual inversion
balance, distinct-adjacent odd-count relation and retained parity flip. Its
word-code horizon guard remains separate from the bare tuple checker. Actual
retained words derive the needed bounds and distinctness internally.
Actual Gaussian signing and same-scalar pair cancellation are now derived in
[GaussianDeterminantSignTransport](Lean/IPRADerivations/Analysis/GaussianDeterminantSignTransport.lean).
The raw double negative equals canonical recode; comparison with the original
code retains its canonical guard. Actual retained ranks derive word validity.
[GaussianRationalAdjacentProduct](Lean/IPRADerivations/Analysis/GaussianRationalAdjacentProduct.lean)
now proves actual adjacent-factor swaps using that SAME numerical reader, and
a genuine unconditional QF induction identifies the original determinant
scalar fold with the actual generic evaluated-factor product. Numerical
bounds/data and raw factors remain internal. Exchanged matrix-factor matching,
concrete retained-word field-sum reindexing and full alternation/adjugate/
determinant algebra remain required.

[GaussianRationalFiberVandermonde](Lean/IPRADerivations/Analysis/GaussianRationalFiberVandermonde.lean)
now constructs the actual U/W power/completion tables, constant-polynomial WP
and polynomial product WM. Genuine QF coefficient/evaluator fold proofs
identify WM with the actual WP*M finite sums. Original norm and field-point
predicates produce the same ordinate list and selected x, derive 1<=t<=m,
and prove the returned first-t polynomial rows vanish at that x. The lower
standard rows use coordinate r, and the actual PR8 payload keeps the exact
original partition sum. The right inverse and nonzero completed determinant
are derived below. The global multiplicity count uses the resulting local
row-factor quotients. The explicit determinant formula for the same
block-completed matrix is derived below.

[GaussianRationalLagrangeCardinals](Lean/IPRADerivations/Analysis/GaussianRationalLagrangeCardinals.lean)
now constructs actual numerical skip/deletion lists with proved full coverage.
A guarded QF induction on the SAME original reverse reconstruction-factor fold
proves the denominator nonzero from original field distinction. The native
norm/reciprocal then gives actual cardinal delta evaluations. A query-parametric
ascending coefficient-dot identity proves the numerical Vandermonde right-inverse
entry computation for this cardinal data. The actual PR2 and original-fiber PR4
outputs retain the SAME generated ordinate list, selected x and exact partition;
source point distinction and original index guards discharge the field premises.
Singletons and empty admissible-index domains are covered. The full actual completed-matrix right inverse is now derived in
[GaussianRationalFiberRightInverse](Lean/IPRADerivations/Analysis/GaussianRationalFiberRightInverse.lean).
For t=length(R)<=m its actual blocks are W=[[V,C],[0,I]] and
Z=[[N,-NC],[0,I]], with N the SAME ascending cardinal coefficient table.
The proof derives the small V*N identity, splits the SAME m-term product,
and cancels the actual upper-right sums by one shared triple-product Fubini
body. The lower standard rows keep their original global coordinate r.
[GaussianRationalMatrixFiniteSums](Lean/IPRADerivations/Analysis/GaussianRationalMatrixFiniteSums.lean)
supplies the derived same-fold split, raw-safe delta selection, negation and
actual scalar matrix-product producer; no matrix or sum output law is supplied.
Original curveZeros and pointDistinct yield the actual field distinction and
t<=m for the original generated ordinate list. PR2/PR4 output identities keep
N/C/W/Z/WZ/R/t/m, the original selected x and exact cardinal partition.
Empty and full fibers, zero dimensions, singleton and raw ordinate codes have
explicit guarded endpoints.
[GaussianFiberDeterminantNonzero](Lean/IPRADerivations/Analysis/GaussianFiberDeterminantNonzero.lean)
uses the actual right inverse and the scalar determinant laws to derive
`det W · det Z = 1`. It identifies the sole coefficient of the constant
polynomial lift with the same nonzero determinant and retains the original
fiber data. The [triangular determinant theorem](Lean/IPRADerivations/Analysis/GaussianScalarTriangularDeterminant.lean)
reduces the actual scalar determinant of a field-triangular matrix to its
actual diagonal product in either orientation. The [Newton polynomial table](Lean/IPRADerivations/Analysis/GaussianVandermondeNewtonPolynomials.lean)
uses the same original nodes to compute the forward difference products.
The [square Vandermonde theorem](Lean/IPRADerivations/Analysis/GaussianVandermondeNewtonMatrix.lean)
proves the literal product for the original square power matrix. The
[unit triangular eliminator](Lean/IPRADerivations/Analysis/GaussianVandermondeCompletionElimination.lean)
clears the upper-right block of the original completed matrix by actual
multiplication. The [completed determinant theorem](Lean/IPRADerivations/Analysis/GaussianCompletedVandermondeProduct.lean)
uses the extended Newton table to derive the literal forward pair product
for that original matrix whenever the ordinate count is at most its size.
It proves the same value for the original constant polynomial lift and
field nonvanishing when the ordinates are distinct.

[GaussianPolynomialColumnAlternation](Lean/IPRADerivations/Analysis/GaussianPolynomialColumnAlternation.lean)
now constructs the actual adjacent-column table with inactive raw-row fallback.
It derives original-to-swapped table shape, matches the SAME determinant factor
products using the shared word-position swap, and derives the bounded retained-rank
range/involution contracts for the actual field-sum reindexing. Thus the SAME
original/swapped determinant programs have opposite evaluations at every numerical
query under only original shape and the adjacent-position guard. Its PR4 returns
both original program payloads; empty and singleton inactive cases retain their
correct evaluations.
[GaussianPolynomialColumnCoefficients](Lean/IPRADerivations/Analysis/GaussianPolynomialColumnCoefficients.lean)
adds the original and swapped buffers, whose combined width is `mL+1`, and
derives its vanishing on the actual grid from the evaluation theorem.
[GaussianRationalFiniteGridIdentity](Lean/IPRADerivations/Analysis/GaussianRationalFiniteGridIdentity.lean)
uses that many distinct points to force the computed zero flag and the
zero value of every coefficient. Canonicality then gives literal negation of
the original stored coefficients at all bounded indices. The PR4 result
retains both buffers and the original swap payload.

[RuntimeWordAppend](Lean/IPRADerivations/Foundations/RuntimeWordAppend.lean)
proves the append and bounded digit laws used by
[GaussianRationalTupleExpansion](Lean/IPRADerivations/Analysis/GaussianRationalTupleExpansion.lean).
The latter expands the product of the first `d ≤ m` Gaussian-rational row sums
into the sum over all `m^d` words, using
[GaussianRationalBlockSums](Lean/IPRADerivations/Analysis/GaussianRationalBlockSums.lean)
to flatten the folds. The same block-sum library proves that masking by a
fixed selector agrees with summing the indices in the actual retained list.
[RuntimeWordSorting](Lean/IPRADerivations/Foundations/RuntimeWordSorting.lean)
derives a computed sort using `m²+1` steps of the adjacent swap. It preserves
the checker and produces either the identity word or a repeated adjacent
digit. [GaussianScalarColumnSelection](Lean/IPRADerivations/Analysis/GaussianScalarColumnSelection.lean)
uses that trace to prove the signed permutation law and zero for repeated
columns. [GaussianScalarDeterminant](Lean/IPRADerivations/Analysis/GaussianScalarDeterminant.lean)
derives the scalar Leibniz formula and bounded cell congruence, and
[GaussianScalarIdentityDeterminant](Lean/IPRADerivations/Analysis/GaussianScalarIdentityDeterminant.lean)
proves that the actual identity table has determinant one.
[GaussianScalarDeterminantMultiplication](Lean/IPRADerivations/Analysis/GaussianScalarDeterminantMultiplication.lean)
expands the true product of dot sums and uses this selection law and the
original retained-word scan to prove scalar multiplicativity.

[GaussianPolynomialScalarLeftDeterminant](Lean/IPRADerivations/Analysis/GaussianPolynomialScalarLeftDeterminant.lean)
applies the result to evaluation of the actual scalar-left polynomial product.
The [grid comparison](Lean/IPRADerivations/Analysis/GaussianRationalGridCoefficientEquality.lean)
then gives equality of its determinant coefficients with the independently
scaled determinant coefficients, including for the original fiber product.
[GaussianScalarDiagonalDeterminant](Lean/IPRADerivations/Analysis/GaussianScalarDiagonalDeterminant.lean)
proves the diagonal determinant and actual row action. The constructed row
quotients and repeated-root factor are checked separately in
[GaussianPolynomialRowQuotient](Lean/IPRADerivations/Analysis/GaussianPolynomialRowQuotient.lean).
[GaussianPolynomialRowFactorDeterminant](Lean/IPRADerivations/Analysis/GaussianPolynomialRowFactorDeterminant.lean)
composes the row quotients with the actual scalar diagonal action and
finite grid coefficient comparison. It proves the factor identity at
every stored coefficient after padding. The
[original fiber quotient](Lean/IPRADerivations/Analysis/GaussianNormFiberDivisibility.lean)
then uses `det W · det Z = 1` to transfer that factor identity to
the original returned norm. It takes the original norm input and source
point predicates, and preserves the exact fiber count and partition.

[Linear cancellation](Lean/IPRADerivations/Analysis/GaussianRationalLinearCancellation.lean)
and [fixed-width synthetic division](Lean/IPRADerivations/Analysis/GaussianRationalFixedWidthStrip.lean)
give the next steps for separating factors of different abscissae.
The [superelliptic rows](Lean/IPRADerivations/Analysis/GaussianSuperellipticTail.lean)
give the exact original curve equation, and the
[weighted maximum](Lean/IPRADerivations/Analysis/GaussianPolynomialWeightedDegree.lean)
uses the original nonzero rows and computed degrees.
The [cyclic word and wraps](Lean/IPRADerivations/Foundations/RuntimeCyclicPermutation.lean)
and [digit sum](Lean/IPRADerivations/Foundations/RuntimePermutationDigitSum.lean)
supply numerical permutation facts for the weighted proof. The
[original companion matrix entries](Lean/IPRADerivations/Analysis/GaussianSuperellipticMatrixEntries.lean)
now have the evaluated rotation and wrap-power formula, with the inverse
index tied to the original matrix slots. The
[matching stored coefficient law](Lean/IPRADerivations/Analysis/GaussianSuperellipticMatrixCoefficients.lean)
reflects the evaluated identity at a finite grid and identifies the actual
padded cell and its tighter unpadded buffer. The
[original cell leading law](Lean/IPRADerivations/Analysis/GaussianSuperellipticMatrixLeading.lean)
identifies its computed degree and leading coefficient in both wrap cases.
A zero row gives a zero cell independently of the flag of `f`. For nonzero
`f`, the cell and selected row have the same computed nonzero flag. The
[power-product law](Lean/IPRADerivations/Analysis/GaussianRationalPowerProduct.lean)
gives an exact finite product for a common leading base and summed exponents.
The [permutation sum law](Lean/IPRADerivations/Foundations/RuntimePermutationSums.lean)
reindexes an arbitrary fixed numerical body along the actual retained word.
[Actual determinant term degrees](Lean/IPRADerivations/Analysis/GaussianPolynomialDeterminantTermDegree.lean)
derive the zero and nonzero branches of every existing stage and signed
term. The computed degree is the sum of the degrees of the actual factors,
and the leading coefficient uses their actual leading product and sign.
[Leading coefficient selection](Lean/IPRADerivations/Analysis/GaussianPolynomialDeterminantLeadingSelection.lean)
uses the original signed coefficient sum. Once its earlier terms vanish
and the selected slot has a single nonzero contributor, the actual scan
returns the first slot, degree and leading value. The
[actual word weights](Lean/IPRADerivations/Analysis/GaussianSuperellipticWordWeights.lean)
derive strict degree away from the retained cyclic term. The
[term bridge](Lean/IPRADerivations/Analysis/GaussianSuperellipticWordTerms.lean)
transfers these weights to the existing determinant stages, and the
[cyclic leading product](Lean/IPRADerivations/Analysis/GaussianSuperellipticCyclicLeading.lean)
computes the actual leading value with the exact wrap count. The
[original norm theorem](Lean/IPRADerivations/Analysis/GaussianSuperellipticNormDegree.lean)
combines these laws with the
[degree dominance criterion](Lean/IPRADerivations/Analysis/GaussianPolynomialDeterminantDegreeDominance.lean)
to derive the original flag, exact degree, signed leading coefficient and
finite weighted point bound.

The [grouped factor product](Lean/IPRADerivations/Analysis/GaussianNormGroupFactorProduct.lean)
is monic of computed degree equal to the original prefix sum of fiber
sizes. At completion the sum is the length of the original point list.
Field-value distinction of the original abscissae proves that the prefix
product does not vanish at the next abscissa. The
[padded factorization degree law](Lean/IPRADerivations/Analysis/GaussianRationalPaddedProductDegree.lean)
proves that a coefficient reconstruction of a nonzero padded norm yields
nonzero factors and the exact degree sum. The
[actual block transfer](Lean/IPRADerivations/Analysis/GaussianRationalBlockFactorTransfer.lean)
uses one initial finite coefficient comparison to derive the intermediate
root and cancellation at each stripping step. The
[original finite norm bound](Lean/IPRADerivations/Analysis/GaussianNormFiniteZeroBound.lean)
applies this transfer through the original group count and identifies the
sum of all removed multiplicities with the length of the input point list.

For the subspace construction, the
[bivariate power expansion](Lean/IPRADerivations/Analysis/GaussianBivariatePowerExpansion.lean)
identifies the original evaluator with an actual nested finite sum in the
ascending exponents. It reads the original descending storage slots in
both coordinates. The
[actual weighted basis](Lean/IPRADerivations/Analysis/GaussianWeightedMonomialBasis.lean)
enumerates the original admissible pairs in lexicographic order. Its
returned evaluation vector uses precisely those pairs. The
[rectangular pivot operation](Lean/IPRADerivations/Analysis/GaussianRationalRowElimination.lean)
normalizes a nonzero source pivot, eliminates its column and preserves
the original homogeneous row equations in both directions. The
[flat bivariate sum](Lean/IPRADerivations/Analysis/GaussianBivariateFlatSum.lean)
uses the basis quotient and remainder labels. The
[polynomial compiler](Lean/IPRADerivations/Analysis/GaussianAnnihilatorPolynomial.lean)
stores the input coefficients at their actual retained ranks and derives
the weighted bound and nonvanishing from the finite input witness. The
[evaluation identity](Lean/IPRADerivations/Analysis/GaussianAnnihilatorPolynomialEvaluation.lean)
filters the full sum by the original basis predicate and derives the exact
row dot product. The
[actual row-combination theorem](Lean/IPRADerivations/Analysis/GaussianRationalRowSpan.lean)
uses finite sum interchange to carry null row equations to any supplied
span membership certified by coordinate value equality. The
[subspace bound](Lean/IPRADerivations/Analysis/GaussianSuperellipticSubspaceFromSpan.lean)
uses each point’s existential coefficient witness to derive its zero
equation and applies the exact norm bound to the same compiled polynomial.
The [pivot search](Lean/IPRADerivations/Analysis/GaussianRationalPivotSearch.lean)
chooses the least available row with a nonzero field entry, or derives
field-zero entries for all available rows on failure. The
[elimination loop](Lean/IPRADerivations/Analysis/GaussianRationalEliminationLoop.lean)
computes the full rectangular update and its tag history, preserving the
original homogeneous equations. The
[tag profile](Lean/IPRADerivations/Analysis/GaussianRationalEliminationTagProfile.lean)
shows that bounded pivot rows have unique tags and provides their actual
column lookup. The
[unmarked-row invariant](Lean/IPRADerivations/Analysis/GaussianRationalEliminationUnmarkedRows.lean)
makes every processed entry of an unmarked row field-zero. The
[pivot history count](Lean/IPRADerivations/Analysis/GaussianRationalPivotHistoryCount.lean)
computes the least free column from strict count deficiency. The
[free-column vector](Lean/IPRADerivations/Analysis/GaussianRationalFreeColumnVector.lean)
has a unit at that column. The [pivot column invariant](Lean/IPRADerivations/Analysis/GaussianRationalEliminationPivotColumns.lean)
derives the exact field unit and zeros for every computed pivot column.
The [annihilator program](Lean/IPRADerivations/Analysis/GaussianRationalAnnihilatorVector.lean)
uses these equations and the unmarked rows to prove that the same
nonzero vector solves the reduced system. The full elimination loop
transfers that vector back to the original homogeneous system. The
[closed subspace bound](Lean/IPRADerivations/Analysis/GaussianSuperellipticSubspaceTheorem.lean)
applies the supplied-vector theorem to this actual output. The
[rank deficiency criterion](Lean/IPRADerivations/Analysis/GaussianRationalRankNullityCriterion.lean)
proves equivalence between strict deficiency and a nonzero null vector of
the original matrix. The
[proper-span witness](Lean/IPRADerivations/Analysis/GaussianRationalProperSpanWitness.lean)
produces a unit vector outside the original row span in the deficient case.
When every column has a pivot, the
[reduced span theorem](Lean/IPRADerivations/Analysis/GaussianRationalFullReducedSpan.lean)
computes coefficients representing any supplied target vector in the
reduced rows. The [one-pivot transport](Lean/IPRADerivations/Analysis/GaussianRationalRowSpanPivotTransfer.lean)
derives the actual coefficient correction for the original rows. The
[backward recursion](Lean/IPRADerivations/Analysis/GaussianRationalRowSpanRewind.lean)
keeps each represented coordinate fixed as it revisits the numerical
column history. Finally, the [original-span criterion](Lean/IPRADerivations/Analysis/GaussianRationalOriginalSpanRank.lean)
identifies properness of the original span with strict deficiency and
applies this criterion to the original point bound.

[FiniteCoverAssignment](Lean/IPRADerivations/Foundations/FiniteCoverAssignment.lean)
computes the first accepted cover index and the original-index groups
for a fixed bounded test on numerical data. It proves that the sum of
actual group sizes is the original length. If every group has size at
most the cutoff, the original length is at most the number of groups
times that cutoff.

[Forward row-span transport](Lean/IPRADerivations/Analysis/GaussianRationalRowSpanForward.lean)
computes coefficient lists for the same elimination steps. The
[reduced-span test](Lean/IPRADerivations/Analysis/GaussianRationalReducedSpanMembership.lean)
checks the candidate coefficients at all original columns. The
[original-span test](Lean/IPRADerivations/Analysis/GaussianRationalOriginalSpanMembership.lean)
reflects actual existential membership in the original rows. The
[cover membership adapter](Lean/IPRADerivations/Analysis/GaussianSuperellipticCoverMembership.lean)
uses this test on the original monomial evaluation vectors. Each actual
group inherits the original curve equation, field distinctness and span
membership, so the [closed covering theorem](Lean/IPRADerivations/Analysis/GaussianSuperellipticCoverBound.lean)
derives the sharp count from the supplied finite family and cover.

[Polynomial Y shift](Lean/IPRADerivations/Analysis/GaussianPolynomialYShift.lean)
pads the original rows and appends one polynomial-zero row.
[Constant injection](Lean/IPRADerivations/Analysis/GaussianPolynomialConstantInjection.lean)
adds the original incoming X polynomial to the constant Y row.
The [monic remainder fold](Lean/IPRADerivations/Analysis/GaussianPolynomialMonicHornerReduction.lean)
uses these coefficient operations and the actual companion to reduce all
original Y rows. The [quotient fold](Lean/IPRADerivations/Analysis/GaussianPolynomialMonicHornerQuotient.lean)
uses the top row of the same remainder and derives reconstruction at
arbitrary numerical X and Y queries. The
[rectangular grid theorem](Lean/IPRADerivations/Analysis/GaussianBivariateGridCoefficients.lean)
identifies stored coefficients from exact agreement on a rectangular grid.
[Rectangular buffers](Lean/IPRADerivations/Analysis/GaussianBivariatePolynomialBuffers.lean)
implement literal padding and addition with exact evaluator laws. The
[full monic table](Lean/IPRADerivations/Analysis/GaussianBivariateMonicFactor.lean)
and [bivariate convolution](Lean/IPRADerivations/Analysis/GaussianBivariatePolynomialProduct.lean)
compute the actual product of the monic factor and quotient. The
[closed coefficient identity](Lean/IPRADerivations/Analysis/GaussianBivariateMonicDivisionIdentity.lean)
proves equality of each stored coefficient of the padded original input
and the computed product plus remainder. Its only source guards are
positive monic Y degree and the original row widths.
The [high-Y norm bound](Lean/IPRADerivations/Analysis/GaussianHighYNormBound.lean)
uses the computed remainder and the original common zeros to give the
sharp finite point count when the actual norm is nonzero.

## Characteristic coefficients and rational field transport

[GaussianRationalCharacteristicPolynomial](Lean/IPRADerivations/Analysis/GaussianRationalCharacteristicPolynomial.lean)
computes the characteristic polynomial of an actual Gaussian-rational
matrix with numerical dimension. It proves the literal leading coefficient
one and identifies every evaluation with the actual scalar determinant of
`X I - A`. [GaussianRationalConvolutionNorm](Lean/IPRADerivations/Analysis/GaussianRationalConvolutionNorm.lean)
proves the coefficient L1 product estimate for the stored convolution.
[GaussianPolynomialConvolutionDifference](Lean/IPRADerivations/Analysis/GaussianPolynomialConvolutionDifference.lean)
gives the corresponding perturbation bound for the actual two products.
[RuntimePermutationFactorialBound](Lean/IPRADerivations/Foundations/RuntimePermutationFactorialBound.lean)
bounds the retained word count by `n!` through maximum deletion and
an injection into the smaller enumerator. The source spectrum application
still needs to combine these results into the quantitative coefficient
precision budget for names and construct the spectral radius.

[RationalGaussianEmbedding](Lean/IPRADerivations/Analysis/RationalGaussianEmbedding.lean)
preserves field equality, zero, one, addition, multiplication and negation
from the original scalar rational codes. Its real-axis round trip uses
canonical recoding. [RationalPolynomialGaussianEmbedding](Lean/IPRADerivations/Analysis/RationalPolynomialGaussianEmbedding.lean)
constructs the actual mapped coefficient list and proves that the actual
rational Horner calculation embeds into Gaussian Horner. This also gives
zero reflection and the evaluation formula at arbitrary raw real-axis
queries. [RationalGaussianRealPart](Lean/IPRADerivations/Analysis/RationalGaussianRealPart.lean)
and [RationalRowSpanGaussianEmbedding](Lean/IPRADerivations/Analysis/RationalRowSpanGaussianEmbedding.lean)
now transport original rational row-span membership through the actual
rectangular embedding. Every Gaussian witness yields a rational witness
by taking real parts. The rational norm specialization still needs the
matrix-calculation and determinant transport that identify its norm
polynomial.

## Logical strength and program boundaries

The ordinary scheduling proof keeps the user's entire context fixed during
induction. That context can contain quantified or undecidable formulas. The
induction formula itself is the QF implication
`t≤N → observationBit(t,h(t),x)=1`. Its conclusion is converted back to the
original bounded observation only after the reflected equation is proved.
Universal closure of stages and demands is introduced after finite transfer;
the proof never inducts on the unbounded assertion that a represented object
is globally valid.

The parameter-changing program constructs its backward schedule and performs
an ordinary forward primitive recursion with the terminal data fixed. The
coherence comparison of backward arrays is total. The comparison of horizons
and forward values retains `t≤N`, exactly where truncated subtraction requires
it. Both public defining equations concern the explicit generated PR symbol;
their premises contain neither schedule coherence nor the recurrence being
proved. Degree/program parameters fixed in Lean are distinguished from
internally quantified numerical parameters.

The norm section's field interface requires exact decidable equality and
primitive-recursive coded field operations whose laws are proved in the
object theory. The source identifies rationals and explicitly presented
number fields as examples. Arbitrary Cauchy-name coefficients do not satisfy
that interface. Proofs for externally fixed matrix sizes must not be presented
as a single uniform numerical-dimension constructor without the required code
and lookup proof.

## Acceptance gates for the remaining work

The source's Section 6 supplies concrete implementation obligations beyond
the environment labels. Completion needs the following evidence:

1. **Arithmetic and reflection:** actual signed/rational/list PR definitions,
   defining equations, valid-input guards, and bounded Boolean compilation.
   Existing library components must be connected to the selected source
   representation by proved adapters.
2. **Scheduling:** actual backward and forward programs with QF invariant
   proofs, then variable-query maxima and the concrete nonlinear-name
   instance. The general finite transfer, global induction, predetermined recursion and
   variable-query envelope claims are checked above;
   they do not prove every application automatically.
3. **Metric algebra and aggregate witnesses:** actual two-sided checker
   reflection, all five finite-calculus clauses, least-neighbor construction,
   distance/value names and the two-parameter approximate-witness evaluator.
4. **Polynomial analysis:** Gaussian-rational convolution/synthetic division,
   exact descent assumptions or their derivations, actual factorization
   budgets, finite Hausdorff stability, coefficient sampling and both
   root-membership directions. Finite product stability is now checked in
   the full original rational coding above. Uniform approximate factorization
   is checked by actual backward coefficient-error induction. Its concrete
   monic instance now discharges (RD) using the proved uniform step. Its [balanced-radius producer](Lean/IPRADerivations/Analysis/GaussianBalancedRadius.lean)
   now derives the actual zero/nonzero radius certificates and bounded
   scan/witness outputs from a supplied coefficient list. Actual
   [translation](Lean/IPRADerivations/Analysis/GaussianRationalTranslation.lean)
   now constructs the coefficients of P(z+W), and the
   [monic frontend](Lean/IPRADerivations/Analysis/GaussianTranslatedBalancedRadius.lean)
   connects the original C,N,z to the full radius certificate. Relative
   Euclidean finite-sum norms are also checked. The actual
   [dominant plateau](Lean/IPRADerivations/Analysis/GaussianDominantPlateauValues.lean)
   and its [original monic-input frontend](Lean/IPRADerivations/Analysis/GaussianTranslatedDominantPlateau.lean)
   now derive the same positive coefficient's dominance at three literal
   consecutive radii. The actual bounded center search supplies its own
   success, and no maximum, count, monotonicity or plateau premise is
   supplied. The actual [pointwise squared weights](Lean/IPRADerivations/Analysis/GaussianDominantScoreWeights.lean)
   satisfy 16^abs(i-k)*S_i<=S_k at the selected radius. The actual
   [off-dominant Gaussian sum](Lean/IPRADerivations/Analysis/GaussianOffDominantSum.lean)
   now satisfies 9*normSq(otherSum)<=4*selectedScore, giving the required
   2/3 norm estimate for every displacement within that radius. All term,
   weight and common-denominator sum premises are derived; the stronger
   displayed sum of individual magnitudes is not separately encoded.
   The actual [polynomial decomposition](Lean/IPRADerivations/Analysis/GaussianRationalDominantDecomposition.lean)
   and [strict dominant lower/upper bounds](Lean/IPRADerivations/Analysis/GaussianDominantMagnitude.lean)
   are now checked, with the unchanged source D=2^N*4^(2*N*N). The
   [original-input preparation](Lean/IPRADerivations/Analysis/GaussianTranslatedDominantEstimates.lean)
   connects the literal P(z+delta) split, bounds against actual P(z),
   both residual branches and the conditional off-sum norm estimate.
   The actual [rational direction](Lean/IPRADerivations/Analysis/GaussianRationalDirection.lean)
   now proves the exact source certificate A*b^2<=d^2, d>=0 and b>0 for its
   actual unit output, with original nonzero/k/epsilon guards only. Its
   [initializer](Lean/IPRADerivations/Analysis/GaussianRationalDirectionNormalizer.lean),
   [computed loop](Lean/IPRADerivations/Analysis/GaussianRationalDirectionIteration.lean)
   and [phase transfer](Lean/IPRADerivations/Analysis/GaussianRationalPhaseCertificate.lean)
   discharge all normalization, clock and local approximation laws. Actual
   normalizer/target data and the 65/64 bracket are retained. Dominant-pair
   decrease and uniform monic contraction are now proved by the actual
   [selected residual estimates](Lean/IPRADerivations/Analysis/GaussianDominantResidualEstimates.lean),
   [original positive-residual transport](Lean/IPRADerivations/Analysis/GaussianMonicPositiveDecrease.lean)
   and [zero/positive branch](Lean/IPRADerivations/Analysis/GaussianMonicDescentBranch.lean).
   [GaussianMonicRD](Lean/IPRADerivations/Analysis/GaussianMonicRD.lean) constructs
   the fixed step and proves its uniform object-theory monicRD sentence.
   [Concrete applications](Lean/IPRADerivations/Analysis/GaussianMonicApplications.lean)
   discharge RD for approximate-root/factorization programs.
   [Concrete root support](Lean/IPRADerivations/Analysis/GaussianMonicRootSupport.lean)
   and [concrete adequacy](Lean/IPRADerivations/Analysis/GaussianMonicRootAdequacy.lean)
   now discharge that RD contract in the actual root names, source proposition
   and completed-distance corollary, preserving their genuine input guards.
   Actual [nonconstant translation](Lean/IPRADerivations/Analysis/GaussianTranslatedNonconstant.lean)
   also proves the original positive-degree coefficient survives translation.
   [Nonmonic RD](Lean/IPRADerivations/Analysis/GaussianNonmonicRD.lean) uses the
   same fixed step at the original N to prove finite contraction for every
   nonconstant rational polynomial, even with zero leading coefficients.
   [Nonmonic approximate roots](Lean/IPRADerivations/Analysis/GaussianNonmonicApproximateRoot.lean)
   instantiate the actual finite residual clock without an RD premise.
   Actual [triangular coefficient recovery](Lean/IPRADerivations/Analysis/GaussianTranslationCoefficientValues.lean),
   [rational rescaling](Lean/IPRADerivations/Analysis/GaussianTranslationScaledCoefficients.lean)
   and [computed maximum](Lean/IPRADerivations/Analysis/GaussianTranslationCoefficientMaximum.lean)
   now give the [quantitative translation bound](Lean/IPRADerivations/Analysis/GaussianTranslationCoefficientBound.lean)
   with the stronger coefficient constant 2^N, hence the source N*2^N.
   Genuine [compiled backward induction](Lean/IPRADerivations/Foundations/BoundedSyntaxBackwardInduction.lean)
   proves the actual row invariant; no inversion or global coefficient law
   is supplied. A separate [actual inverse-binomial row proof](Lean/IPRADerivations/Analysis/GaussianInverseBinomialRows.lean)
   now derives the literal Pascal sums by guarded backward induction, and
   [inverse translation](Lean/IPRADerivations/Analysis/GaussianRationalInverseTranslation.lean)
   binds them to ordinary binomial coefficients and actual translated entries.
   The original a_k is canonically recoded; original length and k<=N suffice,
   including N=0 and noncanonical raw inputs. No inverse identity is assumed.
   [Internal rational power-order reflection](Lean/IPRADerivations/Analysis/RationalNonnegativePowerOrder.lean)
   is also proved. Actual [coefficient apartness and radius combination](Lean/IPRADerivations/Analysis/GaussianNonmonicTravelCoefficientBound.lean)
   and its [normalized program comparison](Lean/IPRADerivations/Analysis/GaussianNonmonicTravelComparison.lean)
   derive the source squared budget. [Residual clearing](Lean/IPRADerivations/Analysis/GaussianTravelResidualClearing.lean)
   and [shrinking-power arithmetic](Lean/IPRADerivations/Analysis/RationalShrinkingStepPowerBound.lean)
   then give the original travel bound. The unchanged displacement is proved
   to stay within the actual [starting radius](Lean/IPRADerivations/Analysis/GaussianNonmonicDisplacementRadius.lean).
   [GaussianNonmonicStepBound](Lean/IPRADerivations/Analysis/GaussianNonmonicStepBound.lean)
   closes the full finite source step-bound lemma and its actual PR3 endpoint
   from original coefficient/rate/residual assumptions, without an NC, chosen
   coefficient, radius, power or output-law premise. All 15 numerical inputs
   are internal. [General coefficient names](Lean/IPRADerivations/Analysis/GaussianGeneralCoefficientNames.lean)
   now derive whole-tail apartness from the actual h+2 test; the
   [sample builder](Lean/IPRADerivations/Analysis/GaussianGeneralPolynomialSamples.lean)
   retains all supplied coefficients and derives its initial B bound.
   [All-coefficient perturbation](Lean/IPRADerivations/Analysis/GaussianRationalAllCoefficientPerturbation.lean)
   covers the changing leading observation. Actual
   [global constants](Lean/IPRADerivations/Analysis/GaussianGeneralFTAConstants.lean)
   and [rate comparisons](Lean/IPRADerivations/Analysis/GaussianGeneralFTARates.lean)
   discharge the source clock and rate obligations, with the documented
   upper-power binary-length convention. The
   [actual product recursor](Lean/IPRADerivations/Analysis/GaussianGeometricProduct.lean),
   [tail gap](Lean/IPRADerivations/Analysis/GaussianGeometricProductTail.lean)
   and [finite uniform bound](Lean/IPRADerivations/Analysis/GaussianGeometricProductBound.lean)
   prove the [computed source product bound](Lean/IPRADerivations/Analysis/GaussianGeneralProductBound.lean)
   1<=U_j<=R from N>=1 alone, without a supplied global bound or infinite product.
   The [actual trajectory](Lean/IPRADerivations/Analysis/GaussianGeneralFTATrajectory.lean)
   samples P_j at j+L and has proved updates, canonicality and initial residual.
   The [computed sampled-step theorem](Lean/IPRADerivations/Analysis/GaussianGeneralFTAStepBound.lean)
   derives U C rho^j from original coefficient names/apartness and the local
   disk/residual budgets; every finite rate/lambda/NC obligation is discharged.
   The [actual adjacent-sample drift](Lean/IPRADerivations/Analysis/GaussianGeneralFTACoefficientDrift.lean)
   is bounded by B Q^j/(8D) throughout the computed R disk, from genuine
   coefficient coherence and precision/rate arithmetic alone.
   The [actual residual recurrence](Lean/IPRADerivations/Analysis/GaussianGeneralFTAResidualStep.lean)
   and [position-margin bootstrap](Lean/IPRADerivations/Analysis/GaussianGeneralFTARadiusStep.lean)
   now establish the [source-only simultaneous invariant](Lean/IPRADerivations/Analysis/GaussianGeneralFTAInvariant.lean)
   by genuine QF induction. The next disk is derived before coefficient drift
   is used for the next residual; no circular global premise is supplied.
   [Finite actual-trajectory telescoping](Lean/IPRADerivations/Analysis/GaussianGeneralFTATelescope.lean)
   and the original computed schedules prove the
   [general FTA main inequalities](Lean/IPRADerivations/Analysis/GaussianGeneralFTARootName.lean),
   including every later original coefficient sample and zero leading entries.
   The [actual root program](Lean/IPRADerivations/Analysis/GaussianGeneralFTAName.lean)
   is a fast Gaussian point name in the computed R disk. Its
   [same-precision polynomial evaluations](Lean/IPRADerivations/Analysis/GaussianGeneralFTAPolynomialValueName.lean)
   give a canonical fast zero PR2 name using the derived V_t bound and computed
   bl(4S+1) shift. The
   [general polynomial observer](Lean/IPRADerivations/Analysis/GaussianGeneralPolynomialEvaluation.lean)
   derives its exact (N+1)U^N plus weighted-Lipschitz modulus at any bounded
   fast point name, retaining separate numerical coefficient/point data.
   Its [actual generic value name](Lean/IPRADerivations/Analysis/GaussianGeneralPolynomialValueName.lean)
   is fast and canonical, and finite fixed-query slack removal transports any
   raw K*2^-s envelope to program zero without a modulus-dominates-K premise.
   The [general FTA binding](Lean/IPRADerivations/Analysis/GaussianGeneralFTAValueZero.lean)
   proves that precise generic program-zero predicate from the original source
   assumptions. The [constant coefficient compiler](Lean/IPRADerivations/Analysis/GaussianConstantCoefficientNames.lean)
   also derives actual coefficient coherence and computed apartness from
   numerical polynomial entries and one positive-degree nonzero coefficient;
   no coefficient-name schema is supplied for this case. The
   [original numerical polynomial binding](Lean/IPRADerivations/Analysis/GaussianConstantPolynomialEvaluation.lean)
   proves actual coefficient and guarded-QF Horner-prefix equality, then
   constructs the concrete root/value programs and original-evaluation
   dyadic zero bound from list length and a nonzero positive-degree
   coefficient alone. Arbitrary outer list-code extensionality is not used.
   The [Euclidean name relation](Lean/IPRADerivations/Analysis/GaussianNameEquivalence.lean)
   and [independent normalizer comparison](Lean/IPRADerivations/Analysis/GaussianValueNormalizerExtensionality.lean)
   now prove cross-name equivalence and program-zero transport by finite
   fixed-query slack removal. The
   [general polynomial extensionality theorem](Lean/IPRADerivations/Analysis/GaussianGeneralPolynomialExtensionality.lean)
   derives its raw discrepancy from equivalent coefficients and points,
   retaining every coefficient and the original independent disks/data/shifts.
   It includes same-upper-degree coefficient, point and disk independence.
   [Actual degree padding](Lean/IPRADerivations/Analysis/GaussianPolynomialDegreePadding.lean)
   preserves the original raw entries and adds literal leading zeros; genuine
   guarded QF Horner inductions prove equal evaluation. The
   [different-degree extensionality theorem](Lean/IPRADerivations/Analysis/GaussianPolynomialDegreeExtensionality.lean)
   compares the original normalized programs through their actual common-degree
   extensions, retaining independent disks, data and shifts.
   [Actual Gaussian-name ring laws](Lean/IPRADerivations/Analysis/GaussianNameRingLaws.lean)
   now prove associativity, commutativity, both distributions and the
   zero/one/inverse laws up to exact cross-precision equivalence, from
   original point-Cauchy conditions alone. Computed disks and all nested
   normalization errors are derived.
   [Actual reciprocal names](Lean/IPRADerivations/Analysis/GaussianNameReciprocal.lean)
   now derive separation, regularity, both product inverse laws and properness
   from point CN and the original finite dyadic apartness witness. Bare
   negated zero is not an effective apartness selector.
   [Uniform prefix interpretation](Lean/IPRADerivations/Analysis/GaussianPolynomialNameHorner.lean)
   derives actual add/multiply Horner recurrence for internal prefix lengths;
   the full prefix binds to the original value program and zero predicate
   with its exact original data and normalization shift.
   [The collected name-level FTA certificate](Lean/IPRADerivations/Analysis/GaussianRepresentedFTA.lean)
   now derives the actual root, prefix-arithmetic and full Horner-zero
   certificate from the original source input, retaining R/T/data and the
   original programs. Its actual sample output has proved fields and bounds.
   Completed-field realization and represented factorization remain separate.
   The [natural scalar action](Lean/IPRADerivations/Analysis/GaussianRationalNaturalScale.lean)
   and [finite Gaussian sum](Lean/IPRADerivations/Analysis/GaussianRationalFiniteSum.lean)
   prove the actual recurrences and algebra used by the now-proved literal
   inverse-binomial Pascal row and its source-identity binding. Generic
   completed-field and the remaining
   representation adapters stay separate; the complete packet scope is retained.
   Adequacy now has a single closed proof of all its stated clauses,
   including both sharp represented estimates at the original C_Z/M_Z
   constants. The later unnumbered stage-distance/zero-distance corollary is also
   checked by an actual nonnegative fast PR2 diagonal distance name and
   both Member equivalence directions, including explicit stage k+3.
   Generic completed Gaussian-point and field realization remains separate.
5. **Coded field algebra:** actual runtime polynomial buffers, convolution
   product, monic companion and quotient/remainder programs are now checked in
   [GaussianRationalPolynomialBuffers](Lean/IPRADerivations/Analysis/GaussianRationalPolynomialBuffers.lean),
   [GaussianRationalPolynomialProduct](Lean/IPRADerivations/Analysis/GaussianRationalPolynomialProduct.lean),
   [GaussianRationalMonicCompanion](Lean/IPRADerivations/Analysis/GaussianRationalMonicCompanion.lean)
   and [GaussianRationalMonicReduction](Lean/IPRADerivations/Analysis/GaussianRationalMonicReduction.lean).
   The original coefficient lengths and literal monic head alone yield actual
   canonical quotient/remainder lists and the exact evaluator identity at
   every internal base-field point. The quotient length M+2 is deliberately
   coarse; the remainder has D entries. No output law is an input.
   [GaussianRationalMonicReconstruction](Lean/IPRADerivations/Analysis/GaussianRationalMonicReconstruction.lean)
   now proves the actual coefficient identity for those SAME returned Q/R
   codes and the actual convolution product, on the common width D+M+2.
   Original shapes/monicity and the queried index bound suffice. The source
   input is recoded coefficientwise; arbitrary outer-list codes are not
   identified. A genuine fixed-index QF prefix induction derives this identity
   without an evaluator premise, and an actual PR4 reconstructed buffer has
   the proved entries, length and canonicality. This remains an exact Q(i)
   dependency. [GaussianPolynomialMonicCompanion](Lean/IPRADerivations/Analysis/GaussianPolynomialMonicCompanion.lean)
   now constructs an actual companion step over Q(i)[X], with internally
   quantified Y row count and X degree bounds. Original row shapes yield
   literal stored coefficient cancellation, including the true constant-one
   monic top-row convolution, before scalar/two-variable specialization.
   The last shifted row is explicitly zero; raw inputs, m=1 and a=c=0 are
   covered. [GaussianPolynomialMultiplicationMatrix](Lean/IPRADerivations/Analysis/GaussianPolynomialMultiplicationMatrix.lean)
   now constructs actual numerical-dimension polynomial columns and the source
   row-major matrix. Complete coefficients are retained at a proved uniform X
   width; genuine compiled QF stage invariants and explicit Y-row reversal
   derive the literal evaluation-row identity at the actual curve point.
   [GaussianRationalPolynomialDegree](Lean/IPRADerivations/Analysis/GaussianRationalPolynomialDegree.lean)
   supplies the actual canonical trim/computed degree and root-bound adapter
   from the original nonzero-coefficient existence, including zero/default
   semantics. [GaussianRationalPolynomialProductDegree](Lean/IPRADerivations/Analysis/GaussianRationalPolynomialProductDegree.lean)
   now derives the actual product's leading value/nonvanishing and computed
   degree from the SAME coefficient convolution and factor scans; raw and
   zero-factor cases have explicit source scopes. The actual numerical
   determinant and norm give the local and accumulated multiplicity proofs
   for the exact Gaussian-rational coding. The source superelliptic theorem
   now gives the weighted degree, leading coefficient and weighted point
   bound in the same coding. The original proper-subspace application
   computes its annihilator by Gaussian elimination. The subsequent
   finite covering implication is proved for the supplied family.
   Arbitrary high-Y reduction, its literal stored division identity,
   and the explicit completed Vandermonde formula are checked in this
   Gaussian-rational coding. Further coded-field instances remain open.
6. **Verification:** register each completed module in `IPRADerivations`, audit
   its named public endpoints in `Checks/Axioms.lean`, run normal Lake builds
   and the source import-closure gate, and document exact assumptions and
   malformed-code conventions. Reports must not count target definitions or
   native semantic proofs as object derivations.

The complete packet remains unfinished. This audit keeps all 17 source claims
and the explicit descent/field/representation boundaries in view while work
proceeds on independently checkable proofs.
