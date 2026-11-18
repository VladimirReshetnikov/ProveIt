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
| `thm:approx-factor`, [04_root_sets.tex](../docs/proofs/foundations/ipra_finite_demand/sections/04_root_sets.tex) | **Checked full actual uniform construction with a concrete monic instance.** [GaussianApproximateFactorization](Lean/IPRADerivations/Analysis/GaussianApproximateFactorization.lean) proves `uniform_approximate_factorization_closed`, `returned_approximate_factorization_closed` and `returned_product_evaluation_closed`. The actual PR4 returns N computed roots and the actual degree-N product coefficients, with full coefficient L1 error≤eta=p/q. Numerical C,N,p,q are internal. [Parameters](Lean/IPRADerivations/Analysis/GaussianFactorParameters.lean) computes A0 and epsilon=p/(2NLq); [stage bounds](Lean/IPRADerivations/Analysis/GaussianFactorBounds.lean) derives the whole coefficient invariant by compiled bounded induction and each root radius using the proved [monic residual-radius theorem](Lean/IPRADerivations/Analysis/GaussianMonicResidualRadius.lean). Actual [linear multiplication/error transport](Lean/IPRADerivations/Analysis/GaussianRationalDeflationError.lean), [product reconstruction](Lean/IPRADerivations/Analysis/GaussianRationalReconstruction.lean) and [weighted budgets](Lean/IPRADerivations/Analysis/GaussianWeightedErrorBudget.lean) give the complete backward QF error proof. | No mathematical remainder for this conditional theorem in the stated coding: the input is a coefficient list of length N+1 with literal canonical leading coefficient one, N≥1 and 1≤p≤q. The additional premise is precisely `GaussianFactorParameters.monicRD`, a uniform local contraction for proper monic polynomials, from which stage residuals are derived. The concrete fixed step is now constructed in [GaussianMonicRD](Lean/IPRADerivations/Analysis/GaussianMonicRD.lean), and [GaussianMonicApplications](Lean/IPRADerivations/Analysis/GaussianMonicApplications.lean) proves the actual and returned approximate-root/factorization instances with that RD premise discharged internally. The generic interface retains its step argument; the general nonmonic FTA remains separate. The alternative bounded-grid interface, general convolution norm identity and separately expanded (TE) coefficient sum remain unformalized and unclaimed. The proved source coefficient-error target uses the equivalent actual one-step error recurrence and backward prefix-weighted induction. Root existence, desired factorization/error and global stage invariants are not premises. |
| `thm:root-support`, [04_root_sets.tex](../docs/proofs/foundations/ipra_finite_demand/sections/04_root_sets.tex) | **Checked full source construction with a concrete fixed-step instance.** [GaussianRootSupport](Lean/IPRADerivations/Analysis/GaussianRootSupport.lean) proves `collision_tolerant_root_support_closed`, the original two-cover checker and the actual PR3 root-name program. [GaussianCoefficientNameBounds](Lean/IPRADerivations/Analysis/GaussianCoefficientNameBounds.lean), [GaussianRootSchedule](Lean/IPRADerivations/Analysis/GaussianRootSchedule.lean), [GaussianRootSamples](Lean/IPRADerivations/Analysis/GaussianRootSamples.lean), [GaussianRootRadius](Lean/IPRADerivations/Analysis/GaussianRootRadius.lean) and [GaussianRootCoefficientCoherence](Lean/IPRADerivations/Analysis/GaussianRootCoefficientCoherence.lean) construct exact source A/R/b/E(t), actual sample/factor programs, final coefficient radius A, listed-root radius A+2 and coefficient discrepancy 4*2^-E(t). [GaussianRootStability](Lean/IPRADerivations/Analysis/GaussianRootStability.lean) derives both original Euclidean covers at 2^(-t-2). Numerical degree, data and all precisions are internal; only fixed PR schemas are external. | No mathematical remainder for this source result in the chosen coding. The generic interface retains the local monic RD contract; [GaussianMonicRootSupport](Lean/IPRADerivations/Analysis/GaussianMonicRootSupport.lean) discharges it using the proved fixed step and exports `concrete_root_support_closed`, actual named/returned covers and checker acceptance. Only genuine CN, positive degree and stage order remain. The original root-name PR3, coefficient errors, radii, product evaluation, listed zeros and returned fields are audited. No final radius, factorization/coherence law, root separation or cover is an input premise. |
| `prop:root-adequacy`, [04_root_sets.tex](../docs/proofs/foundations/ipra_finite_demand/sections/04_root_sets.tex) | **Checked full source proposition and concrete completed-distance instance.** [GaussianRootAdequacyTheorem](Lean/IPRADerivations/Analysis/GaussianRootAdequacyTheorem.lean) proves the single closed `root_adequacy_closed` sentence: actual P-value fastness, literal quantified Member iff actual polynomial-program zero, all-stage nonnegative fast Euclidean distance names, both sharp represented error cuts and the source PR forward stage at every precision. [SharpEvaluation](Lean/IPRADerivations/Analysis/GaussianRootSharpEvaluation.lean) proves `root-eval-error` at exact 2*C_Z/D; [SharpDistance](Lean/IPRADerivations/Analysis/GaussianRootSharpDistance.lean) proves `root-distance-residual` as the genuine two-name order cut at exact M_Z/C_R. The original Z is retained; sample disk Z+1 is derived from its represented norm bound. All degrees, data, stages and precision indices are internal. [Actual power envelopes](Lean/IPRADerivations/Analysis/GaussianRationalPowerEnvelope.lean), [rational-disk Lipschitz](Lean/IPRADerivations/Analysis/GaussianRationalHornerRadiusLipschitz.lean), [finite slack removal](Lean/IPRADerivations/Analysis/GaussianFastValueCut.lean), [distance upper cuts](Lean/IPRADerivations/Analysis/GaussianEuclideanDistanceUpperCut.lean) and [actual affine distance names](Lean/IPRADerivations/Analysis/GaussianLinearDistanceName.lean) supply derived components. | No mathematical remainder for the displayed proposition in the chosen original rational/name coding under its genuine CN/pointCN, numerical disk/degree and local RD assumptions. The later unnumbered stage-distance/zero-distance corollary is checked by [DistanceCompletion](Lean/IPRADerivations/Analysis/GaussianRootDistanceCompletion.lean) and [DistanceZero](Lean/IPRADerivations/Analysis/GaussianRootDistanceZero.lean); [CompletedAdequacy](Lean/IPRADerivations/Analysis/GaussianRootCompletedAdequacy.lean) identifies its literal zero predicate with literal P-program zero. [GaussianMonicRootAdequacy](Lean/IPRADerivations/Analysis/GaussianMonicRootAdequacy.lean) now exports the full original proposition and completed corollary with RD discharged internally, retaining original C_Z/M_Z and genuine CN/pointCN/disk/degree guards. It binds the actual PR3 root and PR2 polynomial/distance names and proves membership iff actual polynomial-name zero iff completed distance-name zero. Distance completion and its membership equivalence require only CN, pointCN and positive degree. Generic completed Gaussian-point and field realization remains separate. No desired error/coherence/order, represented minimizing root or output invariant is an input. |
| `thm:general-norm`, [05_norm_certificates.tex](../docs/proofs/foundations/ipra_finite_demand/sections/05_norm_certificates.tex) | **Partial dependency; polynomial-norm endpoint open.** [Algebra/PolynomialFiniteRoots](Lean/IPRADerivations/Algebra/PolynomialFiniteRoots.lean) proves actual fraction-free coded synthetic division, leading scaling/nonzero preservation, distinct-root removal and closed `finite_root_bound_closed` for a fixed external degree with arbitrary internal rational root-list length. It assumes only a nonzero decoded leading coefficient, bounded actual root equations, independent denominator positivity and cross-distinctness. The concrete exact Q(i) endpoint [GaussianRationalFiniteRoots](Lean/IPRADerivations/Analysis/GaussianRationalFiniteRoots.lean) now makes the degree numerical: original length N+1, nonzero recoded head, actual root evaluations and pairwise nonzero qsub values imply length<=N by genuine QF proofs for actual PR4 quotient stages. The actual tagged trim in [GaussianRationalPolynomialDegree](Lean/IPRADerivations/Analysis/GaussianRationalPolynomialDegree.lean) now removes leading field-zero coefficients and derives the root bound at its computed degree from original nonzero-coefficient existence. The zero tag has an explicit sentinel; generic coded-field adapters remain separate. Fixed-dimension signed matrix arithmetic in [Core/LinearAlgebra](Lean/IPRADerivations/Core/LinearAlgebra.lean) supplies only part of the required algebra. | The actual polynomial-valued multiplication matrix and its evaluation-row identity for the original reduced-Y representation are now constructed in GaussianPolynomialMultiplicationMatrix. Complete general high-Y reduction/quotient witnesses and remaining coded-field representation adapters, then prove Vandermonde independence, determinant divisibility at each fiber and total multiplicity counting. Preserve the essential nonzero-computed-norm premise, including singular/ramified cases. |
| `thm:norm-degree`, [05_norm_certificates.tex](../docs/proofs/foundations/ipra_finite_demand/sections/05_norm_certificates.tex) | **Open weighted determinant endpoint; exact product-degree dependency checked.** [GaussianRationalPolynomialProductDegree](Lean/IPRADerivations/Analysis/GaussianRationalPolynomialProductDegree.lean) derives genuine leading-coefficient multiplication/nonvanishing and computed degree additivity for the SAME actual Gaussian-rational convolution from original nonzero factors, with separate zero-factor cases. This does not yet prove the unique maximal weighted determinant term or superelliptic norm nonvanishing. | For `m≥2`, `deg f=d≥1`, `gcd(m,d)=1` and nonzero canonical remainder `G=Σ_{i<m} A_i Y^i`, derive the unique maximal weighted term, the permutation `j↦(j+k) mod m`, its sign, exact leading coefficient, and exact degree `W(G)` from the actual determinant constructor. |
| `cor:norm-zeros`, [05_norm_certificates.tex](../docs/proofs/foundations/ipra_finite_demand/sections/05_norm_certificates.tex) | **Open.** | Compose the actual general norm bound and degree/nonvanishing theorems with identical coded polynomials, field data and finite-point predicates. Numerical examples do not establish either premise. |
| `cor:norm-subspace`, [05_norm_certificates.tex](../docs/proofs/foundations/ipra_finite_demand/sections/05_norm_certificates.tex) | **Open actual annihilator producer and zero-count application.** | Implement bounded Gaussian elimination on the supplied row matrix, produce a nonzero annihilator with the actual pivot/free-column equations, prove its canonical polynomial has `W(G)≤L`, transfer all supplied evaluation-vector memberships to zeros and apply the sharp count. A supplied annihilator certificate is a conditional consumer, not the missing producer. |

The additional displayed equation `eq:constant-loss-budget` is checked in
[BackwardDemandBounds](Lean/IPRADerivations/Foundations/BackwardDemandBounds.lean).
`numerical_constant_schedule` quantifies the loss internally and proves
`h(t)=K+c*(N∸t)` for the actual PR schedule. The general version computes
`c=loss(x)` from persistent data and `constant_loss_transfer_closed` derives
the explicit initial budget. Stage-dependent additive losses and their finite
sum formula remain separate.


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
   zero-factor cases have explicit source scopes. General high-Y reduction
   and symbolic quotient witnesses,
   remaining field representations, numerical-dimension determinant/norm
   programs, fiber multiplicity/nonvanishing proofs and the Gaussian-elimination
   annihilator producer remain. An
   all-point base-field evaluator identity does not by itself instantiate an
   extension field. Supplied and constructed certificates retain separate
   acceptance claims.
6. **Verification:** register each completed module in `IPRADerivations`, audit
   its named public endpoints in `Checks/Axioms.lean`, run normal Lake builds
   and the source import-closure gate, and document exact assumptions and
   malformed-code conventions. Reports must not count target definitions or
   native semantic proofs as object derivations.

The complete packet remains unfinished. This audit keeps all 17 source claims
and the explicit descent/field/representation boundaries in view while work
proceeds on independently checkable proofs.
