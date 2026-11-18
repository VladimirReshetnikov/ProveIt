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
| `thm:approx-factor`, [04_root_sets.tex](../docs/proofs/foundations/ipra_finite_demand/sections/04_root_sets.tex) | **Checked full actual uniform construction, conditional on explicit (RD).** [GaussianApproximateFactorization](Lean/IPRADerivations/Analysis/GaussianApproximateFactorization.lean) proves `uniform_approximate_factorization_closed`, `returned_approximate_factorization_closed` and `returned_product_evaluation_closed`. The actual PR4 returns N computed roots and the actual degree-N product coefficients, with full coefficient L1 error≤eta=p/q. Numerical C,N,p,q are internal. [Parameters](Lean/IPRADerivations/Analysis/GaussianFactorParameters.lean) computes A0 and epsilon=p/(2NLq); [stage bounds](Lean/IPRADerivations/Analysis/GaussianFactorBounds.lean) derives the whole coefficient invariant by compiled bounded induction and each root radius using the proved [monic residual-radius theorem](Lean/IPRADerivations/Analysis/GaussianMonicResidualRadius.lean). Actual [linear multiplication/error transport](Lean/IPRADerivations/Analysis/GaussianRationalDeflationError.lean), [product reconstruction](Lean/IPRADerivations/Analysis/GaussianRationalReconstruction.lean) and [weighted budgets](Lean/IPRADerivations/Analysis/GaussianWeightedErrorBudget.lean) give the complete backward QF error proof. | No mathematical remainder for this conditional theorem in the stated coding: the input is a coefficient list of length N+1 with literal canonical leading coefficient one, N≥1 and 1≤p≤q. The additional premise is precisely `GaussianFactorParameters.monicRD`, a uniform local contraction for proper monic polynomials, from which stage residuals are derived. Its fixed PR step and upstream FTA descent implementation/proof remain open; no unconditional approximate-root/factorization theorem is asserted. The alternative bounded-grid interface, general convolution norm identity and separately expanded (TE) coefficient sum remain unformalized and unclaimed. The proved source coefficient-error target uses the equivalent actual one-step error recurrence and backward prefix-weighted induction. Root existence, desired factorization/error and global stage invariants are not premises. |
| `thm:root-support`, [04_root_sets.tex](../docs/proofs/foundations/ipra_finite_demand/sections/04_root_sets.tex) | **Checked full source construction conditional on explicit local (RD).** [GaussianRootSupport](Lean/IPRADerivations/Analysis/GaussianRootSupport.lean) proves `collision_tolerant_root_support_closed`, the original two-cover checker and the actual PR3 root-name program. [GaussianCoefficientNameBounds](Lean/IPRADerivations/Analysis/GaussianCoefficientNameBounds.lean), [GaussianRootSchedule](Lean/IPRADerivations/Analysis/GaussianRootSchedule.lean), [GaussianRootSamples](Lean/IPRADerivations/Analysis/GaussianRootSamples.lean), [GaussianRootRadius](Lean/IPRADerivations/Analysis/GaussianRootRadius.lean) and [GaussianRootCoefficientCoherence](Lean/IPRADerivations/Analysis/GaussianRootCoefficientCoherence.lean) construct exact source A/R/b/E(t), actual sample/factor programs, final coefficient radius A, listed-root radius A+2 and coefficient discrepancy 4*2^-E(t). [GaussianRootStability](Lean/IPRADerivations/Analysis/GaussianRootStability.lean) derives both original Euclidean covers at 2^(-t-2). Numerical degree, data and all precisions are internal; only fixed PR schemas are external. | No mathematical remainder for this conditional source result in the chosen coding. The genuine CN assumption and local monic RD contract are retained; the upstream RD implementation/proof remains open. No final radius, factorization/coherence law, root separation or cover is an input premise. |
| `prop:root-adequacy`, [04_root_sets.tex](../docs/proofs/foundations/ipra_finite_demand/sections/04_root_sets.tex) | **Partial: both represented membership directions and the source PR forward stage checked.** [GaussianEuclideanDistanceName](Lean/IPRADerivations/Analysis/GaussianEuclideanDistanceName.lean) supplies the actual Euclidean fast distance name and represented-cut adapters. [GaussianRootMembership](Lean/IPRADerivations/Analysis/GaussianRootMembership.lean) proves the exact quantified `Member` predicate equivalent to normalized V_s vanishing by local stage elimination and [actual rational slack removal](Lean/IPRADerivations/Analysis/GaussianRationalSlackRemoval.lean). [GaussianPolynomialValueName](Lean/IPRADerivations/Analysis/GaussianPolynomialValueName.lean) constructs the genuine packed PR2 name for P(z) and proves its literal program-zero predicate equivalent to normalized vanishing. [GaussianRootAdequacy](Lean/IPRADerivations/Analysis/GaussianRootAdequacy.lean) proves `represented_root_membership_closed` and `primitive_represented_root_stage_closed` with the original supplied Z, deriving sample disk Z+1 from the represented point bound. Exact finite FE/Lipschitz/residual budgets and root-list witnesses remain checked components. | Prove the two additional sharp represented inequalities `root-eval-error` and `root-distance-residual`, with the original C_Z/M_Z constants; connect any further stage-distance completion claims explicitly. [Rational-disk Horner perturbation](Lean/IPRADerivations/Analysis/GaussianRationalHornerRadiusPerturbation.lean) supplies a finite component, not those inequalities. The complete source proposition is not yet credited as finished. |
| `thm:general-norm`, [05_norm_certificates.tex](../docs/proofs/foundations/ipra_finite_demand/sections/05_norm_certificates.tex) | **Partial dependency; polynomial-norm endpoint open.** [Algebra/PolynomialFiniteRoots](Lean/IPRADerivations/Algebra/PolynomialFiniteRoots.lean) proves actual fraction-free coded synthetic division, leading scaling/nonzero preservation, distinct-root removal and closed `finite_root_bound_closed` for a fixed external degree with arbitrary internal rational root-list length. It assumes only a nonzero decoded leading coefficient, bounded actual root equations, independent denominator positivity and cross-distinctness. Fixed-dimension signed matrix arithmetic in [Core/LinearAlgebra](Lean/IPRADerivations/Core/LinearAlgebra.lean) supplies only part of the required algebra. | Construct monic reduction and the multiplication matrix over the coded field, extend the rational finite-root family to the required runtime degree/field representation, then prove evaluation-row identities, Vandermonde independence, determinant divisibility at each fiber and total multiplicity counting. Preserve the essential nonzero-computed-norm premise, including singular/ramified cases. |
| `thm:norm-degree`, [05_norm_certificates.tex](../docs/proofs/foundations/ipra_finite_demand/sections/05_norm_certificates.tex) | **Open.** Small fixed-degree observation identities do not prove arbitrary superelliptic determinant nonvanishing. | For `m≥2`, `deg f=d≥1`, `gcd(m,d)=1` and nonzero canonical remainder `G=Σ_{i<m} A_i Y^i`, derive the unique maximal weighted term, the permutation `j↦(j+k) mod m`, its sign, exact leading coefficient, and exact degree `W(G)` from the actual determinant constructor. |
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
   is now checked conditional on the explicit local (RD) contract, using
   actual backward coefficient-error induction. The upstream (RD) proof
   remains open. The root-support construction is now checked under that
   same RD contract.
   Adequacy now has actual Euclidean distance names, both represented
   membership directions, a genuine P(z) value name and the source PR
   forward stage. Its two sharp represented error inequalities and any
   further stage-distance completion adapters remain as recorded above.
5. **Coded field algebra:** actual monic reduction/determinant programs,
   fiber multiplicity and degree proofs, and the Gaussian-elimination
   annihilator producer. Supplied certificates and constructed certificates
   have separate acceptance claims.
6. **Verification:** register each completed module in `IPRADerivations`, audit
   its named public endpoints in `Checks/Axioms.lean`, run normal Lake builds
   and the source import-closure gate, and document exact assumptions and
   malformed-code conventions. Reports must not count target definitions or
   native semantic proofs as object derivations.

The complete packet remains unfinished. This audit keeps all 17 source claims
and the explicit descent/field/representation boundaries in view while work
proceeds on independently checkable proofs.
