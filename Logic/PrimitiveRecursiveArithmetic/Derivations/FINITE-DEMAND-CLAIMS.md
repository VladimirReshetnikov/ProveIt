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
| `thm:nonlinear-name-validity`, [02_backward_induction.tex](../docs/proofs/foundations/ipra_finite_demand/sections/02_backward_induction.tex) | **Open actual logistic-name instance.** The general predetermined recursion is checked, as are generic rational-name arithmetic components. | Encode the actual clipping, rational logistic map and shifted name evaluator; prove range, the Lipschitz constant four, the parameter-shift identity, initial observations and the `K+2N` schedule. Generic transfer alone does not prove those local inequalities. |
| `lem:aggregate-calculus`, [03_aggregates.tex](../docs/proofs/foundations/ipra_finite_demand/sections/03_aggregates.tex) | **Open object implementation of the finite metric interface.** The archived `FiniteHausdorff` results are native Lean proofs. | For actual nonempty coded finite lists, implement and reflect the two-sided cover checker and prove triangle, concatenation, sup-product, Lipschitz image, and distance-to-set estimates. Empty/malformed codes need explicit validity conventions. |
| `thm:aggregate-chain`, [03_aggregates.tex](../docs/proofs/foundations/ipra_finite_demand/sections/03_aggregates.tex) | **Partial components.** Actual least finite selectors and rational telescoping are checked in [ApproximateWitness](Lean/IPRADerivations/Foundations/ApproximateWitness.lean) and [Analysis/RationalSummableTails](Lean/IPRADerivations/Analysis/RationalSummableTails.lean). They do not construct this chain. | Build the actual least-neighbor PR sequence; derive list membership and the sharp `3·2^(-j)(1−2^(-(v−j)))` bound; verify its reindexed point-name program, support membership and initial-point distance. Do not assume a limiting point or an already coherent selected chain. |
| `thm:aggregate-optimization`, [03_aggregates.tex](../docs/proofs/foundations/ipra_finite_demand/sections/03_aggregates.tex) | **Partial components.** `ApproximateWitness` proves actual finite minimization and its explicit coverage/modulus/evaluation-error consumer. | Construct the aggregate value name and prove its regularity and lower-bound meaning; combine the actual finite minimizer with the chain constructor to produce the full two-parameter approximate-point-name family. Preserve the `(4L+2)` budget. No exact minimizing point or cross-precision coherence of selected minimizers is supplied. |
| `lem:product-stability`, [04_root_sets.tex](../docs/proofs/foundations/ipra_finite_demand/sections/04_root_sets.tex) | **Open.** The scalar bisection/factor identities in `Analysis/PolynomialBisection` concern another root representation. | Encode Gaussian-rational product coefficients; derive evaluation error at each supplied factor, squared-norm product comparisons and actual bounded nearest-neighbor witnesses in both directions, including repeated roots and zero tolerance. |
| `thm:approx-factor`, [04_root_sets.tex](../docs/proofs/foundations/ipra_finite_demand/sections/04_root_sets.tex) | **Open actual uniform factorization constructor, conditional on the source's explicit rational-descent lemma (RD).** | Reify the specified descent clock, synthetic division, coefficient bounds `A_j`, product budget `L`, and finite deflation; derive the complete coefficient-norm error. Keep the exact (RD) assumption and its upstream proof status visible. Neither a root object nor the desired factorization may be an input premise. |
| `thm:root-support`, [04_root_sets.tex](../docs/proofs/foundations/ipra_finite_demand/sections/04_root_sets.tex) | **Open source aggregate-root constructor.** The existing real scalar bracket/name construction has different inputs, observations and guards. | Combine actual approximate factorization, sampled coefficient names, the explicit `E(t)` schedule and product stability; prove the common final-coefficient radius bound and arbitrary-index Hausdorff coherence, with internal numerical degree where the source requires uniformity. |
| `prop:root-adequacy`, [04_root_sets.tex](../docs/proofs/foundations/ipra_finite_demand/sections/04_root_sets.tex) | **Open.** Generic polynomial residual/name bounds are useful components but do not identify this finite-set membership predicate. | Derive both explicit evaluation/distance error inequalities, sampled square-root/minimum observations, PR root-to-membership indices and both object-theory implications between represented zero and the exact quantified `Member` predicate. Retain the supplied point bound `Z`. |
| `thm:general-norm`, [05_norm_certificates.tex](../docs/proofs/foundations/ipra_finite_demand/sections/05_norm_certificates.tex) | **Open actual polynomial-norm zero-count endpoint.** Fixed-dimension signed matrix arithmetic in [Core/LinearAlgebra](Lean/IPRADerivations/Core/LinearAlgebra.lean) supplies only part of the required algebra. | Construct monic reduction and the multiplication matrix over the coded field, prove finite root bounds, evaluation-row identities, Vandermonde independence, determinant divisibility at each fiber and total multiplicity counting. Preserve the essential nonzero-computed-norm premise, including singular/ramified cases. |
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
   root-membership directions.
5. **Finite field algebra:** actual monic reduction/determinant programs,
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
