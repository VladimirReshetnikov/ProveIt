# Lean and source audit for the continuous iPRA framework

## Scope and baseline

The inspected repository snapshot is
`VladimirReshetnikov/ProveIt@5f3be02388442f16487d2dc5c2529961dd783d2b`
(20 November 2026).  The audit read actual source modules, not just the
packet summaries.  The main README's description of roughly thirty
derived packets is a coarse summary: the pinned `Derivations` tree contains
many newer analysis and foundations modules.  A generic account of finite
certificates, finite nets, or name coherence alone would duplicate existing
work.

Source files were retrieved with the selected GitHub connector.  Their
Git blob identifiers and local SHA-256 hashes are recorded in
`source_audit.json`.  The existing ProveIt modules were **inspected, not
rebuilt in this session**.  When this audit says that an existing source
contains an object endpoint, it means its declared conclusion is a value
of `Prf PRAAx`; it does not certify a fresh replay of the whole repository.

## Relevant existing modules

All paths below are relative to
`Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/`.

| Module and exact endpoint | Existing content | Boundary that remains relevant |
| --- | --- | --- |
| `Foundations/BoundedSyntax.lean`: `BoundedSyntax.boolean_reflection_closed` | Compiles one arity-indexed bounded formula to an actual PR symbol and derives Boolean reflection of the literal source formula. | Compilation recurses externally on fixed syntax. It is not an internal universal PR evaluator. |
| `Foundations/BoundedSyntaxInduction.lean`: `induction`, `induction_at` | Derived bounded-formula induction by QF induction on the compiler bit. | Local hypotheses may be arbitrary formulas, but the induction formula must be the compiled bounded one. |
| `Foundations/TraceReflection.lean`: `trace_at`, `trace`, `loop_compile` | Actual primitive-recursive run, QF invariant, and open base/step/final obligations. | Establishing an application invariant is still required; finite trace checking is not unrestricted semantic reflection. |
| `Foundations/GuardedLoop.lean`: `loop_at` | Handles transition assumptions that are valid only below the supplied bound. | The quantifier-free invariant is guarded by `t ≤ N`, with the external guard kept in the context. |
| `Foundations/FiniteQueryDemand.lean`: `finiteMaximum` and its laws | Computes actual maxima of variable finite query families; supplies backward demand envelopes. | Does not justify an unbounded oracle or an unsupported uniform evaluator. |
| `Foundations/FiniteNet.lean`: `finite_net_closed` | Coverage, modulus, property stability, and correctness at net points imply the relaxed property at every represented domain point. | Coverage and the modulus remain explicit premises of this general theorem. |
| `Foundations/ApproximateWitness.lean`: `argmin_spec`, `argmin_minimal`, `approximate_witness` | Actual least finite argmin and finite-net residual estimates. | A residual bound does not imply that independently selected witnesses form a Cauchy sequence. |
| `Foundations/StrongMinimizer.lean`: `selected_pair_stable` | Converts residual estimates for actual finite-net minimizers into a distance estimate using an explicit strong-convexity certificate and schedule. | General residual-diameter regularity is a genuine generalization; merely repeating strong convexity is not. |
| `Analysis/RationalArgmin.lean`: `selected_spec`, `selected_minimal`, `selected_least` | Actual least minimization of signed rational values with independent positive denominators. | The evaluator is a fixed `PR 2` program. No common denominator is needed in this existing implementation. |
| `Analysis/DyadicCauchy.lean`: `dyadic_cauchy`, `certificates_coherent` | Derives all-pairs coherence from adjacent motion, and derives motion from local certificate hypotheses. | Coherence hypotheses are mathematical content, not an automatic consequence of finite solvability. |
| `Foundations/FiniteHausdorff.lean` and `FiniteHausdorffImage.lean`: `local_image_closed`, `rational_scaled_image_closed` | Actual nearest-neighbor/min/max scans and image bounds from finite local metric laws. | Common-scale or independent-scale adapters and supplied local Lipschitz laws are retained. |
| `Foundations/SetoidInterpretation.lean`: `Presentation`, `sound` | Transports intuitionistic first-order proofs through domain/equivalence presentations. | Domain closure, equivalence congruence, and translated axiom derivations must be supplied. It does not create all real objects. |
| `Foundations/UniversalEvaluatorObstruction.lean`: `no_universal_primitive_recursive_evaluator`, `diagonal_obstruction` | Separates an external semantic diagonal theorem from its object arithmetic counterpart. | Prohibits collapsing every PR code into one total internal PR evaluator. |
| `Foundations/CoherenceObstruction.lean`: `no_coherent` | A finite arithmetic diagonal obstruction is derived for persistent bounded simulation observations. | The final “no computable branch” conclusion also uses an external fact about the simulator's indices; the file explicitly does not formalize that final semantic step. |
| `Foundations/FiniteUseSignObstruction.lean`: `no_exact_sign_machine` | An external Lean metatheorem derives finite-use continuity of an actual oracle machine and rules out exact sign selection. | It is a semantic representation theorem, not a new object sentence of iPRA. |
| `Foundations/PrecisionCostDAG.lean`: `actual_rational_budget_program_closed` | Actual runtime rational error propagation over a finite dependency graph. | Quantitative local error estimates remain the application's responsibility. |

The new project should use these modules as the arithmetic backend.  The
continuous model-theoretic contribution is the **uniform transfer through
nested infimum/supremum formulas under a total correspondence**, including
the absence of a quantifier-rank loss for nonexpansive connectives.  The
completion, gluing, function-space, and residual-diameter results are
application-level mathematical work, not new claims that the repository
lacked finite loops or finite minima.

## What was actually checked in this session

The official Lean 4.32.0 release was downloaded and invoked locally.  It
reports compiler commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`.
The five-module project in `work/lean/` has no dependencies beyond the
bundled standard library and builds successfully with `lake build`.

The principal theorem is
`QuantitativeIPRA.Continuous.formula_transfer`.  Its syntax is genuinely
arity indexed.  Its model contains a nonempty finite carrier indexed by
`0,...,last` and an atomic interpretation.  A correspondence between two
models is total in both directions and controls every atomic predicate on
every related tuple.  The theorem proves that a common score error `e` is
preserved by constants, minimum, maximum, truncated complement, and any
finite nesting of infimum/supremum quantifiers.  The two models may have
different finite carrier sizes.  It is not restricted to shared lists.

The proof derives the infimum/supremum cases from the separately checked
`min_correspondence` and `max_correspondence`.  For minima, a minimizer of
the right model is transported to a related left point to get one
inequality; a left minimizer gives the converse.  Thus no factor equal to
the number of samples or quantifier depth enters the bound.  Explicit
primitive recursions define all finite extrema and argmin/argmax selectors.

The additional checked `ScoreNet` lemmas retain mesh and evaluation
hypotheses and prove:

* finite extrema approximate all semantic values with mesh plus evaluation
  error;
* the selected finite argmin gives an actual point with error
  `meshError + 2*evaluationError` against any point;
* two unrelated nets of the same observable have extrema within
  `max(meshError,meshError') + evaluationError + evaluationError'`;
* bounded perturbation of the value function adds exactly that perturbation
  to the comparison bound.

An explicit endpoint/midpoint tent-function example proves that the
correspondence error can be attained.  It provides a checked example of a
quantifier changing the value between different nets while satisfying the
transfer theorem.

The `#print axioms` output is in `lean/axiom-audit.txt`.  The principal
theorems depend on Lean's `propext` and `Quot.sound`; none of the audited
theorems depends on `Classical.choice` or `sorryAx`.  These are metatheoretic
kernel dependencies, not extra axioms added to iPRA.

## Precise formalization status

The new `.lean` files prove **semantic Lean propositions**.  They are not
claimed to produce new `Prf PRAAx` proof values.  Their type-level function
parameters and arbitrary `ScoreNet` carrier type belong to Lean's
metatheory.  The human arithmetic proofs admit the fixed-program iPRA
specialization described in the report, but the reification into the
repository's actual object syntax remains to be implemented.

`lean/ObjectTheoryPlan.lean.txt` gives the exact formulas, imports,
constructor choices, existing endpoint names, and proof obligations.  It
specifies a two-sided bounded correspondence in the object language, the
two exact new min/max endpoints, and an external fixed-formula compiler
that constructs PR evaluator syntax and object proof values in parallel.
It also identifies the rational, environment-coding, finite-net, modulus,
and coherence adapters that must be proved for each application.

There is no claimed general “Lean implies iPRA” translator, no new
universal program evaluator, no unchecked `sorry` filled into a theorem,
and no closed iPRA claim obtained by dropping a certificate premise.

## Suggested integration order

1. Add object min/max correspondence lemmas to
   `IPRADerivations/Foundations/ContinuousQuantifier.lean`, using the actual
   selected extrema and `BoundedSyntax` to retain precise bounded formulas.
2. Define a fixed finite continuous-formula frontend whose generated
   evaluator programs reuse those folds.  Generate its object transfer
   proof by external structural recursion.  Add explicit equations for
   packing and extending the environment.
3. Instantiate the frontend for compact metric nets and derive the
   finite cross-net relations from the paper's coverage and modulus
   estimates.  Export the Cauchy inequality at arbitrary numerical
   precisions before introducing an external real-valued interpretation.
4. For completion, gluing, and function-space applications, keep the
   geometric certificate production separate from structural transport.
   Derive each claimed certificate or leave its exact assumption in the
   endpoint.  Use the existing guarded-loop and Boolean induction APIs
   when runtime list lengths vary.
5. Replay the new object modules at the pinned repository toolchain and
   audit their actual endpoint types and axioms.  Only after these gates
   should the new results be counted as completed `Derivations` entries.
