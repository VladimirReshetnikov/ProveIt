# Foundation audit and continuous-object extension

## Scope and evidence

Repository: `VladimirReshetnikov/ProveIt`.

Pinned revision: `5f3be02388442f16487d2dc5c2529961dd783d2b`.

Reviewed through the selected GitHub connector. I read the current `UNIFICATION-PLAN.md`, `ENDPOINTS.md`, the current Derivations README and progress log, selected original framework papers, and the actual source of the modules listed below. The source snapshots are under `research/foundation_sources/`. This was a source audit; I did not replay the root Lake build. References to checked upstream derivations describe the source's object judgments and upstream status, not a fresh independent build of this archive.

The top-level `PrimitiveRecursiveArithmetic/README.md` is materially less current and less detailed than `Derivations/README.md`. The latter was approximately 886 KB at the pinned revision. It records many more source theorems than the overview's older packet intake summary. A claim that all topology/category/continuous results are still merely packet outlines would be false.

## Existing work that should be reused, not announced as a new framework

All paths below are relative to `Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/`.

| Source | Actual present interface | Boundary retained by the source |
|---|---|---|
| `Foundations/SetoidInterpretation.lean` | General relative interpretation of one-sorted intuitionistic first-order equational syntax; arbitrary formulas `D` and `E`; substitution and equality congruence; `sound` transports object derivations. | It is an external proof-translation theorem. The current implementation is one-sorted and has equality atoms; many-sorted syntax and general relation symbols are not implemented there. Each interpreted source axiom still needs an actual derivation. |
| `Foundations/PresentedCategory.lean` | Fixed iPRA formulas `Obj`, `Hom`, `Eqv`; fixed terms for identity and composition; laws supplied as derivable rules. Derives inverse uniqueness, section/monic, retraction/epic, terminal uniqueness, with a concrete additive-monoid instance. | It does not create a universe of all maps or a total universal PR evaluator. Generic category axioms remain supplied proof fields until a concrete category is instantiated. |
| `Foundations/Yoneda.lean` | Presentation-wise Yoneda identity; naturality of the represented construction; representable case; a closed additive-monoid example. | This is not a blanket universe of arbitrary functors/natural transformations with PR evaluation. |
| `Foundations/BoundedSyntax.lean` | Actual arity-indexed bounded syntax `BFm n`; first-order interpretation; capture-avoiding substitution; compilation and object proof of the Boolean equivalence. | The compiler is external structural recursion on one fixed syntax tree, not an internal PR evaluator for arbitrary PR symbols. |
| `Foundations/BoundedSyntaxInduction.lean` and `BoundedSyntaxBackwardInduction.lean` | Already present in tree and described in README: genuine bounded-formula induction through the Boolean compiler, with contexts and runtime bounds. | No stronger unrestricted induction is introduced. The audit read the Boolean frontend but did not independently replay those modules. |
| `Foundations/FiniteQueryDemand.lean` | Actual runtime maximum over internally varying query families; proved index bounds; a literal source formula adapter; observational induction under genuine local transfer hypotheses. | Query-demand correctness is not a magical provider of correctness or termination of arbitrary external observations. |
| `Foundations/FiniteQueryTable.lean` | `table_good`, `table_entry`, and `fix_precision`: finite Boolean table reasoning followed by universal introduction. | The fact that the fields exist is not supplied merely by Boolean verification of a hypothetical table. |
| `Foundations/CoherentTower.lean` | Actual least lifting selector under a bounded surjective-lifting contract; PR point recursion; `pt_mem`, `pt_coherent`, `tower_closed`; binary-tree instance. | Infinite height without a lifting/viability resource is not the hypothesis. No arbitrary infinite-tree branch theorem follows. |
| `Foundations/CoherentMinimizer.lean` | Coherent extraction from approximate minimizers and a quantitative uniqueness modulus; monotone modulus normalization and the Cauchy estimate `cauchy`. | Canonical completed evaluation `f(X)=V` and uniqueness of the completed name are explicitly not derived there. |
| `Foundations/StrongMinimizer.lean` | Actual finite-net least-argmin points; residual bounds; a rational pair-distance estimate from a separate strong-convexity certificate. | Completed-domain minimizer existence and evaluator/denominator compatibility remain application obligations. |
| `Foundations/ContractionIterates.lean` | Abstract coded space with a decidable ball, cleared distance, and PR step; contraction iteration and a genuine QF proof of a Cauchy estimate. | Coefficient names and analytic majorant construction are not supplied by this arithmetic theorem. |
| `Foundations/DyadicNames.lean` | Sample stability, addition regularity, apartness-guarded reciprocal estimate on a common dyadic scale. | These finite rational estimates alone do not establish a sort of all internally coded continuous objects. |
| `Analysis/GaussianRootDistanceCompletion.lean` | Actual primitive-recursive diagonal name for Euclidean distance to the collision-tolerant polynomial-root support, with a derived modulus. | This is a specialized executable result with explicit input contracts, not a generic internal enumeration of completed spaces. |
| `Foundations/UniversalEvaluatorObstruction.lean` | External theorem `no_universal_primitive_recursive_evaluator`, based on the actual `PR.ev`; separate ordinary object-theory `diagonal_obstruction`. | It rules out a PR universal value function. It does not rule out an arithmetic evaluation graph or quantification over code domains with totality predicates. |
| `Foundations/FiniteUseSignObstruction.lean` | External oracle-machine proof that a total exact-sign selector for rapid names cannot be correct, even for rational limits. Execution locality is derived from explicit adaptive runs. | It is deliberately a representation/algorithm metatheorem rather than a `Prf PRAAx` theorem. |

The README also records current modules for discrete Gronwall, ODE refinement/uniqueness, finite-net transfer, finite products/exponentials, adjunctions, Kan formulas, trace compilers, and many concrete analytic identities. Those entries should guide targeted reuse, but a README row is not a substitute for reading each imported theorem's exact type.

## A current-source correction particularly relevant to analytic claims

The generic and concrete FTA work has advanced far beyond the initial packet outlines. Current entries include a concrete monic descent proof `GaussianMonicRD`, actual approximate-root/factorization constructors, concrete monic root-support/adequacy, and a general nonmonic finite residual construction `GaussianNonmonicRD` / `GaussianNonmonicApproximateRoot`. Root-distance completion is explicitly connected to an actual diagonal program.

Therefore the report should not suggest that supplying a finite root certificate or a scalar diagonal construction is a new solution to a previously untouched FTA obstruction. The defensible extension is to abstract the existing stable-observable and completion machinery, preserve its precise executable guarantees, and add a relational continuous-object layer with explicit totality assumptions.

## The useful new distinction: syntax can be PR while evaluation is relational

A false dichotomy would be: either fix every function externally or assume an impossible universal PR evaluator. There is a third possibility.

1. Use a fixed deterministic machine with a PR bounded trace predicate `T(e,x,t,a)`.
2. Define `Eval(e,x,a) := exists t, T(e,x,t,a)`.
3. Define a name-domain formula that includes `forall x, exists t,a, T(e,x,t,a)` and the appropriate cross-precision regularity.
4. Let operations act on program *codes*. Their code constructors are PR even when the created programs have no uniform PR evaluation bound.
5. Prove closure/congruence of those constructors from the arithmetical domain predicates.

Then a genuine first-order variable can range over continuous-object codes. The existing setoid interpretation accepts the arbitrary arithmetical domain/equality formulas. No universal total evaluator has been introduced.

This is not claimed as a novel computability-theoretic invention. It is a project-specific integration of the source's interpretation theorem, its evaluator obstruction, and the continuous representation contracts. Its mathematical value is to remove an unnecessary restriction while exposing the totality obligations hidden by a naive oracle formulation.

## Complete new section delivered

`ipra_continuous_framework/sections/relational_codes.tex` contains:

- Three-layer separation: executable PR schema, relational arithmetic presentation, external standard-space semantics.
- The bounded trace relation and concrete finite trace-assembly/decomposition requirements.
- A real-name domain `RN(e)` and cross-name relation `Near(e,f;r)` using only arithmetic quantifiers.
- Rational slack removal with explicit PR witness index `max(K0,(A+1)D)` for denominator product `D` and natural `A >= C`.
- Full human proof that the relational name domain is a setoid and that `Near` satisfies an exact triangle rule.
- Addition code closure and extensionality from a fixed number of totality witnesses; group laws; a bounded multiplication construction.
- A complete diagonal completion theorem for jointly total double names and a fixed PR monotone modulus: `x_k = a_(mu(p,k+2),k+2)`.
- A proof of the complete cross-index convergence relation, including the low output precisions, via rational slack removal.
- Independence of completion from rowwise equivalent presentations and differing moduli.
- The scalar-totality / finite-batch distinction, with three valid interfaces: fixed PR clock, batch certificate, or a specific adaptive-execution contract.
- A concrete Lean module plan and precise limitations of the currently existing object-interpretation backend.

The mathematical proofs make clear where the underlying trace constructor correctness must still be formalized. No placeholder is being counted as a checked theorem.

## The batch-totality issue is essential

`Tot(e) := forall n, exists t,a, T(e,n,t,a)` supplies any fixed finite number of witnesses by a finite first-order argument. This is sufficient for binary composition, sum/product, a single diagonal query, and an auxiliary precision used in slack removal.

A variable-length finite-net scan instead needs a tuple of traces for an internally varying number of requests. An informal induction on the existence of the prefix tuple has an existential, generally unbounded induction invariant. It is not the QF induction scheme of iPRA. A PR *checker* for the tuple is not a PR *producer* for it.

Do not assert unprovability of a general collection implication without a separate model-theoretic proof. The correct status here is that this implication is not supplied by the framework and is explicitly retained as an obligation. For executable PR observations, actual clocks/outputs construct the table and remove the issue. For nonadaptive code observations, a `BatchTotal` hypothesis can provide the table. For adaptive loops, a finite query envelope or a particular totality/trace theorem is needed; batch totality by itself should not be casually generalized to unrestricted adaptive calls.

Applications affected include numerical integration, finite-net extrema, continuous-logic bounded quantifier approximations, and variable-step Euler schemes. The analysis/model agents have been alerted to retain the appropriate fixed-PR-family assumptions.

## Other mathematical pitfalls to state explicitly

### Completion versus coherence

An approximation at every precision is not a point. One needs coherence directly, a construction of coherent selections, a quantitative uniqueness modulus, or a stable quotient observable that avoids selection. The repository already supplies important instances of all these strategies; generic claims must not erase the needed resource.

### Dense versus compact

A countable dense presentation with no finite-net bound is not an effective compact presentation. A finite-net proof of a supremum needs a quantitative continuity modulus and a PR net-size/content generator (or explicit batch evidence). Arbitrary open-cover compactness is not a consequence of naming conventions.

### Abstract semantics versus interpretation

Using Lean `Real`, `MetricSpace`, `Category`, or `Model` in a host proof does not produce an object-theory theorem. The object claim must be an actual arithmetic sentence and the target derivation must inhabit `Prf PRAAx`. Standard-space denotation and its soundness are separate external results.

### Interpreted induction

A QF source formula may become quantified when equality is replaced by extensional name equality. The ordinary iPRA QF induction axiom does not then apply to the translated formula. Interpreting an entire stronger theory requires proving each translated induction axiom, not only interpreting the underlying algebraic signature.

### Standard computable objects versus all classical objects

In the standard model, total computable name codes present computable reals (or the chosen represented structures). They do not enumerate all classical reals. A countable numeric presentation can still support useful first-order interpretation results, but the intended semantic class and any adequacy claim must be stated accurately.

### Internal reflection

An external Lean theorem producing a `Prf PRAAx` term from a fixed valid source proof is not the arithmetic sentence `forall p, Proof(p,phi) -> phi` for all formulas, and not a self-consistency theorem. The unified framework must never turn a generic proof-transformer correctness statement into uniform internal soundness by notation.

### Qualitative versus quantitative validity

The assertion that some continuity, convergence, or separation modulus exists is not an explicit PR resource. A client needs either a supplied numerical modulus with a derivation of its contract, or an actual construction and proof. A noncomputable/unknown modulus cannot be hidden inside a generic semantic structure field while calling the resulting algorithm primitive recursive.

## Recommended integration boundary

Use the existing `BoundedSyntax`, `FiniteQueryDemand`, finite table, rational arithmetic, and setoid libraries as the numerical/proof backend. Add a proposed `Foundations/RelationalNames` family in a future integration branch, with submodules for actual trace code, rational slack, name equality, fixed-call constructors, and diagonal completion. Keep generic many-sorted/relation-symbol interpretation as a named separate adapter task. Route finite-net and ODE clients through explicit PR-clock or batch interfaces.

The resulting report can honestly say that it resolves a conceptual obstruction to quantifying over continuous objects, provides complete human proofs for several closure/completion constructions, and identifies a missing collection obligation in naive universal-oracle arguments. It should not claim full formalization of all those generic constructions, unrestricted compactness, or an interpretation of arbitrary classical analysis in iPRA.

## Source URLs

Canonical URL prefix for every path above:

`https://github.com/VladimirReshetnikov/ProveIt/blob/5f3be02388442f16487d2dc5c2529961dd783d2b/Logic/PrimitiveRecursiveArithmetic/`

Direct principal sources:

- [Unification plan](https://github.com/VladimirReshetnikov/ProveIt/blob/5f3be02388442f16487d2dc5c2529961dd783d2b/Logic/PrimitiveRecursiveArithmetic/UNIFICATION-PLAN.md)
- [Endpoint receipts](https://github.com/VladimirReshetnikov/ProveIt/blob/5f3be02388442f16487d2dc5c2529961dd783d2b/Logic/PrimitiveRecursiveArithmetic/ENDPOINTS.md)
- [Current derivation inventory](https://github.com/VladimirReshetnikov/ProveIt/blob/5f3be02388442f16487d2dc5c2529961dd783d2b/Logic/PrimitiveRecursiveArithmetic/Derivations/README.md)
- [Setoid interpretation source](https://github.com/VladimirReshetnikov/ProveIt/blob/5f3be02388442f16487d2dc5c2529961dd783d2b/Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Foundations/SetoidInterpretation.lean)
- [Finite-query demand source](https://github.com/VladimirReshetnikov/ProveIt/blob/5f3be02388442f16487d2dc5c2529961dd783d2b/Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Foundations/FiniteQueryDemand.lean)
- [Universal-evaluator obstruction](https://github.com/VladimirReshetnikov/ProveIt/blob/5f3be02388442f16487d2dc5c2529961dd783d2b/Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Foundations/UniversalEvaluatorObstruction.lean)
- [Current specialized diagonal completion](https://github.com/VladimirReshetnikov/ProveIt/blob/5f3be02388442f16487d2dc5c2529961dd783d2b/Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Analysis/GaussianRootDistanceCompletion.lean)

