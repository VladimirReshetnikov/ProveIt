# FIBER source-claim audit

This audit covers the complete delivered packet
[`foundations/fiber_ipra_2026-11-16`](../docs/proofs/foundations/fiber_ipra_2026-11-16/).
It was reviewed against the implementation on 2026-11-17. It supplements the
packet's historical [theorem ledger](../docs/proofs/foundations/fiber_ipra_2026-11-16/metadata/THEOREM_LEDGER.md)
and the repository [progress report](PROGRESS.md). The delivered sources are
preserved. Their original statements that no new Lean module had been compiled
describe the delivered artifact, rather than the current implementation.

The inventory includes all 20 theorem, corollary and proposition environments,
the summable-tail assertion stated outside an environment, the interface proof
fields, all 28 targets in Appendix B, and the implementation and regression
obligations in the formalization plan. The packet contains no `lemma`
environment.

**Checked** below means that the displayed mathematical scope has an ordinary
`Prf PRAAx` derivation. A conditional object theorem retains its displayed
object-language hypotheses. A proof generator indexed externally by a fixed
formula, program symbol or quantifier pattern is distinguished from a single
object sentence quantifying over codes for all such inputs. **Partial** means
that checked components cover a stated subproblem and further mathematical or
representation work remains. **Open** means that the source claim has no
corresponding completed endpoint identified in this audit. No packet is counted
complete from a module name, a metadata record, a Python test, or a declaration
whose premises already contain the requested conclusion.

Implementation paths in the tables are relative to
[`Lean/IPRADerivations`](Lean/IPRADerivations/). Declaration names in the
`Foundations` modules have prefix `LeanProofs.IPRA.Foundations`; names in the
`Analysis` modules have prefix `LeanProofs.IPRA.Analysis`. Structural backend
names are identified separately.

## Every theorem environment

The source locations below identify the environment's first line. Unlabelled
environments are identified by their printed title. Historical IDs such as K1
come from the delivered theorem ledger.

| Source claim | Location and label | Current scope and exact declarations | Remaining work |
|---|---|---|---|
| O1. No primitive-recursive universal evaluator | [02_boundary.tex](../docs/proofs/foundations/fiber_ipra_2026-11-16/paper/sections/02_boundary.tex), line 61, unlabelled theorem | **Checked external obstruction and internal diagonal family.** [UniversalEvaluatorObstruction](Lean/IPRADerivations/Foundations/UniversalEvaluatorObstruction.lean) `no_universal_primitive_recursive_evaluator` proves that no binary `E : PR 2` represents every unary PR program under actual `PR.ev` semantics. `diagonal_obstruction` closes the object-level no-index theorem using `EmbeddingBasics.no_universal_evaluator`. [Core/Evaluation](Lean/IPRADerivations/Core/Evaluation.lean) defines the shared evaluator and proves closed computation derivations. | No mathematical remainder for the stated metatheorem. The external semantic assertion is separate from the object-language diagonal sentence; no internal universal evaluator is introduced. |
| K1. Local certificate sealing | [04_kernel.tex](../docs/proofs/foundations/fiber_ipra_2026-11-16/paper/sections/04_kernel.tex), line 11, `thm:sealing` | **Inherited checked structural schema.** `LeanProofs.ConciseIPRA.Prf.exE` has exactly the fresh-witness branch and shifted conclusion required by the source. | No mathematical remainder. The optional delivered alias `FIBER.seal` has not been installed as a new library module. |
| Observational escape | 04_kernel.tex, line 30, unlabelled corollary | **Inherited checked elimination schema.** `Prf.exE` seals any branch whose public conclusion has no fresh certificate variable. The application supplies its actual observation-invariance derivation. | Concrete equivalence bits, observation congruence and stability proofs remain obligations for each interface. There is no generic installed FIBER observation record or observation compiler. |
| K2. Finite residual discharge | 04_kernel.tex, line 45, `thm:cut` | **Inherited checked structural schema.** `LeanProofs.ConciseIPRA.Prf.trans` works for arbitrary formulas and arbitrary contexts, under a derivation of each source hypothesis. | No mathematical remainder. A residual producer is a premise until its own derivation is supplied. |
| K3. Fixed-formula Boolean reflection schema | 04_kernel.tex, line 70, `thm:boolean-reflection` | **Checked for the implemented packed bounded syntax.** [BoundedFormulas](Lean/IPRADerivations/Foundations/BoundedFormulas.lean) provides `BF`, `bitAt`, `fmAt`, `reflect`, `bf_reflect`, `bf_cases`, and `bf_dec`. [BooleanizationCorollaries](Lean/IPRADerivations/Foundations/BooleanizationCorollaries.lean) provides `bit_one_iff`, `bit_zero_iff`, and `imp_iff`. These return object derivations at arbitrary argument terms and contexts. | The source's proposed arity-indexed `BFm n` frontend is not installed. Translation from that syntax or arbitrary original formulas to packed `BF`, with formula-equivalence proofs, must be explicit before crediting a frontend. See the reflection scope below. |
| K4. Canonical bounded selection | 04_kernel.tex, line 134, `thm:least` | **Checked generic conditional object family.** [BoundedSelection](Lean/IPRADerivations/Foundations/BoundedSelection.lean) provides `mu`, `found_bound`, `least`, and closed `canonical_bounded_selection` for any fixed binary PR verifier. The internal query has an explicit universally quantified bit-valued contract. Bounded existence yields an in-range accepted least witness and literal zero at every earlier input. `BoundedFormulas.bf_choice` and `bf_least` also cover reflected predicates. | No mathematical remainder for this source theorem. The verifier bit contract and bounded totality must be proved by a client; they cannot be inferred from intended semantics. |
| K5. Master-certificate theorem | 04_kernel.tex, line 171, `thm:master` | **Checked conditional object family.** [MasterCertificate](Lean/IPRADerivations/Foundations/MasterCertificate.lean) provides the actual PR sequence `master`, its `entry` decoder, `master_decode`, `master_length`, `master_valid`, and closed `master_closed`. Pointwise bounded totality yields every decoded entry's bound and acceptance. | A client must translate its fixed verifier into the implemented predicate and prove pointwise totality. A uniform numerical bound on the entire sequence code and sequence concatenation are further compiler requirements, not premises hidden in `master_valid`. |
| K6. Least finite demand closure | 04_kernel.tex, line 209, `thm:demand-closure` | **Checked conditional object family.** [DemandClosure](Lean/IPRADerivations/Foundations/DemandClosure.lean) provides actual variable-length sequence coordinates, reflected order, coordinate sum, maximum, join, zero vector and PR iteration. `closure_prefixed`, `closure_stable`, `demand_closure`, and closed `demand_closure_closed` prove cappedness, stabilization at the exact sum of caps, prefixedness and minimality. | No mathematical remainder for the source finite-product theorem. The operator's cap preservation and monotonicity are explicit object premises. Compiler integration still needs demand extraction and finite schedule unrolling. |
| K7. Bounded strategy realization | 04_kernel.tex, line 263, `thm:strategy` | **Checked proof-generator family with closed object endpoints.** [StrategyRealization](Lean/IPRADerivations/Foundations/StrategyRealization.lean) provides fixed `Pattern`, actual `check`, `verifierF : PR 2`, `verifier_at`, `check_sound`, `strategy_sound`, `bounded_strategy`, and `bounded_strategy_program`. Bounds may depend on the entire packed move history. Existential responses and universal tables are decoded from the supplied code. | No mathematical remainder for the source's acceptance-implies-formula theorem over the implemented reflected leaves. Translation of other source leaf syntax is the K3 frontend obligation. No completeness or extraction from arbitrary classical proofs is asserted. |
| C1. FIBER compilation | [05_compiler.tex](../docs/proofs/foundations/fiber_ipra_2026-11-16/paper/sections/05_compiler.tex), line 59, `thm:compilation` | **Partial external compiler metatheorem.** [FiberCompiler](Lean/IPRADerivations/Foundations/FiberCompiler.lean) has actual typed acyclic `Program` syntax, `Program.compile`, `compile_at`, `compile_closed`, guarded residual computation, scoped metadata and `GeneratedSymbol.correct`. Primitive nodes require local sequents and recursively constructed premise programs. Pair/projection, QF loop, search, Boolean branch, lexical witness, strategy, observation and specialized call constructors are implemented. | Complete global runtime demand flattening, whole-master metadata/verification, transformation/observation composition and cyclic graph unrolling. Local symbol evaluation correctness does not assert the missing global realizer laws. Witness residual hoisting is explicitly the possibly stronger producer `∀c,φ(c)→R(c)`. |
| C2. Compositionality | 05_compiler.tex, line 131, `thm:composition` | **Partial realizer construction.** `FiberCompiler.Program.callCompiled` specializes a previously compiled interface, retaining its specialized residuals. `Program.bind_residuals` and `booleanCase_residuals` preserve control-flow guards; the literal proof is compiled by recursive substitution/cut. `StagedGraph` and `BoundedCover.composition` remain additional components. | `SequenceComposition` now proves the actual runtime append/flatMap/flatten lengths and lookups. Construct master-input reassociation, bounds/verifier and global output-transformer/observation stability using those proved list operations. The acyclic local proof kernel and static specialized call do not yet supply these realizer fields. |
| Reuse under arbitrary terms and contexts | 05_compiler.tex, line 159, unlabelled corollary | **Inherited checked structural schema.** `LeanProofs.IPRA.inst`, `Prf.subst`, `Prf.weaken`, and `Prf.ofNil` provide the advertised arbitrary-term and arbitrary-context reuse. `StagedGraph.instantiate_into` also supports local hypotheses. | No mathematical remainder for already constructed object derivations. This does not supply a missing compiler or a missing local theorem. |
| R1. Bounded producer elimination | [06_residuals.tex](../docs/proofs/foundations/fiber_ipra_2026-11-16/paper/sections/06_residuals.tex), line 61, unlabelled proposition | **Inherited checked structural schema, with checked bounded-selection components.** `Prf.trans` discharges a proved producer; `Prf.exE` seals a witness-independent branch. `bf_choice` and `least_spec` supply explicit terms for reflected bounded producers. | Every producer's existence proof and every source-verifier adapter remain inputs. No theorem here eliminates an unproved producer merely because it is bounded. |
| A1. Dyadic adjacent-motion theorem | [07_analysis.tex](../docs/proofs/foundations/fiber_ipra_2026-11-16/paper/sections/07_analysis.tex), line 22, `thm:dyadic` | **Checked conditional object family.** [DyadicCauchy](Lean/IPRADerivations/Analysis/DyadicCauchy.lean) provides `discrepancy`, `discrepancy_between`, closed `dyadic_cauchy`, and closed `dyadic_endpoints`. The exact sharp integer bound has arbitrary internal indices and a runtime parameter. | No mathematical remainder for the source's cleared-denominator endpoint. Interpreting a represented real or exporting a particular interface's observation requires that client's evaluator/observation adapter. |
| Independent certificates become coherent | 07_analysis.tex, line 61, unlabelled corollary | **Checked conditional object family.** `DyadicCauchy.motion_of_certificates`, `certified_discrepancy`, `certified_between`, `certificates_coherent`, and `certificates_coherent_endpoints` use an arbitrary object predicate `C(k,w,x)`, pointwise existential coverage, and adjacent-pair soundness. | No mathematical remainder for fixed public PR observation symbols. A client whose observations depend on the local code must first establish the stated invariant public observation or a bounded canonical selector. No global choice premise is introduced. |
| A3. Finite-net lifting | 07_analysis.tex, line 113, `thm:net` | **Checked conditional object family.** [FiniteNet](Lean/IPRADerivations/Foundations/FiniteNet.lean) provides `lift_at`, `finite_net`, and universally closed `finite_net_closed`, with arbitrary finite parameter families, domain formulas, proximity relations, and image/net terms. | The finite net, membership, coverage, modulus, stability, and pointwise validity are explicit source premises. Constructing them for a particular metric space is a separate application proof. |
| O2. No unguarded finite-use exact sign selector | [08_algebra.tex](../docs/proofs/foundations/fiber_ipra_2026-11-16/paper/sections/08_algebra.tex), line 12, `thm:no-sign` | **Open external representation obstruction.** The source gives a finite-query adversary argument. [GapDecision](Lean/IPRADerivations/Foundations/GapDecision.lean) `gap_zero`, `gap_far`, and `gap_decide` prove guarded integer-distance decisions, rather than this impossibility result. | Define rapidly convergent rational names and deterministic finite-query transcripts, prove indistinguishability under a perturbation beyond the finite queried set, then formalize the contradiction. A guarded decision theorem does not prove the unguarded obstruction. |
| G1. Stable cluster transport | 08_algebra.tex, line 55, unlabelled theorem | **Open; the quantitative statement needs a precise interface.** No checked finite incidence/multiplicity common-coarsening theorem is identified. The small matrix identities in `Algebra.ObservationAlgebra` concern different observations. | Encode boxes, multiplicities, coverage/count soundness, inflation and common coarsening; prove component multiplicity conservation. Specify the matching metric and prove the claimed observation modulus. Short edges do not alone bound an entire connected component's diameter by `2ε`. |
| G2. Gap-guarded labeling | 08_algebra.tex, line 82, unlabelled proposition | **Requires source clarification/correction for complex boxes.** A metric separation gap alone does not make lexicographic ordering of arbitrary valid complex boxes stable. No checked labeling theorem is identified. | Restrict to real roots with order-separated intervals, supply a coordinate-order separation guard, or specify a stable locator/reference labeling. Prove certificate-independent matching under that precise guard. See the counterexample below. |
| G3. Finite-algebra observation | 08_algebra.tex, line 120, unlabelled theorem | **Partial.** [Core/LinearAlgebra](Lean/IPRADerivations/Core/LinearAlgebra.lean) supplies externally fixed-dimension signed matrices. [ObservationAlgebra](Lean/IPRADerivations/Algebra/ObservationAlgebra.lean) provides `newton2`, `newton3a`, `newton3b`, `companion2`, `companion3`, `quad_observation`, and `quad_observation_sq`. | Encode and check arbitrary finite spanning/ideal-membership certificates, prove closure under polynomial action, and prove transport under supplied substitutions/quotient maps. The existing degree-two/three identities do not prove arbitrary finite-presentation correctness, root-cluster independence, or basis independence. |

## Exact object-theory scopes

### Reflection and least search

`BoundedFormulas.BF` is external syntax with equality, conjunction, disjunction,
negation, bounded universal quantification and bounded existential
quantification. Every bound and equality term is fixed before the proof is
generated. A bounded binder extends the packed parameter from `y` to
`pairT i y`. `fmAt_subst` and `bitAt_subst` establish substitution through
these binders. Order atoms are expressible as equalities because
`le a b` is `monus a b = 0` and `lt a b` is `le (succ a) b` in
[`Core/Order`](Lean/IPRADerivations/Core/Order.lean). The derived implication
constructor and its `imp_iff` proof use the checked decidability of the
antecedent.

For every fixed `A : BF`, `reflect A y` returns three object derivations in
any context. They prove `A(y) → bit(A,y)=1`, its converse, and that the bit is
zero or one. `BooleanizationCorollaries.bit_one_iff` has the orientation in
the source statement. These open endpoints can be universally closed with
`closeUniv`. The schema does not quantify internally over arbitrary formula
codes. A parser or translation from the proposed `BFm n` datatype must prove
that its packed interpretation is the original input formula.

[`BoundedReflection`](Lean/IPRADerivations/Foundations/BoundedReflection.lean)
uses the actual conjunction fold `allB` and existential fold `exB`.
`all_elim`, `all_intro`, `ex_elim`, and `ex_intro` are arbitrary-term indexing
and reflection lemmas. For arbitrary numerical bodies their acceptance
criterion is nonzero, expressed as `¬(body=0)`. For generated reflected bits,
`bf_cases` converts this to `body=1`. This convention matters when adapting
an external verifier.

`bfWit` is a PR least witness term, with the bound returned when there is no
accepted witness. `bf_choice` needs an actual bounded existential proof.
`bf_least` rejects earlier witnesses even without an existence premise.
`least_spec` packages the successful bounded-predicate case. The lower-level
`first_found` and `first_before` each require the corresponding object proof
that the original verifier value is zero or one. The bit premise cannot be
discarded for an arbitrary PR numerical function. The complete wrapper
`BoundedSelection.canonical_bounded_selection` now retains that contract as
an object-language antecedent and quantifies both the query and exclusive
bound internally. Its `mu` is the actual complement least search.

### Master certificates and strategies

`MasterCertificate.sequence values N x` is an actual PR sequence code with
declared length `N`. It builds a stack by recursion and reverses the in-range
lookup index through `entry`. `sequence_decode` is proved by object QF
induction at an arbitrary internal index `i<N`. `master` instantiates this
construction with the least accepted witness for query `pairT i x`.

For fixed `b : PTm 1` and `A : BF`, `master_closed` has literal type

```lean
([] : List (Fm PTm 0)) ⊢[PRAAx]
  univ 2 (MasterCertificate.masterFormula b A)
```

The two internal variables are family length `N` and parameter `x`. The
antecedent is `∀i<N ∃c<b(i,x) A(c,i,x)` and the consequent asserts validity of
each actual decoded master entry. It does not assume a previously correct
master code. It also does not yet give the compiler a numerical upper bound
for that entire sequence code, or arbitrary list concatenation equations.

`StrategyRealization.Pattern` is external fixed syntax with reflected leaves
and dependent bounded existential/universal nodes. An existential certificate
is a pair containing its response and the continuation. A universal
certificate is a length-checked table decoded with `MasterCertificate.entry`.
The checker tests every bounded universal move and recursively verifies the
appropriate continuation. It is not a checker defined as the truth value of
the desired quantified conclusion. `verifierF P : PR 2` is an explicit
generated PR symbol, with object evaluation equality `verifier_at`.

`bounded_strategy_program P` is the closed two-variable object sentence

```text
∀ code history,
  verifierF(P)(code,history)=1 → fmAt(formula(P),history).
```

The pattern is an external schema parameter. The code and move history are
internal universally quantified naturals. No strategy-existence premise, table
selector axiom, or universal evaluator for all PR programs occurs.

### Finite demand closure

`DemandClosure.iterate F k r x` starts from the actual length-`r` zero
sequence and applies the actual coordinatewise join with `F` at every stage.
Dimension `r`, cap sequence `caps`, data parameter `x`, iteration counters,
and candidate prefixed vectors are internal naturals. `rank r caps` is the
actual finite sum of decoded caps. The cap-preservation formula `mapsInto`
and the monotonicity formula `monotoneOn` quantify over encoded vectors with
coordinate order, restricted to the capped product. They imply that the
operator respects coordinate-equivalent representatives.

`demand_closure_closed F` universally closes `r,caps,x` in

```text
mapsInto(F,r,caps,x) → monotoneOn(F,r,caps,x) →
  [d(K)≤caps ∧ coordinatesEQ(d(K),d(K+1)) ∧ F(d(K))≤d(K)
   ∧ ∀e (e≤caps → F(e)≤e → d(K)≤e)],
where K=rank(r,caps).
```

Equality is finite-product equality at every coordinate below `r`, expressed
by the actual bounded universal formula `coordinatesEQ`. Equality of unrelated
sequence codes is not needed. `rank_step_or_prefixed`, `prefixed_later`, and
`nonprefixed_growth` derive the potential-growth contradiction rather than
assuming a rank-growth or settlement contract. The induction predicates are
QF reflected order/rank formulas. Empty dimension and zero caps are included.
This covers all three conclusions of `thm:demand-closure`.

### Dyadic and summable coherence

For fixed `p q : PR 2`, the signed numerator is the difference of the natural
terms `p(k,x)` and `q(k,x)`. The runtime parameter `x` remains internal in both
closed three-variable dyadic endpoints. `dyadic_cauchy` uses indices `N,r,x`;
`dyadic_endpoints` uses `N,M,x` and the guard `N≤M`. Their common sharp
conclusion is

```text
1 + |2^(M−N) a(N,x) − a(M,x)| ≤ 2^(M−N).
```

This is the source's exact integer bound, including equality of endpoints.
The induction is on the offset with a QF inequality. Adjacent motion remains
an outside quantified hypothesis that is instantiated in the step. The
zero-offset case and negative signed numerators are included. The rational
strict Cauchy inequality is an interpretation after clearing positive powers
of two, as explicitly allowed by the source.

The certificate corollary takes arbitrary `C : Fm PTm 3` with coordinates
`k,w,x`. Its two object premises are `∀k ∃w C(k,w,x)` and
`∀k,w (C(k,w,x) → |2a(k,x)−a(k+1,x)|≤1)`. `motion_of_certificates` opens and
seals each witness using `Prf.exE`. The public conclusion contains only the
fixed observation symbols. Both `certificates_coherent` and
`certificates_coherent_endpoints` are universally closed in three internal
variables. There is no requirement to produce one infinite witness array.

The additional A2 claim in [07_analysis.tex §7.2](../docs/proofs/foundations/fiber_ipra_2026-11-16/paper/sections/07_analysis.tex)
has no theorem environment. It is **checked for signed rational sequences with
independently varying positive sample and error denominators** in
[RationalSummableTails](Lean/IPRADerivations/Analysis/RationalSummableTails.lean).
For fixed PR symbols, a sample is `(p(k,x)−q(k,x))/d(k,x)` and its adjacent
error is `e(k,x)/f(k,x)`. The actual PR accumulator starts at `(E,D)=(0,1)`
and adds the next error by `(E,D) ↦ (E*f+e*D,D*f)`.

`accumulator_succ` gives these exact rational-addition equations;
`sumDen_positive` proves positivity from the error-denominator contract.
`cross_triangle` and `rational_step` prove the cleared triangle step and
cancel the positive intermediate sample denominator. QF induction then proves
`finite_telescoping` at internal `N,r,x`. No common-scale conversion or
pairwise Cauchy estimate is assumed.

`summable_tail_endpoints` closes internal `N,M,x` and retains sample/error
denominator positivity, adjacent error bounds, the actual rational finite-sum
tail certificate and `N≤M`. Its conclusion has positive tail denominator and

```text
Tden(N,x) * |a(M,x)*d(N,x) − a(N,x)*d(M,x)|
  ≤ Tnum(N,x) * d(N,x)*d(M,x).
```

Thus the finite error sum can be compared to an independently supplied rational
tail bound. A specified rate at which that bound tends to zero remains input
when the application requests a global Cauchy rate. The original
[SummableTails](Lean/IPRADerivations/Analysis/SummableTails.lean) is the simpler
signed-integer/common-unit specialization, with its own direct finite sums.

### Finite-net lifting

`FiniteNet` has arbitrary formulas for the domain, the finite-point property,
the relaxed property, input proximity and output proximity. The finite family
of parameters has external arity `k`, and every parameter is instantiated by
an arbitrary object term. `finite_net_closed` universally closes the ambient
`n` variables, retaining these five premises in order.

1. The input point belongs to the encoded domain.
2. A bounded net point covers that input.
3. The supplied function obeys the required local modulus.
4. The property transfers along the output-proximity relation.
5. Every in-range net point belongs to the domain and satisfies the property.

`lift_at` opens the covering index with local existential elimination. Its
result has no such index. This establishes the source's conditional lifting
theorem without constructing nets for arbitrary compact spaces. Concrete
discrepancy functions and numerical margins instantiate the supplied proximity
formulas and require their own correctness proofs.

## Definitions, compiler invariants and application obligations

The definitions in [03_interfaces.tex](../docs/proofs/foundations/fiber_ipra_2026-11-16/paper/sections/03_interfaces.tex)
carry mathematical proof obligations. A structure containing a `sound` field
does not provide any instance of that field. The delivered
[`lean/FIBER/Blueprint.lean`](../docs/proofs/foundations/fiber_ipra_2026-11-16/lean/FIBER/Blueprint.lean)
is explicitly a blueprint; its `Program` constructors do not carry all the
source theorem's local contracts.

| Obligation and source | Available checked material | Concrete remaining deliverable |
|---|---|---|
| Interface, validity and totality, §3.2 | PR terms and ordinary formulas can express query validity, exclusive bounds, verifier equality and bounded totality. | Install consistent formula constructors with substitution equations; prove concrete query/verifier soundness contracts. Totality stays a theorem, hypothesis or exact producer residual. |
| Certificate-independent observation and metric/quotient fibers, §§3.2, 3.6 | `Prf.exE` enforces the lexical witness condition; `GapDecision` supplies signed absolute-value lemmas; fixed algebraic observations are available. | Supply each actual equivalence bit's reflexivity, symmetry and transitivity, exported-operation congruence, and numerical stability proofs. These are not implied by metadata names. |
| Realizer fields and escape classes, §§3.3–3.4 | Least bounded search and master construction cover canonical bounded witnesses; local elimination covers sealed witnesses. | Define demand, master bound/verifier, transform, observe and residual constructors together with their literal local soundness sequents. Prove that every exported code is canonical or observationally independent. |
| Herbrand capsules, §3.5 | `exB`, `bf_choice`, bounded reflection and pairing provide components. The reference implementation has a capsule algorithm. | Encode the actual list and prove the disjunction's meaning through lookup; prove pointwise mapping and invariant elimination, and the least-valid-member adapter when selection is requested. No dedicated generic capsule endpoint is identified. |
| Node arities, scopes and QF loop invariants, §5.1–§5.2 and Appendix A | `StagedGraph` handles proof-bearing local nodes; `TraceInvariant.trace_invariant_all` and `trace_invariant` preserve a supplied PR bit invariant through an actual PR run. | `FiberCompiler.Program` now enforces arities and lexical witness scope by its indices and compiles supplied checked QF loops. Complete a runtime graph frontend and global demand/unrolling adapter, and prove their interpretation into that typed syntax. |
| Compiler output tuple, §5.3 and Appendix A | The checked typed acyclic `FiberCompiler` returns literal residual/input sequents and local generated symbols with evaluation equalities; the arithmetic families supply its primitive contracts. | Return all seven prescribed components `(demand,bound,verifier,transform,observe,residuals,proof)` from an accepted typed source program; cover all node constructors, calls, loops and cyclic unrolling. |
| Residual normal form and hierarchy R0–R8, §6 | Structural rules cover R0; bounded reflection/search, master certificates, demand closure, coherence and finite-net lifting cover displayed conditional R1–R6 instances within their documented representation scope. | Supply precise R7 guarded operations and rational adapters for the full R4 scope. Preserve every unresolved R8 producer as an object formula with all parameters, strictness and zero cases. No generic theorem supplies absent height, modulus, gap or representative data. |
| Metastability, §7.3 | Fixed bounded windows can use reflected formulas and strategies once a control program is fixed. | Construct the concrete window verifier and its witness bound. Keep `g` as a supplied fixed PR program unless a separate coded bounded semantics is proved. A global Cauchy rate needs a tail/rate producer. |
| Guarded partial operations, §7.5 | `GapDecision.gap_decide` distinguishes zero from a separated magnitude under its exact signed approximation contract. | For reciprocal/division, supply exact rational interval arithmetic, a positive apartness margin, a precision transformer and verified output error. Logarithms, square roots, pivots and normalized vectors require their own domain guards and stability estimates. |
| Modulus calculus, §7.6 | Signed ring/order arithmetic and finite sum APIs are available. | Prove the actual numerical contracts for addition; multiplication on bounded boxes; composition; `L`-term sums with the length allowance; division under apartness; root labels under an adequate labeling guard; and mesh/quadrature total error. A qualitative continuity premise is insufficient. |
| A4. Certified bisection and uniqueness, §7.7 | `Core.Integers` and the exact polynomial identities in `Foundations.QuantitativeIdentities` support finite algebra; cancellation is available in the arithmetic library. The archive has executable bisection tests. | Encode the entire rational trace, prove midpoint selection preserves signs, prove exact width halving, and derive uniqueness from a checked factor identity `p(y)−p(x)=(y−x)Q(x,y)` with a positive lower bound for `Q`. No full polynomial interval checker or bisection endpoint is identified. |
| Branch/Puiseux and representative interfaces, §§8.5–8.6 | Fixed quadratic observation identities provide a small finite example; finite strategies provide compatibility consumers. | For exact splitting data, prove truncation identities and permutation-invariant validity. For approximate data, prove cluster/residual bounds. Preserve discriminant/order guards for labels and representative-totality/continuation as separate producers. |

The wider domain discussion in [09_domains.tex](../docs/proofs/foundations/fiber_ipra_2026-11-16/paper/sections/09_domains.tex)
and the [difficulty matrix](../docs/proofs/foundations/fiber_ipra_2026-11-16/paper/sections/C_difficulty_matrix.tex)
state application requirements. They do not introduce further numbered
theorems. Their proof work remains explicit as follows.

| Application family | Required finite mathematical endpoint and producer boundary |
|---|---|
| Combinatorics and finite algebra, §9.1 | Fixed PR definitions, arbitrary-term recursion equations, QF invariant, arithmetic proof and universal closure. A coloring, tiling or large coefficient checker still needs its own object reflection theorem. Existing unrelated finite identities do not discharge it. |
| Real/complex and special-function analysis, §9.2 | Exact coefficient identities first; convergence from an actual majorant/tail; continuation from a finite overlap path and compatibility proof; asymptotics from effective constants. `DyadicCauchy`, `SummableTails`, `NestedRegions` and `StrongMinimizer` supply specific coherence consumers with displayed contracts, rather than the represented function evaluators or all listed special functions. |
| Probability, §9.3 | Encode finite rational laws, normalization, moments/convolution and threshold sums. General-law applications also need quantization, tail-moment and boundary-mass/anti-concentration producers and a verified total error budget. |
| Topology/geometry and observational gluing, §9.4 | Encode complexes/covers/refinement maps and the relevant crossing or winding checker. Prove transport along an actual spanning tree and check cycle compatibility, with summed metric errors. Produce the approximation and separation moduli rather than assuming a completed-space construction. |
| Diophantine/arithmetic geometry, §9.5 | A bounded enumerator with soundness and completeness below the supplied height, plus a complete-height/list producer. Rational representatives require a separate totality and compatible-continuation theorem. Bounded search does not turn abstract finiteness into such a producer. |
| Prime distribution, §9.6 | An explicit estimate with constants, threshold, parameter ranges and exact arithmetic error checker. Effective production of the constants remains a separate theorem. |
| Computability/proof coding, §9.7 | Exact source/target theories, formulas and pinned program data; ordinary derivations for each direction; a checked bridge at the application boundary. Semantic equivalence or executable replay alone does not establish internal derivability. |
| Classical arguments, §9.8 | Bounded decidable cases and fixed strategies are checked families. Stable negative targets need the actual negative-translation and stability derivations. Unbounded positive existence requires a producer. |

## Appendix B target-by-target crosswalk

This table preserves every provisional target name from
[B_signatures.tex](../docs/proofs/foundations/fiber_ipra_2026-11-16/paper/sections/B_signatures.tex).
Names are mapped by theorem scope rather than namespace resemblance.

| Source target | Checked declaration or exact outstanding obligation |
|---|---|
| `Kernel.discharge` | `ConciseIPRA.Prf.trans`, inherited checked schema. |
| `Kernel.specialize` | `LeanProofs.IPRA.inst`, inherited checked schema. |
| `Kernel.seal` | `ConciseIPRA.Prf.exE`, inherited checked rule. |
| `Bool.bit_cases` | `BoundedReflection.eqb_cases`, `sg_cases`, `all_cases`, `ex_cases`; `BoundedFormulas.bf_cases` for the generated formula bit. |
| `Fold.any_sound` | `BoundedReflection.ex_elim`; reflected leaf acceptance is recovered with `bf_cases` and `reflect`. |
| `Fold.any_complete` | `BoundedReflection.ex_intro`; it accepts a nonzero body, with bit conversion supplied for reflected leaves. |
| `Fold.all_sound` | `BoundedReflection.all_elim`, `all_reflect`; the raw body condition is nonzero. |
| `Fold.all_complete` | `BoundedReflection.all_intro`, under the actual bounded universal nonzero premise. |
| `BFm.reflect` | `BoundedFormulas.reflect` and `BooleanizationCorollaries.bit_one_iff` for packed `BF`. Translation of the proposed arity-indexed syntax remains explicit work. |
| `Search.leastAccepted_found` | `BoundedSelection.least`, closed `canonical_bounded_selection`, for arbitrary binary verifier symbols under the explicit bit contract; `bf_choice`/`least_spec` for reflected predicates. |
| `Search.leastAccepted_minimal` | The earlier-zero conjunct of `BoundedSelection.least` and `canonical_bounded_selection`; `bf_least` for reflected predicates. |
| `Sequence.lookup_append` | `MasterCertificate.stack_succ`, `drop_push`, `sequence_decode`, `sequence_length` establish lookup for the actual constructor. `SequenceComposition.sequence_append`, `sequence_append_associative`, `runtime_flatMap_lookup` and `runtime_flatten` now provide actual arbitrary-code append/flatten equations, including empty cases. Append associativity is extensional. |
| `Master.valid` | `MasterCertificate.master_valid`, closed `master_closed`. |
| `Demand.iter_mono` | `DemandClosure.iterate_increasing`, actual PR orbit at arbitrary internal stage and dimension. |
| `Demand.potential_strict` | `DemandClosure.rank_strict`, `join_rank_strict`, `rank_flat`, `join_rank_flat`, `rank_step_or_prefixed`, and `nonprefixed_growth`, derived from actual coordinate sums and the actual orbit. |
| `Demand.stabilizes` | `DemandClosure.closure_stable`, included in `demand_closure` and `demand_closure_closed`, at exactly the actual sum of caps. |
| `Demand.least` | `DemandClosure.iterate_le_prefixed_at`, `closure_prefixed`, and the universally quantified leastness conjunct of `demand_closure`. |
| `Strategy.realize` | `StrategyRealization.check_sound`, `strategy_sound`, closed `bounded_strategy_program`. |
| `Interface.localSound` | Concrete compiled interface instances are pending. `StagedGraph.Node.d` stores a supplied local proof without proving new local mathematics. |
| `Interface.obsIndependent` | Pending for concrete general FIBER interfaces. The dyadic certificate theorem covers its specific public observation contract. |
| `Compile.sound` | Typed acyclic source compilation is checked by `FiberCompiler.Program.compile`, `compile_at`, and `compile_closed`; static scheduling is also checked by `StagedGraph`. Full global runtime realizer fields and cyclic unrolling remain pending. |
| `Compile.compose` | `FiberCompiler.Program.callCompiled` and guarded bind/case residual equations prove static specialized calls and local proof composition. `SequenceComposition` supplies the actual runtime demand-list flattening and lookup arithmetic. Global master/transformer/observation assembly remains pending. |
| `Dyadic.scaledBound` | `DyadicCauchy.discrepancy`, `discrepancy_between`; universally closed `dyadic_cauchy`, `dyadic_endpoints`. |
| `Dyadic.cauchy` | The same exact bound implies the source's permitted cleared-denominator strict inequality. No completed-real semantics is imported. |
| `FiniteNet.lift` | `FiniteNet.lift_at`, `finite_net`, `finite_net_closed`. |
| `Clusters.commonCoarsening` | Pending actual incidence/count checker and object common-coarsening proof with a precise quantitative observation relation. |
| `Clusters.labelUnderGap` | Pending corrected order/locator guard and matching proof. Metric separation alone is insufficient for complex lexicographic labels. |
| `Bridge.fiberOpen` | The generic backend has `IPRABridge.conciseToStandardSequent`, `standardToConciseSequent`, `conciseSequent_iff`, and `scopedStandardSequent_iff`. A FIBER-specific instantiated open-sequent round trip is not identified. |

The bridge declarations above are in
[`Bridge/Lean/IPRABridge/OpenSequents.lean`](../Bridge/Lean/IPRABridge/OpenSequents.lean)
and [`ScopedSequents.lean`](../Bridge/Lean/IPRABridge/ScopedSequents.lean).
Their exact namespaces and environment/label premises must be retained when a
client constructs the application endpoint.

## Formalization-plan and regression obligations

The complete [FORMALIZATION_PLAN.md](../docs/proofs/foundations/fiber_ipra_2026-11-16/lean/FORMALIZATION_PLAN.md)
and [Section 10](../docs/proofs/foundations/fiber_ipra_2026-11-16/paper/sections/10_lean.tex)
are accounted for below. Organizational proposals such as introducing
`FIBER/Bool.lean` are satisfied mathematically only by the matching declarations,
irrespective of their installed directory.

| Phase | Scope checked and outstanding acceptance work |
|---|---|
| 0. Structural kernel | The exact inherited rules and `inst` are checked. The archived `FIBER/Kernel.lean` is an alias candidate, not an installed integration module. Dedicated alias compilation and the requested nonempty-context/nontrivial-substitution examples remain an optional integration task. |
| 1. Boolean atoms and folds | Checked atoms, actual `allB`/`exB`, arbitrary-term extension/indexing and both reflection directions are present in `BoundedReflection`. Its induction predicates are QF state equations; universally quantified source contracts remain hypotheses outside those predicates. |
| 2. Fixed formula reflection | Checked external recursion over packed `BF`, nested binders, substitutions, decidability and reflection. The proposed general `BFm n` frontend and named nested-quantifier regression instances remain to be connected explicitly. |
| 3. Least accepted code and sequence coding | Checked complete generic one-success selection under an explicit bit contract, least reflected witnesses, actual sequence constructor and in-range decoder. Actual append/flatten length and lookup are now checked in `SequenceComposition`; whole-code bounds and full realizer assembly remain work for the compiler. |
| 4. Master certificates | The variable-length bounded-family theorem is checked directly, including its actual PR code and closed endpoint. The prescribed three-query polynomial-evaluation regression and numerical whole-code bound are separate follow-up tests/contracts. |
| 5. Demand closure | The full variable-length order/rank/join/orbit theorem is checked, including cap preservation, sharp stabilization, prefixedness and minimality. The source's suggested fixed-coordinate milestones are subsumed mathematically. A concrete two-coordinate regression should instantiate this actual theorem rather than report a host settlement calculation. |
| 6. Bounded strategies | General fixed patterns, dependent bounds, actual checked response/table trees, explicit PR verifier and closed soundness theorem are checked. The concrete depth-two regression is still a named-instance obligation. |
| 7. Interface/compiler records | Typed acyclic syntax, recursive proof generation, local metadata symbols, guarded residuals and lexical scope are checked in `FiberCompiler`. Complete global runtime demand/master/observation composition and cyclic unrolling; actual realizer instances still need their mathematical local contracts. |
| 8. Cross-domain examples | Exact runtime-parameter dyadic coherence, including sealed local certificates, and conditional finite-net lifting are checked families. Genuine cluster-certificate agreement and corrected gap labels remain. Concrete rational-net, cluster and polynomial-evaluation regression instances must instantiate actual representation checkers. |
| 9. Build, axioms and bridges | [Checks/Axioms.lean](Lean/IPRADerivations/Checks/Axioms.lean) registers the new dyadic, certificate, integer/rational tail, finite-net, master, demand, strategy, compiler-kernel and evaluator-obstruction endpoints. Direct and normal integration builds and standard-axiom audits are recorded in the progress report. `ConciseIPRA.pra_iff_native` and the generic open bridges exist; a concrete FIBER native transfer and open-sequent round trip should be recorded when performed. No such packet-specific receipt is inferred from the generic bridge theorem. |

`pra_iff_native` is defined in
[`ConciseIPRA/NativeBiInterpretation.lean`](../ConciseIPRA/Lean/ConciseIPRA/NativeBiInterpretation.lean).
The standard Lean metatheoretic axioms recorded for the audited new endpoints
are `propext`, `Classical.choice` and `Quot.sound`. Their appearance does not
add any object axiom to `PRAAx`. Build acceptance must continue to exclude
`sorryAx`, unproved theorem-specific axioms and quantified induction stronger
than the stated object theory.

The latest root integration, based on `32099fe883` with runtime sequence
composition, passed 2,089 build jobs and 2,055 axiom reports for 1,977
distinct declarations. Every report uses only the standard Lean axioms.
The portable and independent Diophantine import gates passed across 3,508
and 5,252 modules respectively. The full demand endpoints first landed in
`b1bd8ac2e4`; its reviewed source hash is
`b6d91cfab1bfa8e78d5aedad3b633efceeae59eafb8c8f448bf567692777fade`.
These receipts cover the implemented theorem scopes. Global realizer and
compiler assembly, representation adapters and application obligations above
remain open.

Appendix B requests eight concrete regression examples. Generic coverage and
an instantiated regression receipt are kept separate.

| Requested example | Current support and next check |
|---|---|
| Least even number in a bounded interval | Reflection, order and least search are available. State the precise empty-interval convention and compile the actual parity/interval instance. |
| Two local divisibility witnesses giving a gcd observation | Structural sealing and ordinary gcd/divisibility APIs are available. Build the actual two-certificate formula and prove its gcd observation invariant. No dedicated FIBER regression is identified. |
| Two-coordinate cyclic demand closure | The general arbitrary-dimension object theorem is checked. Add a concrete two-coordinate instance with actual demand terms and proofs of cap preservation and monotonicity. The archive's example remains executable evidence. |
| Depth-two `∀∃` strategy | The general verifier/soundness theorem is checked. Supply an actual strategy code, prove its table equations and acceptance, and instantiate `bounded_strategy_program`. The JSON example alone is executable evidence. |
| Three independent polynomial evaluations in one master code | `master_closed` covers arbitrary internal length. Instantiate the three actual polynomial evaluators and prove their input totality and lookup equations. |
| Dyadic estimate from independent adjacent certificates | The arbitrary-predicate closed family `certificates_coherent_endpoints` is checked, with local `exE`. A domain-specific certificate evaluator is additional application work. |
| Rational finite-net inequality | `finite_net_closed` supplies the full conditional consumer. Instantiate rational proximity, actual net, coverage and a numerical stability theorem to obtain the requested concrete example. |
| One open bridge round trip | Generic checked bridge and bridge regression modules exist. Add and record a FIBER endpoint instance with the actual residual context and free-variable environment. |

The delivered [reference code](../docs/proofs/foundations/fiber_ipra_2026-11-16/reference/fiber_reference.py),
[tests](../docs/proofs/foundations/fiber_ipra_2026-11-16/reference/test_fiber_reference.py),
and [JSON examples](../docs/proofs/foundations/fiber_ipra_2026-11-16/examples/)
are useful finite evidence for mixed-radix coding, search, master bundling,
demand closure, strategy trees, dyadic bounds, finite nets, bisection, capsules
and rejected witness escape. Their host execution provides no additional
`Prf PRAAx` endpoint.

## Source issues to settle before cluster formalization

For G2, consider `P(z)=z²+1`, with roots `i` and `−i`. Fix arbitrarily small
positive rational `h`. Valid boxes centered at `(h,1)` and `(−h,−1)`, each
with coordinate half-width `2h`, contain the two roots and put the lower box
first under lexicographic order of centers or lower corners. Changing the
centers to `(−h,1)` and `(h,−1)` gives equally accurate valid singleton boxes
and reverses this order. The boxes remain disjoint with a fixed positive
metric separation when `h` is small, and their diameters can be made smaller
than any prescribed fraction of that gap. Thus even arbitrarily fine
precision plus a metric gap does not fix the lexicographic order for complex
roots with equal real parts. A real-root restriction or an explicit
coordinate-order/locator guard resolves the missing hypothesis. This audit
does not alter the delivered proposition.

For G1, the source's finite incidence argument suggests a genuine
multiplicity-conservation theorem. Its quantitative observation conclusion
needs a separately specified distance on cluster families and a proof for the
chosen inflation/coarsening construction. A path of overlapping inflated
boxes can have many vertices, so a bound for one edge does not provide the
same bound for the whole merged component. A satisfactory next result should
state the finite count equations and precise matching metric, prove common
coarsening, and derive a justified observation modulus. Stating matching or
pairwise observation agreement as an input would leave the theorem's main
work unproved.

For G3, a spanning certificate need not be a basis. Its matrices are supplied
lifts of multiplication on the generated module. Intrinsic trace,
determinant or characteristic-polynomial claims require care about relations
among spanning vectors and any change of presentation. The delivered theorem
only credits supplied multiplication matrices and explicitly transported
identities unless a further freeness/independence certificate is supplied.
Future endpoints should preserve that distinction rather than asserting
presentation-independent invariants from spanning alone.

## Next mathematical deliverables

1. Use the checked sequence append/flatten API to finish master-code bounds
   and realizer composition; connect the arity-indexed source syntax to the
   checked packed reflection generator.
2. Complete the global compiler/realizer result above the checked typed
   acyclic kernel, with flattened demands and exact specialized residuals. Use the checked demand closure to generate and verify
   the finite unrolling of cyclic demand graphs.
3. Rational denominator-changing telescoping is checked. Add guarded interval
   arithmetic and use it for a complete rational polynomial bisection trace
   theorem and the factor-bound uniqueness conclusion.
4. Settle the precise G1 metric and the G2 labeling guard, then implement real
   cluster-count certificates and prove common-coarsening/label stability.
5. Generalize the finite-algebra example to checked finite presentations and
   prove polynomial-action and transport correctness with all relation or
   independence assumptions displayed.
6. Formalize the remaining unguarded-sign obstruction at its actual
   metatheoretic representation type and record the requested concrete
   native/open-bridge and regression instances.

These remaining tasks are independent mathematical and compiler obligations.
The currently checked master, demand-closure, strategy, dyadic, summable-tail
and finite-net families provide reusable ordinary object-theory components
for them.
