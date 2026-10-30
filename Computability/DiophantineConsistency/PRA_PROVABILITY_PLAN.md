# PRA proof-existence target

The active objective requires a Lean proof that the equivalence between each
selected small equation's unsolvability and `Con(ZFC)` is provable in
primitive recursive arithmetic (PRA). The earlier request for an HA derivation
also remains relevant. Existence of an object-theory proof is enough; a
printed proof is not required.

## Current scope and open endpoints

A [post-merge finite-list theorem](reviews/pra-after-fixed-merge-refresh-author-replay/README.md)
now eliminates any finite list of closed coded induction instances whose
`Code 2` predicate bodies ignore the induction parameter. Its 31-module
source-current chain has passed two independent replays. General
parameter-dependent instances and arbitrary external parameters remain open.

A [conditional positive first-carrier theorem](reviews/adaptive-construction-first-positive2011-independent.md)
now supplies the carrier identity from the first norm and explicit size bounds.
The key remaining input is a stronger actual-Assembly transport-quotient bound;
the 13-variable zero is not yet constructed. The [seed-size theorem](reviews/adaptive-construction-seed-size2011-independent.md)
derives one of its size bounds from explicit first-Pell seed hypotheses.

The [first-Pell correction quotient](reviews/adaptive-construction-correction2011-independent.md)
is now derived in every stated IΣ₁ model from explicit seed-index and ordinate
hypotheses and the constructed scaling. A [positive-correction theorem](reviews/adaptive-construction-correction-positive2011-independent.md)
now also derives the required positive correction under explicit index,
scaling and positivity hypotheses. Establishing those hypotheses in the full
construction remains open. A further [actual-seed client](reviews/adaptive-construction-correction-seed2011-independent.md)
derives the index and ordinate hypotheses from the outer seed and rank phase,
while retaining the Assembly multiplier and positivity assumptions.

The [enriched-assembly adapter](reviews/adaptive-assembly-bridge2011-independent.md)
now derives transport, a strong-factor identity and a positive auxiliary
coordinate from the exact 14-coordinate assembly conclusion with explicit
phase and ordinate premises, preserving its bound. Constructing that assembly
conclusion and the final 13-coordinate zero remain open.

The merge pushed as `d53db22f9a` changed `HerbrandFixedGoalExtraction`,
`HerbrandFixedGoalExtractionBound`, `HerbrandFixedGoalWeakening`, and
`HerbrandStageSupport`. Previously recorded dependent replay results cover
the preceding source snapshot; a source-current rebuild of their downstream
PRA and finite-dispatcher clients is in progress. The merge also changed ZFC
interpretation and proof-context sources, so the maintained HA endpoint still
requires its separately scoped source-current replay.

Two closed coded Σ₁ induction instances can now be eliminated together for
[predicate bodies that ignore the induction parameter](reviews/pra-two-parameter-free-author-replay/README.md).
The code supplies concrete zero/one tags and proves their substitution laws
inside candidate PRA. Parameter-dependent predicates and arbitrary finite
sets of induction instances are not covered by this theorem.

Candidate-PRA models now have a checked arithmetic reduct satisfying both
IΣ₀ and IOpen, via the [refreshed bounded comparison](reviews/parsons-bounded-post-preparation-replay/README.md)
and [model-reduct theorem](reviews/pra-model-isigma-zero-author-replay/README.md).
This is a prerequisite for pairing in arbitrary models; candidate primitive
recursive pairing and projection codes and their correctness proofs remain open.

A separate [87-operation adaptive output candidate](research/adaptive-first-root-factor87/README.md)
factors one root of the 88-operation thirteen-variable circuit. The finite
schedule audit and local signed-pair/`Expr.splitNatural` Lean lemmas have
[independent replays](reviews/adaptive-first-root-factor87-independent.md).
A separate [checked context lemma](reviews/adaptive-first-root-factor87-context-independent.md)
extends the rewrite to arbitrary actual one-hole expression substitutions.
The [full revised literal is now bound](reviews/adaptive-first-root-factor87-literal-independent.md)
to the maintained adaptive expression in Lean, including equality of split
values and the positive-shifted zero test in every commutative semiring. The
13-variable candidate still has no completed HA or PRA consistency endpoint.
The [87-gate arithmetic no-zero sentence](reviews/adaptive-factor87-sentence.md)
is closed and semantically equivalent to its parent over every commutative
semiring. A [checked HA derivation](reviews/adaptive-factor87-ha.md) now proves
the parent/reduced sentence equivalence, with an IΣ₀ proof as well. A
[candidate-PRA proof](reviews/adaptive-factor87-pra.md) now transfers that
IΣ₀ equivalence through the bounded comparison. Neither sentence is yet
internally connected to `Con(ZFC)`.

The later upstream merges through `166728f64b` changed ZFC validator modules
reachable from the maintained HA endpoint. Its earlier checked derivation is
snapshot evidence; a dependency-aware source-current replay of that endpoint
is still required. This does not assert a defect in the proof.

The candidate-PRA development also has a [unary Π₁ equivalence transfer](reviews/pra-pi-one-implication-root.md):
it eliminates one closed open-matrix Σ₁ induction instance from a proof of an
equivalence of two unary open-matrix Π₁ sentences. It does not yet bind the
actual equation or refutation sentences, and does not handle arbitrary finite
induction instances.

A [bounded-matrix extension](reviews/pra-bounded-one-induction-current-author-replay/README.md)
now removes one closed Σ₁-induction instance with any Σ₀ matrix on its
three stated arguments, using the candidate-PRA bounded characteristic
compiler. The unary Π₁ equivalence transfer has the same bounded-induction
extension. It still does not handle extra predicate parameters or an arbitrary
finite collection of induction instances.

Subsequent upstream merges changed `ArithmeticCarrierRadix2011.lean`,
`ArithmeticBinomLegendre.lean`, `ArithmeticHalfBinomial.lean`, and
`ArithmeticHalfBinomialSandwich.lean`. The affected adaptive population,
window, and reverse-construction suffix has since [passed two current-source
replays](reviews/adaptive-sandwich-postmerge2011-author.md), with the inherited
provider boundary documented there. A subsequent merge moved the rank-lower
proof into `ArithmeticHalfBinomial` and updated `ArithmeticAdaptivePopulation2011`
and `ArithmeticHalfBinomial2011`. The adaptive affected suffix has now [passed
two more source-current replays](reviews/adaptive-ranklower-postmerge2011-author.md);
the 14-variable wrapper is outside their scope. The AuxBind client has also
been replayed twice against the refreshed provider; the later CellWindow
continuation still needs a current-source replay.
Another subsequent merge changed HalfBinomial, AdaptivePopulation2011 and the
14-variable HalfBinomial wrapper. The affected adaptive suffix has now
[passed author and independent replays](reviews/adaptive-halfindex-postmerge2011-author.md).
The separate Pell rebase and AuxBind client also passed independent replays
against the refreshed provider; the 14-variable wrapper remains outside that
suffix.

A subsequent upstream merge changed eleven PRA prerequisites, including the
Boolean, exhaustion, search and order modules. The [43-module downstream
refresh](reviews/herbrand-all-instantiation-root.md) has now passed twice
alongside the new candidate-PRA witnessing theorem.

A later upstream merge generalized `PRAFormulaParameters.qr_rew` and updated
`PRAUniversalSyntax` to use it. The affected universal-presentation, syntax
and Herbrand replays below authenticate their earlier source snapshots; a
[source-current downstream rebuild](reviews/pra-parameter-current-root.md)
has now passed twice for the 17 affected committed modules.

The 14-variable equation in `equation.pdf` has closed IΣ₁ and HA
proof-existence theorems, but no Lean theorem producing the requested PRA
derivation. The candidate PRA development now includes an actual proof
calculus, an ordered-ring embedding, and characteristic codes for open
formulas with finitely many packed parameters. Lean now proves [candidate-PRA
witnessing for open ∀∃ formulas](reviews/herbrand-all-instantiation-root.md).
The formal IΣ₁-to-PRA conservation argument and the candidate's comparison
with a standard PRA presentation remain open.
The [PA-minus bridge audit](research/pra-peanominus-bridge-audit-20261029.md)
tracks the exact mapped equality axioms and all 17 non-equality axiom
families. Closed candidate-PRA derivations now cover all seventeen families,
including associativity, commutativity, distributivity, and the order axioms.
The [PA-minus translation](Lean/DiophantineConsistency/PRAPeanoMinusTranslation.lean)
now assembles them into a candidate-PRA derivation of every mapped PA-minus
theorem. The comparison with standard PRA and the conservation argument
remain open.
The [bounded-induction comparison](reviews/parsons-bounded-bridge-root.md)
now translates every Foundation IΣ₀ theorem and every proof in a bounded-only
rule calculus into candidate PRA. The original intermediate rule calculus
also permits Σ₁ induction, so this does not yet translate the strict Π₂
endpoint.
The finite Herbrand machinery now extracts disjunctions of unpaired term
triples from triple-existential candidate-theory proofs, with a separate
universally parameterized client. Separately checked [interactive
extractors](research/herbrand-interactive-20261029.md) produce
actual finite staged disjunction proofs with explicit parameter separation,
for one or three challenges per round. The checked four-witness coded-stage
chain now eliminates the finite stages and derives a candidate-PRA goal from
its specific universal-theory premise. Deriving that premise from arbitrary
Σ₁ induction proofs and handling multiple induction instances remain open.
Subsequent upstream merges changed `PRAQCompatibility`, `PRAPeanoMinusBasic`,
`PRAPeanoMinusOrderBasic`, `PRAQOrder`, and several addition and subtraction
providers, followed by `PRAEqualityDifference` and
`PRASubSuccessorInvariant`. The [24-module refresh](reviews/pra-peanominus-current-refresh-root.md)
and later [seven-module suffix](reviews/pra-peanominus-suffix-refresh-root.md)
each passed independent replays for their respective earlier source snapshots.
The [82-module current-source rebuild](research/pra-bounded-characteristic-20261029.md)
has since passed an author run and two isolated replays, including the complete
candidate-PRA Σ₀ characteristic compiler and bounded-matrix witness theorem.
These witnessing results start with a candidate-PRA proof; they do not provide
the missing rule-to-PRA comparison.
After those replays, an upstream merge changed `PRAExhaustion`, `PRANonzero`,
and `PRAPeanoMinusBasic`. A dependency-aware 92-module author rebuild and two
independent replays have since matched all source, object and full-log hashes,
including the bounded compiler, witness and induction-counterexample modules.
A further upstream merge changed `PRAAddOne`, bounded-search and order-witness
modules, and `PRASubReconstruct`. The 92-module and interactive extraction
replays therefore cover the preceding source snapshot; their affected
dependency graphs require another current-source rebuild.
The subsequent 108-module rebuild has now passed two independent replays,
including the candidate-PRA triple-witness client. Foundation and Mathlib
remain inherited boundaries; this does not establish the missing comparison.
A further merge changed bounded-formula and characteristic modules. The
affected candidate-PRA graph has since passed a 68-module author rebuild and
two independent replays with matching source, object and full-log hashes;
the separate extraction and bounded-comparison clients have also been rebuilt
and independently replayed against that provider.
A later merge changed bounded-search Code, Freeze, Invariant and Minimal as
well as the contextual extraction and selection modules. The 68-module and
downstream replays cover the preceding snapshot. The affected candidate-PRA
graph has since passed a 62-module author rebuild and two independent replays
with matching source, object and full-log hashes. The reordered 21-module
contextual extraction and six-module bounded-comparison descendants have also
passed independent replays against that provider.
A later upstream merge refactored finite and interactive Herbrand extraction,
contextual tree witness/selection, and valuation compactness. The checked
coded-stage chain covers the preceding snapshot. Its affected descendants and
a one-closed-coded-induction-axiom U-theory bridge have since passed a
45-module author rebuild and two independent replays. Arbitrary and multiple
induction instances remain open.
The [Foundation one-instance endpoint](Lean/DiophantineConsistency/PRAFoundationOneInduction.lean)
also eliminates one actual successor-induction instance for `codedSigma pred`
with `pred : Code 3` from a candidate-PRA proof of a universally closed open
existential goal. This is one closed instance with no external predicate
parameters; it is not arbitrary or multiple-instance IΣ₁ conservation.
The [collection-rule induction predicate and base](reviews/parsons-collection-rule-root.md)
are proved for Σ₁ relations, but assembling the inference still assumes a
proof of its finite-extension step. A further [semantic step](reviews/parsons-collection-semantic-root.md)
now proves that step under arbitrary assignments, yielding an unconditional
collection-rule transformer when the exact implication is parameter-free.
The [arbitrary-parameter collection rule](reviews/parsons-specialize-root.md)
is now proved as a noncomputable proof transformer by specializing the closed
finite-extension theorem. The [positive-guarded bounded rule](reviews/parsons-guarded-collection-root.md)
is also proved for Σ₁ side formulas and arbitrary parameters. These are
noncomputable proof transformers, not conditional collection axioms or
PRA-internal transformations. The complete cut-free translation and
IΣ₁-to-PRA witnessing remain open.
The [principal logical cases](reviews/parsons-logical-cases-root.md) now
provide the existential, universal, disjunction and conjunction transformers
with explicit strictly smaller local recursive hypotheses. Nonprincipal cases,
a fixed global projection and a global cut-free recursion remain open. The
[structural case](reviews/parsons-structure-root.md) now handles contraction
under any fixed projection and discharges actual PA-minus base axioms.
The [base-only branch](reviews/parsons-fold-root.md) now folds an arbitrary
side sequent and discharges any finite set of actual PA-minus axioms, without
a cut-free or recursive-hypothesis requirement.
The [marked-context invariant](reviews/parsons-invariant-root.md) now starts
from the actual normalized cut-free proof, retains occurrence-specific tags,
handles its base-only and contraction branches, and recovers the original
conclusion from a marked-output proof. The output proof and global induction
remain open.
The [marked induction-block cases](reviews/parsons-marked-block-root.md)
handle parameter opening and the final counter-witness under an explicit Σ₁
side-guard hypothesis and smaller local recursive proofs. Deriving that guard
from a general Π₂ context and assembling the global induction remain open.
The [marked universal case](reviews/parsons-shift-root.md) shifts every
nonprincipal marked entry coherently under the eigenvariable. Other marked
logical cases have now been completed for side-tagged occurrences in the
[marked logical cases](reviews/parsons-marked-logical-root.md). Principal
negative base-axiom decomposition and the single global recursion remain open.
The separate [negative-base state](reviews/parsons-base-state-root.md) now
handles universal opening and terminal resolution when its explicit Π₂/Σ₁
shape hypotheses hold. The [base-axiom shape theorem](reviews/parsons-base-shape-root.md)
now establishes the required universal-prefix/Σ₁ shape for every PA-minus
axiom and preserves it under opening and shifting. Integration and a
secondary recursion measure remain open.
The [unified marked context](reviews/parsons-unified-root.md) now integrates
these cases and proves a decreasing secondary base count for terminal
reclassification. Its final counter-witness case still assumes a Σ₁ side
guard, and the global recursion remains open. The [strict Π₂ disjunction
normalizer](reviews/parsons-prenex-pi2-or-root.md) supplies a bounded-matrix
tupled prenex form for a pair of strict ∀∃ side formulas. The corresponding
[strict conjunction normalizer](reviews/parsons-prenex-pi2-and-root.md) has
also been proved. The [tuple normalizers](reviews/parsons-prenex-tuple-root.md)
extend both connectives to arbitrary finite universal and existential blocks.
The [mixed-tree normalizer](reviews/parsons-prenex-tree-root.md) handles any
finite conjunction/disjunction tree of such blocks. The [side-list client](reviews/parsons-prenex-list-root.md)
normalizes a finite disjunction of supplied tree descriptors. The
source-derivation adapter and general Π₂ normalization remain open. [Height-preserving universal inversion](reviews/parsons-all-invert-root.md)
now opens selected side occurrences at arbitrary terms while retaining
cut-freeness and the strict bound below an existential inference. The
[fresh-variable client](reviews/parsons-fresh-open-root.md) opens a selected
universal side under the same strict bound while shifting the entire context.
The [finite-prefix counterexample rule](reviews/parsons-guard-prefix-root.md)
now opens an explicitly described finite universal guard, assuming that all
other projected sides are Σ₁ and that all strictly smaller derivations have
already been handled. [Guard rewriting](reviews/parsons-guard-rewrite-root.md)
preserves such descriptors under term substitution, and [fresh context
opening](reviews/parsons-fresh-context-root.md) selects a universal at any
side position without consuming the height margin. Multiple guards and the
global recursion are not yet discharged by these conditional lemmas.
In particular, a generated step mark can itself be non-prenex Π₂ and need
not carry a guard descriptor; a recursion restricted to guarded contexts
would therefore not suffice without an adapter that preserves the height bound.
The [finite guarded-context counterexample case](reviews/parsons-counter-context-root.md)
now handles any number of descriptor-bearing sides, using a separate
decreasing formula-complexity measure and the explicit `Below H` hypothesis.
The [Boolean-tree version](reviews/parsons-counter-tree-root.md) extends that
local case to finite positive Boolean trees, with an additive node measure.
For strict Σ₁ predicates with bounded matrices, [step descriptors](reviews/parsons-step-tree-root.md)
now cover the actual generated step and negative sides, and [finite-prefix
descriptors](reviews/parsons-strict-prefix-tree-root.md) extend this to any
finite existential prefix over a bounded matrix. Arbitrary Foundation Σ₁
syntax and the global induction remain open.
The [tree logical invariant](reviews/parsons-tree-logical-root.md) is now
preserved through ordinary logical and contraction premises, while the
[strict-block invariant](reviews/parsons-strict-invariant-root.md) preserves
finite-prefix induction blocks and their generated side descriptors. These
do not establish the remaining base-terminal cases or global recursion.
The [restricted counterexample case](reviews/parsons-counter-strict-root.md)
requires its smaller derivations only for tree-side, strict-block contexts.
A separate [actual PA-minus axiom certificate](reviews/parsons-base-positive-root.md)
now supplies Tree descriptors for terminal base reclassification, including
the axiom with an unbounded existential. The [marked base invariant](reviews/parsons-base-invariant-root.md)
preserves that certificate through initial contexts, shifts, contraction,
opening and terminal reclassification. The [strengthened counterexample
case](reviews/parsons-counter-stable-root.md) now incorporates this base
certificate into the restricted smaller-derivation hypothesis. The global
recursion is now [proved for the restricted invariant](reviews/parsons-global-strict-root.md):
cut-free derivations with Tree sides, strict induction blocks and actual-axiom
base certificates yield PA-minus rule proofs. The [strict-fragment
endpoint](reviews/parsons-strict-initial-root.md) connects an actual
Foundation proof with strict induction and a Tree conclusion to the rule
calculus. Handling arbitrary Σ₁ induction and eliminating the rule calculus
into candidate PRA remain separate requirements. A [strict Π₂ client](reviews/parsons-strict-pi-two-root.md)
constructs the Tree certificate for a universally closed existential with a
Σ₀ matrix; it still concludes in the intermediate rule calculus.
The [identity and truth leaves](reviews/parsons-leaves-root.md)
are now proved for arbitrary unified contexts.

For the selected 13-variable adaptive equation, the actual-zero arithmetic
now reaches [exact Pell indices](reviews/adaptive-exact-indices2011-root.md),
[power recovery](reviews/adaptive-power-finish2011-root.md), and the
[aligned radix](reviews/adaptive-radix2011-root.md) in arbitrary IΣ₁ models.
The [normalized transport](reviews/adaptive-transport-restoration2011-root.md)
has also been recovered from the actual adaptive zero and independently replayed.
The corresponding [rank-population lower bound](reviews/adaptive-population2011-root.md)
is now independently replayed for every internal exponent matching the radix.
The [actual-zero window theorem](reviews/adaptive-window2011-root.md) now
assembles these inputs in arbitrary IΣ₁ models. The window-to-machine halt
client, internal converse and final HA/PRA proof-existence endpoints remain
open. The [reverse transport identity](reviews/adaptive-construction-transport2011-root.md)
is now proved from the positive 14-coordinate equation system, but the other
reverse witnesses and adaptive zero construction remain open. The
[auxiliary phase client](reviews/adaptive-construction-aux-bind2011-root.md)
constructs the positive adaptive auxiliary coordinate from the original
equations when the rank phase and exact Pell-ordinate identity are supplied;
those facts must still be exposed for the chosen halting construction.
The [strong-factor identity](reviews/adaptive-construction-strong2011-root.md)
now follows from the maintained strong norm with the scaled multiplier.
The [auxiliary witness positivity lemma](reviews/adaptive-construction-aux2011-root.md)
proves `y-u>0` from the auxiliary norm when `y ≥ 2`; the
[coordinate client](reviews/adaptive-construction-aux-client2011-root.md)
binds this to the actual 14-coordinate equations. The ordinate bound and
the rest of the witness map still need binding to the actual construction.
The [Pell phase bound](reviews/adaptive-construction-aux-phase2011-root.md)
now proves `ycoord R b ≥ 2` for `R % 4 = 3`; binding the construction's
actual ordinate identity to the client remains open.
The [first and main carrier identities](reviews/adaptive-construction-carrier2011-root.md)
are now proved under explicit witness relations; deriving those relations and
the complete adaptive zero remains open.

Lower-variable forms are also part of the objective. The existing
[`GapSourceExistence66`](Lean/DiophantineConsistency/GapSourceExistence66.lean)
and [`SplitNineSource59`](Lean/DiophantineConsistency/SplitNineSource59.lean)
give nine-coordinate standard-natural existence comparisons to parameterized
source rows, under their stated validity bounds. These source comparisons do
not themselves identify the fixed equation with ZFC consistency or produce
an internal IΣ₁, HA, or PRA proof of that equivalence. They do not discharge
the other selected compact or quartic forms. Later entries record historical
checkpoints and should be read in light of this current scope.

## What is already proved

For the maintained 14-positive-variable equation,
[`HACurrentEquation2011.isigma1_proves_current_iff_consistency`](Lean/DiophantineConsistency/HACurrentEquation2011.lean)
is a closed Lean theorem producing a Foundation IΣ₁ proof of the equivalence
between the literal shifted no-zero sentence and Foundation's ZFC consistency
sentence. In the same module, `ha_current_iff_consistency` is a closed Lean
theorem producing the corresponding derivation in the repository's HA
calculus. The proof passes through the polynomial, machine and source bridges
in arbitrary internal models. These statements do not assert consistency of
ZFC itself.

The repository also records the mathematical consequence of Parsons'
Π₂-conservation theorem: IΣ₁ is Π₂-conservative over PRA. See, for example,
[Joosten, *Two Proofs of Parsons' Theorem*](https://www.phil.uu.nl/ozsl/articles/joosten01.pdf).
This is presently an **external mathematical argument**, not a Lean theorem
producing a PRA derivation. In particular, the `isigma1_proves...` Lean theorem
has an IΣ₁ conclusion; its docstring's PRA claim is not an additional Lean
conclusion. A repository and pinned Foundation source search found no PRA
calculus or formalized Parsons theorem. Thus the requested Lean PRA endpoint
remains open, even for the maintained equation. The previous HA progress
estimate predates the closed HA endpoint and does not estimate the PRA work.

The [source audit](research/pra-conservation-source-audit-20261029.md)
identifies Foundation's existing cut-elimination theorem and explains the
remaining arithmetic reduction and witnessing work. It also examines a direct
primitive-recursive witness route; neither route is already formalized.

A [first-order PRA design](research/pra-first-order-language-design-20261029.md)
specifies arity-indexed primitive-recursive codes, defining equations, full
language equality, parameterized quantifier-free induction and the exact
ordered-ring embedding. It is a design, not yet a Lean implementation.

The first [primitive-recursive function code module](Lean/DiophantineConsistency/PRAFunctionCodes.lean)
now represents fixed-arity codes and proves their exact correspondence with
Mathlib's primitive-recursive vector functions. Its [independent replay](reviews/pra-function-codes-root.md)
passed. The [finite syntax](Lean/DiophantineConsistency/PRAFiniteFunctionCodes.lean)
has decidable equality and a surjective semantics-preserving conversion; its
[independent replay](reviews/pra-finite-function-codes-root.md) also passed.
A [numeric codec](Lean/DiophantineConsistency/PRACodeEncoding.lean) now
has a proved arity-checked roundtrip and an [independent replay](reviews/pra-code-encoding-root.md).
The [first-order language](Lean/DiophantineConsistency/PRALanguage.lean)
now embeds the existing ordered-ring language and has a checked natural-model
reduct; its [independent replay](reviews/pra-language-root.md) passed.
The [candidate PRA theory](Lean/DiophantineConsistency/PRATheory.lean)
now defines its full axiom families and proves standard-natural-model validity;
its [independent replay](reviews/pra-theory-root.md) passed. A closed [object-theoretic add-one theorem](reviews/pra-add-one-root.md)
now connects the designated addition and successor symbols in that theory.
The [predecessor exhaustion theorem](reviews/pra-exhaustion-root.md) is also
a closed derivation using its recursion and open-induction axioms. The
[addition clauses](reviews/pra-addition-root.md) are also derived in the
candidate object theory; the [multiplication clauses](reviews/pra-multiplication-root.md)
have likewise been derived.
Compatibility with a standard PRA presentation, further arithmetic bridges,
primitive-recursive axiom recognition and conservation remain open. This is not a uniform primitive-recursive evaluator.

The [candidate universal-presentation equivalence](reviews/pra-universal-equivalence-root.md)
now proves the same sentence-level theorems in the explicitly defined universal
axiom family and candidate PRA, with arbitrary open-induction parameters. The
result uses completeness externally and does not yet identify the candidate
with standard PRA or establish a witnessing or conservation theorem.
The [universal syntax certificate](reviews/pra-universal-syntax-root.md) now
proves that every axiom in that presentation has a universal prefix and an
open matrix. An effective recognition theorem is still required.
The [finite witness selector](reviews/pra-finite-witness-root.md) collapses a
provable finite disjunction of explicit candidate witnesses to one fixed PR
witness. Extraction of that disjunction from a general proof remains open.
The [open-matrix selection bridge](reviews/pra-herbrand-selection-root.md)
now accepts the actual Foundation open formula and a finite-disjunction proof
in the universal theory, yielding a candidate-PRA proof at one PR witness.
The [existential-sequent structure](reviews/herbrand-existential-sequents-root.md)
shows the relevant cut-free proofs contain no universal-rule nodes and collects
their existential terms. [Finite extraction](reviews/herbrand-finite-extraction-root.md)
now derives a disjunction for a prepared existential sequent. The
[prepared-sequent parameterized witness](reviews/herbrand-parameterized-witness-root.md)
translates the extracted terms into appropriately parameterized PR codes for
that input. The [general ∀∃ preparation and candidate-PRA witnessing](reviews/herbrand-all-instantiation-root.md)
are now proved for open matrices.

The [adaptive 13-variable expression binding](reviews/adaptive-expression2011-root.md)
now identifies the exact accepted polynomial and proves its single positive
shift over arbitrary commutative semirings. The [internal factor-magnitude theorem](reviews/adaptive-factor-magnitude2011-root.md)
now derives magnitude one for the four actual factors from the literal zero.
The [factor-unit theorem](reviews/adaptive-factor-units2011-root.md) now
excludes the negative units by internal modulo-four reasoning and derives all
four positive units. The [scaled-norm theorem](reviews/adaptive-scaled-norms2011-root.md)
derives both actual scaled Pell equations and positive scales. An [internal square-divisibility theorem](reviews/arithmetic-square-divisibility-root.md)
now proves the required positive-scale cancellation, including zero roots.
The [adaptive quotient client](reviews/adaptive-quotients2011-root.md)
now applies it to construct both positive unscaled roots from the actual
natural zero. The [first-root divisibility client](reviews/adaptive-first-divisibility2011-root.md)
now derives a positive internal quotient `Y/q³` from the actual natural zero.
The [transport theorem](reviews/adaptive-transport2011-root.md) now derives
the actual positive transport and gap. The [transport quotient theorem](reviews/adaptive-transport-quotient2011-root.md)
now derives the exact positive transport multiple. The [main-root orientation theorem](reviews/adaptive-main-orientation2011-root.md)
now derives its positive signed representation. The [Pell index client](reviews/adaptive-pell-indices2011-root.md)
constructs positive bounded indices for both recurrences from the actual zero.
Their exact relation and power recovery have since been established as linked
above; the full zero-existence equivalence remains open.

The [exact hierarchy certificate](reviews/arithmetic-current-hierarchy2011-root.md)
now proves in Lean that both maintained source sentences are Π₁ and their
literal biconditional is Π₂. Its source-current replay was performed at the
recorded prior snapshot; subsequent upstream commits changed some prerequisite
sources. The certificate supplies a conservation input, not conservation or
PRA derivability itself.

The [cut-free adapter](reviews/parsons-cut-free-independent.md) now turns an
actual finite Foundation theory proof into a cut-free derivation with the
same axiom list. [Height-preserving conjunction inversion](reviews/parsons-selection-independent.md)
is now established for arbitrary cut-free contexts. Induction-axiom reduction
and the PRA witnessing theorem remain open. The [guard syntax](reviews/parsons-guard-independent.md)
now preserves Σ₁ complexity and side parameters under substitution, preparing
the intended induction-rule case. The [guarded three-premise transformer](reviews/parsons-rule-independent.md)
now constructs that isolated case in an explicit Σ₁-rule calculus; the whole
cut-free reduction and PRA witnessing are not yet established. A
[finite-context bridge](reviews/parsons-rule-embedding-independent.md) now
embeds Foundation proofs into the rule calculus over the same base theory;
it does not remove any induction axioms.

The [mapped Robinson Q result](reviews/pra-q-compatibility-root.md) now
proves that all actual Foundation Q axioms except its strict-order definition
map to theorems of the candidate PRA. The [subtraction recursion clauses](reviews/pra-subtraction-root.md) are
also proved in the candidate theory, as preparation for the order clause.
The [nonzero-bit recursion](reviews/pra-nonzero-root.md) is also proved.
The [nonzero-bit characterization](reviews/pra-nonzero-character-root.md)
is now an object-theory derivation in all models. The order clause and full
compatibility remain open.

## Concrete bridge to formalize

1. Choose and define a precise PRA language and proof calculus, including its
   primitive-recursive function symbols, defining equations and induction
   scheme. State the desired Lean conclusion using its actual derivability
   predicate. Bind the arithmetic language of the existing IΣ₁ proof to that
   PRA language, including the same Gödel coding and ZFC theory.
2. Prove in Lean that the exact equivalence is in the Π₂ fragment accepted by
   the conservation theorem, or produce a provably equivalent Π₂ normal form
   and a PRA derivation transporting the result back. Foundation's
   `Theory.consistent` is constructed as a Π₁ sentence; the current no-zero
   sentence is a universal closure of a negative equality. Their biconditional
   is a Boolean combination of Π₁ sentences, so the exact syntactic or
   normal-form bridge must account for both directions, coding of the fourteen
   variables, and the conservation theorem's precise language and hierarchy.
3. Formalize an applicable proof of Π₂ conservation, or a verified proof
   transformation with an equivalent precise contract. A prose reference,
   a new axiom, a standard-model truth argument, or an unproved transfer
   premise does not establish the requested endpoint. The conservation proof
   is substantial and cannot be inferred merely from the existing Lean
   completeness argument.
4. Apply the formalized transfer to the closed IΣ₁ theorem and export a
   closed Lean theorem asserting existence of a PRA proof of the exact stated
   equivalence. Check the actual theorem's axioms and the entire dependency
   chain. Establish corresponding internal transformations and endpoints for
   the other selected size-metric equations; external equivalence of their
   standard natural-number zero sets alone does not supply a PRA proof.

A possible classical normal-form calculation illustrates step 2. If
`A = ∀ a, P(a)` and `B = ∀ b, Q(b)`, then `A → B` is classically equivalent
over nonempty natural-number domains to `∀ b, ∃ a, (P(a) → Q(b))`, and the
other direction is analogous. Combining and coding the variables gives a Π₂
form when the matrices are suitably bounded or primitive recursive. This is
a route to investigate, not a Lean proof of the required equivalence or of
the conservativity theorem.

The task also continues to seek smaller rigorously certified equations;
size improvements and the proof-existence results for each proposed form must
be tracked separately.

## All Q axiom images in the candidate theory

The [Q-order client](reviews/pra-q-order-root.md) proves the additive
witness characterization of represented strict order in arbitrary
candidate-PRA equality models and obtains `PRA_proves_all_Q`: each actual
Foundation Robinson Q axiom maps to a closed candidate-PRA derivation.
This is not yet a proof translation for arbitrary Q derivations, an
equivalence with standard PRA, or an IΣ₁-to-PRA conservation theorem.

The [Q theorem translation](reviews/pra-q-translation-root.md) now proves
that every actual Foundation Q theorem has a candidate-PRA proof of its
mapped sentence. It is an existence theorem by soundness and completeness,
not a primitive-recursive proof transformer or a conservation theorem.

The [parameterized open induction rule](reviews/pra-induction-rule-root.md)
is admissible in the candidate PRA theory: closed proofs of the base and
step yield a closed proof of the induction conclusion. This does not yet
admit the Σ₁ rule required for Parsons conservation.

The [Parsons open-rule adapter](reviews/pra-parsons-open-rule-root.md)
connects candidate PRA’s quantifier-free induction rule to the exact
`ParsonsRule.base` and `step` definitions. The general Σ₁ rule and its
witnessing reduction are still open.

The [explicit order witness](reviews/pra-q-witness-root.md) supplies a
closed candidate-PRA proof using `pred(y-x)` as the witness for strict
order. The subtraction-to-Q provider chain was rebuilt after the upstream
source merge. General Σ₁ witnessing and conservation remain open.

The [finite order-witness code](reviews/pra-q-witness-code-root.md) packages
`pred(y-x)` into one primitive-recursive function symbol, proves its
all-model meaning, and derives its witness statement in candidate PRA.
The [witnessing note](research/pra-witness-bridge-20261029.md) records the
remaining general Σ₁ and presentation obligations.

The [term compiler](reviews/pra-term-compilation-root.md) now maps every
candidate-language term with finitely many bound inputs to one finite PR
code and proves its equality to that term inside candidate PRA. This is a
definitional-extension ingredient; formula normalization and general Σ₁
witnessing remain open.

The [selected PA-minus bridge](reviews/pra-peano-minus-partial-root.md)
derives the exact mapped Foundation addition-commutativity, additive-order
witness, addition-zero and multiplication-zero axioms in candidate PRA.
The remaining PA-minus axioms, formula compilation and the full
conservation argument remain open.

The [open-semisentence characteristic theorem](reviews/pra-equality-code-root.md)
is now unconditional: a concrete finite equality code discharges both
certificates, so every Foundation open semisentence with finitely many bound
inputs has a PR characteristic and a candidate-PRA proof of correctness.
Free-parameter packing, bounded formulas, universal presentation and
general Σ₁ witnessing remain open.

The [formula-parameter packing](reviews/pra-formula-parameters-root.md)
extends the open characteristic result to arbitrary free numerical parameters
by explicit finite argument packing with an exact evaluation theorem.
Bounded formulas, universal presentation and Σ₁ witnessing remain open.

The [characteristic bit theorem](reviews/pra-characteristic-bit-root.md)
now supplies actual candidate-PRA proofs of both Boolean range and formula
correctness for every open formula after packing its free parameters.
Bounded formulas and Σ₁ witnessing remain open.

The [selection code](reviews/pra-select-code-root.md) has both defining
equations as closed candidate-PRA derivations and an all-model composition
interface. A bounded search invariant and universal presentation remain open.

The [bounded-search code](reviews/pra-bounded-search-code-root.md) now has
its all-model zero and step equations for arbitrary fixed predicates and
parameters. Its search correctness and universal presentation are still open.

The [bounded-search invariants](reviews/pra-search-invariants-root.md) now
provide closed candidate-PRA candidate and predecessor conditions for any
fixed predicate code. A separate logical lemma derives Boolean induction
from these conditions, bitness, successor exhaustion and base/step. The
actual universal theory, presentation equivalence and general Σ₁ witnessing
remain open.
