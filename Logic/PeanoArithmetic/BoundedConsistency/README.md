# Bounded-complexity consistency for Peano arithmetic

This project studies the following **numeralwise consistency scheme** for
first-order Peano arithmetic (PA): for every natural number `n` chosen in the
metatheory, PA proves that no PA derivation in which every formula occurrence
has at most `n` quantifier groups derives falsity.

The phrase “every formula occurrence” and the metatheoretic status of `n` are
essential.  They are part of the formal specification, not presentational
details.

> **Current status.**  The requested numeralwise scheme is complete in both
> Lean and Rocq/Coq.  Each port exports, for every metatheoretic natural
> `n`, an actual object-level PA derivation of its represented sentence
> `Con_n(PA)`.  Both represented proof predicates inspect every formula
> occurrence in arbitrary, possibly nonstandard, coded PA derivations.
>
> **The strictly stronger uniform sentence is now proved in Lean.**  The
> single object sentence `PA ⊢ ∀ n, Prov_PA(⌜Con_n(PA)⌝)`, whose level
> quantifier lies inside the object language and therefore ranges over
> nonstandard elements of nonstandard models, is the unconditional theorem
> `UniformInternalProvabilityTheorem.pa_proves_uniformRestrictedConsistencyProvability`.
> Its audited assumptions are exactly Lean's three standard axioms
> `[propext, Classical.choice, Quot.sound]`.  In Rocq/Coq the corresponding
> sentence remains **conditional** on explicit proof-producing compiler
> premises; see
> [Internal provability of the bounded-consistency
> instances](#internal-provability-of-the-bounded-consistency-instances) for
> their exact statements and status.  The two ports therefore no longer have
> parity at this specific endpoint, and this document does not claim they do.
>
> **Development details.**  The Lean and Rocq/Coq phase-one developments
> machine-check a metatheoretic restricted-proof construction and its semantic
> consistency consequences for the repository's PA/HF natural-deduction
> calculus.  Rocq additionally has canonical natural-number codes, total
> decoders, and an executable checker for those restricted proof trees, with
> exact quotation and soundness theorems.  Lean now goes beyond standard
> codes: in every possibly nonstandard model of `I Sigma 1` it represents the
> coded polarity rank, all-occurrences restricted derivation predicate, and
> fixed-external-bound consistency sentence.  It also has represented coded
> term evaluation, nonstandard-code shift/substitution transport, and a
> rank-zero formula truth predicate with structural and Boolean Tarski
> clauses and semantic transport under negation, shift, and substitution.
> Lean also proves every rank-zero logical inference sound for arbitrary
> nonstandard restricted-derivation codes, discharges the full internal PA
> axiom recognizer at rank zero, and obtains the actual object theorem
> `PA ⊢ Con_0(PA)`.  It now also defines externally indexed Sigma/Pi partial
> truth predicates over nonstandard codes, proves their fixed-level
> definability, and establishes oriented Boolean/quantifier Tarski clauses,
> including both polarity switches.  Rocq now has both the earlier
> standard-model representing formula and a transparent canonical arithmetic
> formula describing accepting traces of the concrete compiled checker.  The
> compiler theorem proves that the canonical machine accepts exactly when the
> executable restricted-proof checker returns true on standard naturals, and
> the trace certificate shell has been unfolded in arbitrary raw PA models.
> Rocq also has a generic route from arbitrary raw-model validity to an
> object-level PA proof, and the canonical fixed-bound consistency sentence
> is now proved equivalent to rejection of accepting canonical traces in
> every raw PA model.  The finite transition formula and every internally
> indexed adjacent pair in its beta-coded trace are now reflected exactly to
> raw-carrier steps of the concrete Minsky program.  Beta functionality now
> makes those local descriptions agree on every live counter, while the
> canonical initial state, accepting output, and final program-counter
> boundary are decoded exactly from one graph witness.  A PA
> zero-or-successor argument further identifies them with one genuine full
> state at the possibly nonstandard final index.  A PA-definable invariant
> can now be propagated across the entire trace by internal PA induction;
> the explicit no-accepting-exit invariant has verified initial and final
> clauses, leaving its concrete one-step preservation theorem open.  Rocq now
> also has transparent polynomial formula/term-code constructors and exact
> one-constructor Sigma/Pi rank equations over arbitrary raw-model elements.
> PA now proves that the concrete polynomial pairing constructor is injective,
> which makes its list nodes and code constructors unambiguous in every raw PA
> model.  PA-order antisymmetry also makes every local maximum and constructor
> rank equation functional.  A synchronized model-internal beta traversal now
> stores formula codes and both ranks, has exact arbitrary-model semantics,
> and computes the external Sigma/Pi ranks uniquely on every standard
> quotation.  PA induction on a traversal index now proves that completely
> unrelated certificates also agree at every arbitrary nonstandard root, and
> this functionality is itself closed into an object-level PA derivation.
> A separate postorder syntax certificate now characterizes well-formed roots
> inside each model.  PA-definable induction and internally derived CRT
> capacity construct their synchronized rank tables even through nonstandard
> bounds; PA itself proves totality of the rank graph on that honest domain.
> A beta-coded assignment formula now additionally has exact arbitrary-model
> lookup semantics, functional values, and PA-provable de Bruijn binder
> extension through every possibly nonstandard model-internal prefix.  The
> five coded-term constructors now have transparent local evaluation rows,
> with recursive values read from beta tables and exact raw-model semantics;
> pairing injectivity and beta functionality make the unified local evaluator
> single-valued even when its constructor witnesses are chosen independently.
> A global support/value beta certificate now has exact raw semantics and is
> proved cross-certificate functional by genuine PA induction, with that
> functionality itself closed into an object-level PA derivation.  Finite beta
> realization additionally constructs the expected certificate for every
> standard quoted term, including pairs of terms over one shared assignment.
> A model-internal syntax/support certificate now characterizes arbitrary
> nonstandard term codes, and genuine PA induction constructs their value
> tables.  A step-parametric capacity trace removes the apparent circularity
> in choosing one beta modulus before the nonstandard value table is known:
> PA induction builds a bound valid for every sufficiently large common step,
> and hence proves unconditional existence and uniqueness on the honest
> syntax/assignment domain.
> Equality, falsity, implication, conjunction, and disjunction also now have
> transparent rank-zero truth-bit rows with exact arbitrary-model semantics,
> and the unified rank-zero row is proved single-valued.  A global supported
> truth certificate ties equality atoms to genuine term certificates on one
> assignment and Boolean rows to smaller supported children.  PA induction
> proves cross-certificate functionality at nonstandard bounds, and raw-model
> completeness closes that fact into an object-level PA derivation.  On every
> standard quantifier-free quotation, finite beta realization now constructs a
> certificate whose unique output is one exactly when the raw formula is true
> and zero exactly when it is false.
> An independently arithmetized quantifier-free syntax certificate now also
> drives the truth-table construction through arbitrary nonstandard bounds.
> PA supplies the truth-bit CRT capacity internally, while the uniform term
> capacity theorem supplies evaluation certificates for equality operands.
> Thus every realizable nonstandard rank-zero syntax code has a unique truth
> certificate, and this totality is itself closed into an object-level PA
> derivation.
> Rocq also now has externally indexed local Sigma-truth and Pi-falsity rows
> at every fixed level.  Their exact raw-model semantics cover all Boolean and
> quantifier constructors; opposite-polarity quantifiers correctly recurse on
> the quantified child under a freshly prepended coded assignment.  Global
> certificate assembly, coherence, assignment transport, and the fixed-level
> Tarski interface are all proved over arbitrary raw PA models.
> Rocq now also exposes every one of the seventeen raw-proof constructor codes
> as a transparent PA term.  Their common constructor formula has exact
> semantics in every law-free raw arithmetic structure, and quotation agrees
> with the executable natural-number proof code in every raw PA model.  PA now
> also proves that every recursive premise field is strictly smaller than its
> enclosing proof code, uniformly for all fourteen recursive constructors.
> An honest beta-supported proof-syntax traversal now closes every constructor
> occurrence and every recursive premise through arbitrary nonstandard bounds;
> its constructor-occurrence totality is itself an object-level PA theorem.
> Lean now has full fixed-level polarity coherence, shift/substitution
> transport, a unified bounded truth interface, and soundness of every coded
> logical inference conditional only on truth of the recognized PA axiom.
> Its quotation-adequacy theorem now discharges every code recognized by the
> finite `PeanoMinus` branch at arbitrary positive levels.  A represented
> induction argument also discharges the genuinely nonstandard induction
> branch, including nonstandard formula codes and universal-closure lengths.
> Splitting the complete recognizer, applying nonstandard derivation
> soundness, and then first-order arithmetic completeness gives the full Lean
> object theorem `PA ⊢ Con_n(PA)` for every external `n`.  Rocq/Coq now proves
> the parallel theorem by an independent raw-model development: it validates
> all seventeen proof constructors, proves every witnessed PA-axiom context
> true (including nonstandard induction instances), excludes restricted
> proofs of falsity in every PA model, and applies first-order completeness.

## The intended theorem

Fix a Gödel coding of PA formulae and derivations.  Let `AHBound(n, p)` mean
that `p` codes a formula in `Sigma_n` or `Pi_n` of the arithmetical hierarchy,
with bounded quantifiers ignored in the usual way.  Define

```text
RestrictedProof_n(d, p) :=
  d is a PA derivation of p, and
  every formula occurrence at every node of d satisfies AHBound(n, -).

Con_n(PA) := not exists d, RestrictedProof_n(d, code(false)).
```

For a one-sided sequent calculus, “every formula occurrence” includes every
formula in every sequent, every principal formula, every premise formula, and
every cut formula.  It also includes the formula used by an axiom instance.
Equivalent bookkeeping is required for natural deduction or a Hilbert
calculus.  Restricting only axioms, only cut formulae, or only the concluding
sentence is not the statement of this project.

The target is an externally indexed family of formal derivations:

```text
for each metatheoretic n : nat, construct a derivation PA |- Con_n(PA).
```

In Lean or Coq this may be exposed as a theorem with a host-language argument
`n : Nat`/`n : nat`, returning an object-level PA derivation.  The parameter is
specialized by the proof assistant before the resulting PA proof is read.  It
must not be silently strengthened to the single object-level assertion

```text
PA |- forall n, Con_n(PA).
```

## Why the bound covers the entire proof

Falsity is quantifier-free.  Therefore, if the restriction were imposed only
on the final statement, then for every `n` the alleged theorem would simply
say that PA has no proof of falsity at all: it would be the ordinary
consistency statement `Con(PA)`.  Under the usual consistency and
representability hypotheses, Gödel's second incompleteness theorem prevents
PA from proving that statement.

The all-occurrences restriction changes the claim.  A fixed complexity bound
allows a fixed partial truth definition.  That partial truth predicate can be
proved compositional for every formula appearing in the restricted
derivation, so PA can verify the soundness of that restricted derivation
without defining truth for arbitrary arithmetic formulae.

This restriction also has to be visible in the arithmetized proof predicate.
It is not enough to observe externally that each standard proof is finite and
therefore has a maximum formula complexity.  An internal PA theorem quantifies
over nonstandard proof codes in nonstandard PA models as well.

## Phase-one hierarchy measure and the coded bridge

The phase-one ports compute two polarity-sensitive syntactic ranks
simultaneously, one `Sigma`-oriented and one `Pi`-oriented.  Atoms have level
zero.  Boolean connectives combine the corresponding ranks componentwise;
negation and the antecedent of implication exchange the two polarities.
Universal and existential quantifiers preserve an already matching outer
block and add a level when the polarity switches.  Consequently, Boolean
branches with different leading polarities are aligned at the correct higher
level rather than being underestimated by a raw maximum over syntax-tree
branches.

For example, the two branches of

```text
(exists x, P(x)) and (forall y, Q(y))
```

have opposite polarities.  The mutually computed ranks place their conjunction
at the next level; they do not incorrectly call the whole formula a one-group
formula merely because each individual branch has one group.

This remains the **external, metatheoretic** hierarchy measurement for the
phase-one PA/HF syntax.  Lean's `CodedHierarchy` module independently performs
the corresponding recursion on Foundation's actual Gödel codes in arbitrary
models and proves agreement on every standard quotation.  Rocq's
`CodedSyntax` proves the analogous agreement for its canonical natural-number
codes, but that computation has not yet been internalized for arbitrary
nonstandard PA models.

The Lean foundation library supplies the closely related typed predicate
`LO.FirstOrder.Arithmetic.Hierarchy`.  Its constructors preserve level across
genuinely bounded quantifiers, preserve a block of matching polarity, and
increase the level when polarity alternates.  The intended final domain
predicate on Gödel codes corresponds to

```text
Hierarchy Sigma n phi or Hierarchy Pi n phi.
```

Bounded quantifiers must still be addressed at the final correspondence
boundary: the small phase-one syntax represents only primitive unbounded
quantifiers, while Foundation's typed hierarchy treats genuine bounded
quantifiers as level-preserving abbreviations.  No theorem currently equates
the PA/HF host rank with Foundation's implication-free NNF rank across that
change of syntax.

## What phase one checks

Both phase-one developments separate four notions which are easy to conflate:

1. the ordinary proof relation;
2. a data-carrying proof tree whose numeric rank bounds every formula
   occurrence by a fixed polarity-sensitive hierarchy level;
3. the resulting restricted-provability relation; and
4. semantic soundness or consistency of that restricted relation under the
   corresponding semantic hypotheses.

The repository's original proof relation lives in `Prop`, so proof
irrelevance prevents either kernel from computing a numeric rank by inspecting
an ordinary proof witness.  Both ports therefore mirror the 17 inference rules
in a `Type`-valued `ProvTree`.  Erasure maps a tree to an ordinary proof, while
ordinary derivability propositionally supplies a tree.  Thus the mirror is a
faithful data presentation of the same calculus, not an added proof system.

Erasing the ranked tree recovers an ordinary proof.  Consequently,
restricted provability implies ordinary provability.  Both ports then combine
erasure with the existing soundness theorem and validity of the PA axioms in
the standard natural-number model to rule out a restricted derivation of
falsity for every external bound, without assuming PA's consistency.  This
phase-one theorem is not a new internal soundness proof by partial truth.

These are genuine kernel-checked metatheorems about the phase-one datatypes.
They do not assert that PA represents those datatypes or proves their
soundness.

### Lean theorem surface

The module `BoundedPAConsistency.Basic`, in namespace
`LeanProofs.BoundedPAConsistency`, provides:

- `sigmaRank`, `piRank`, `quantifierGroups`, and `QuantifierBounded`;
- `hierarchyRanks_rename` and `hierarchyRanks_subst`, together with the
  corresponding one-rank and boundedness corollaries;
- `contextRank`, `nodeRank`, the `Type`-valued `ProvTree`, and numeric
  `proofOccurrenceRank`; the rank includes each node's conclusion, its entire
  displayed context, every formula-valued rule parameter, and all recursive
  premises;
- `eraseProvTree` and `provTree_complete`, proving the two directions of the
  faithful relationship with `PA.Formula.Prov`;
- `ProofAllBounded`, `RestrictedProv`, and theory-relative `RestrictedBProv`;
- monotonicity in the bound and metatheoretic cofinality of the restricted
  relations among all finite ordinary derivations;
- `restrictedProv_erase` and `restrictedBProv_erase`;
- `conclusionRestrictedProv_bot_iff` and
  `conclusionRestrictedBProv_bot_iff`, which formally expose the
  conclusion-only error; and
- the external theorem
  ```lean
  theorem restrictedPA_consistent_standard (n : Nat) :
      ¬ RestrictedBProv n PA.Formula.Ax_s [] PA.Formula.bot
  ```

### Rocq/Coq theorem surface

The module `BoundedPAConsistency.BoundedConsistency`, inside
`PABoundedConsistency`, provides the parallel definitions `sigmaRank`,
`piRank`, `quantifierGroups`, `QuantifierBounded`, `contextRank`,
`ProvTree`, `proofOccurrenceRank`, `ProofAllBounded`, `RestrictedProv`, and
`RestrictedBProv`.  Its tree erasure/completeness, preservation,
monotonicity, cofinality, and conclusion-only-collapse lemmas parallel the Lean
surface.  Its headline phase-one result is:

```coq
Theorem restrictedPA_consistent_standard : forall n,
  ~ RestrictedBProv n Formula.Ax_s [] pBot.
```

Both occurrence ranks explicitly cover each formula-valued inference-rule
parameter.  Term parameters cannot change formula rank.

The raw coded development then represents the all-occurrences restriction,
fixed-level partial truth, proof-rule validation, and PA-axiom truth inside
arbitrary raw PA models.  Its final premise-free object theorem is:

```coq
Theorem PA_BProv_restrictedPAConsistencyFormula : forall level : nat,
  Formula.BProv Formula.Ax_s []
    (restrictedPAConsistencyFormula level).
```

As in Lean, `level` is a host-language parameter.  This is a numeralwise
family of PA derivations, not a derivation of `forall level, Con_level(PA)`.

### Lean coded-induction bridge

`BoundedPAConsistency.Internal` reuses Foundation's nonstandard-model coding
of syntax and least-fixed-point derivations.  Its `inductionAtHierarchy`
generalizes the library's coded fixed-point induction from a hard-coded
level-one invariant to an invariant at any externally fixed positive
arithmetical-hierarchy level, assuming the matching induction fragment.
`inductionInPeanoModel` discharges that fragment in an arbitrary model of full
PA.  The fixed-level development uses this infrastructure to push its
partial-truth invariant through coded derivations; the bridge itself is not a
truth predicate or reflection theorem.

`BoundedPAConsistency.ModelFormulaInduction` specializes the same bridge to
Foundation's formula-code fixed point and exposes all eight syntax cases.  It
allows fixed higher-level invariants to be proved for every internally
well-formed formula code, including nonstandard codes, without host-language
decoding.

Rocq/Coq reaches the same arbitrary-model boundary through explicit
beta-supported raw syntax, rank, assignment, truth, and proof traversals rather
than through Lean's fixed-point derivation library.

### Lean coded-term evaluation

`BoundedPAConsistency.TermEvaluation` evaluates Foundation codes of
arithmetic terms under HFS-coded bound- and free-variable environments.  It
uses Foundation's term recursor, so its value and vector-value graphs are
Sigma-one represented functions in every model of `I Sigma 1`, including on
nonstandard term codes.  The checked equations cover de Bruijn and free
variables, binder extension, argument vectors, and the arithmetic constants,
addition, and multiplication.  This is the term-semantic input to partial
truth; it does not yet evaluate formula codes.

`BoundedPAConsistency.TermEvaluationTransport` proves, by internal structural
induction rather than decoding, that evaluation commutes with coded
free-variable shift and simultaneous bound-variable substitution.  It also
constructs genuine HFS fresh-head and reversed de Bruijn substitution
environments.  The results therefore apply to nonstandard term codes in every
model of `I Sigma 1`.

### Lean coded hierarchy and restricted proof sentence

`BoundedPAConsistency.CodedHierarchy` uses Foundation's formula fixed-point
recursor to compute the pair of `Sigma`- and `Pi`-oriented ranks on actual
formula codes.  Its graph is Sigma-one represented and its
`QuantifierBoundedCode` predicate has a dual Sigma/Pi Delta-one presentation.
The constructor equations, negation swap, and invariance under shift and term
substitution are proved by internal structural induction, so they cover
nonstandard codes in arbitrary models of `I Sigma 1`.  The module also proves
exact agreement with its external rank on standard quoted NNF formulae.

`BoundedPAConsistency.OrientedHierarchy` resolves the minimum-based bound
into separate internal `IsSigmaCode` and `IsPiCode` domains.  It proves the
Boolean and quantifier constructor inversions, polarity exchange under coded
negation, monotonicity, and shift/substitution/free-opening transport needed
by an externally recursive partial-truth family.  These results also range
over arbitrary nonstandard codes and model bounds.

`BoundedPAConsistency.RestrictedDerivation` conjoins that bound with every
node of Foundation's coded derivation fixed point.  Its erasure theorem is an
internal induction over the fixed point, not a decoder argument on standard
naturals.  `BoundedPAConsistency.RestrictedConsistency` packages the result as
a Delta-one restricted-proof predicate, Sigma-one restricted provability,
and a Pi-one sentence `paRestrictedConsistencySentence n` for each external
Lean natural number `n`.  Evaluation of that sentence in every arithmetic
model is proved equivalent to absence of all model-internal restricted proof
codes.  Every externally fixed instance of this exact target is now proved in
PA by `FixedLevelPAAxioms.pa_proves_restrictedConsistency`.

### Lean rank-zero partial truth

`BoundedPAConsistency.QuantifierFreeTruth` is the base case of partial
satisfaction.  It evaluates nonstandard coded arithmetic atoms and Boolean
combinations using a represented finite HFS certificate, supplies exact
positive and negative equality/order clauses, conjunction/disjunction
clauses, Boolean-valuedness, and complementary truth/falsity predicates on
the Delta-one level-zero domain.  Quantifier constructors are deliberately
totalized to zero and carry no semantic claim.

`BoundedPAConsistency.QuantifierFreeTarski` proves internally that level zero
forces *both* polarity ranks to vanish, a fact not immediate from the
minimum-based definition on nonstandard codes.  It derives exact domain
inversion at conjunction/disjunction, exclusion of quantifier constructors,
and positive/negative Tarski clauses for arithmetic atoms and Boolean
connectives.  `BoundedPAConsistency.QuantifierFreeTransport` proves formula
evaluation invariant under coded free-variable shift and simultaneous term
substitution, and complementary under coded negation, for arbitrary model
elements satisfying the internal syntax predicates.

`BoundedPAConsistency.QuantifierFreeSoundness` then performs internal
fixed-point induction over arbitrary rank-zero restricted derivations.  It
checks the initial, Boolean, weakening, shift, cut, and axiom rules; the
quantifier rules are excluded by the rank-zero domain theorem.  The result is
parameterized by one deliberately explicit theory premise saying that every
internally recognized rank-zero axiom is rank-zero true.  Thus the logical
soundness layer is complete at level zero.

`BoundedPAConsistency.QuantifierFreePAAxioms` discharges that final premise
for the repository's actual Delta-one PA recognizer.  Its finite PA-minus
branch is shown to contain only standard quoted axioms, whose surviving
rank-zero cases evaluate true.  The possibly nonstandard induction branch is
excluded structurally because every recognized induction formula contains a
genuine universal quantifier.  Completeness then turns arbitrary-model
rank-zero consistency into the audited object theorem

```lean
theorem pa_proves_restrictedConsistency_zero :
    Peano ⊢ (paRestrictedConsistencySentence 0 : ArithmeticSentence)
```

### Lean fixed-level partial truth

`BoundedPAConsistency.FixedLevelTruth` defines an externally indexed family
`SigmaTrue n`/`PiTrue n` over arbitrary model elements.  Positive-level truth
uses internally finite HFS certificates rather than host-language recursion
on a formula code, so nonstandard codes are included.  Certificate records
traverse both children of conjunctions, choose one disjunct, store existential
witnesses, and stop at quantifier-free or lower opposite-polarity leaves.

`FixedLevelTruthCertificate` proves certificate enlargement and the positive
conjunction, disjunction, and existential Tarski clauses.
`FixedLevelTruthDefinability` represents `SigmaTrue n` by a `Sigma_(n+1)`
formula and `PiTrue n` by a `Pi_(n+1)` formula.
`FixedLevelTruthTarski` supplies the uniform Sigma clauses, their Pi Boolean
duals, Pi universal truth over every model element, and the two level-changing
universal/existential polarity clauses.  `OrientedHierarchy.rankCode_balanced`
proves internally that the two ranks differ by at most one, so every formula
with minimum rank at most `n` lies in either chosen polarity at level `n+1`.
`FixedLevelTruthCoherence` proves conservativity between adjacent levels and
agreement of Sigma/Pi truth wherever both oriented domains apply, using
model-internal structural induction for nonstandard codes.
`FixedLevelTruthSubstitution` proves free-variable shift and simultaneous
bound-variable substitution transport under nonstandard environments.
`FixedLevelTruthLaws` combines these results into ordinary complement,
Boolean, quantifier, opening, and substitution clauses for the unified
predicate `SigmaTrue (n+1)` on codes bounded by `n`.  Together with
`AbstractSoundness` and `FixedLevelSequentDefinability`, this proves the whole
logical calculus sound at every fixed external level once the recognized PA
axioms are shown true.  `FixedLevelPAMinusAxioms` proves term-quotation and
formula-quotation adequacy for every standard arithmetic formula within the
fixed coded bound, then uses standardness of the finite `PeanoMinus`
recognizer to show that all of its accepted axioms are `SigmaTrue (n+1)`.
`FixedLevelPAInductionAxioms` handles the recognizer's genuinely nonstandard
branch.  It proves the recovered induction body true, reverses arbitrary
model-coded bound assignments through `fvarVec`, transfers truth back to the
raw closure body, and performs represented induction over a possibly
nonstandard number of leading universal quantifiers.  Thus every bounded
`InductionUnivR` code is `SigmaTrue (n+1)`.  `FixedLevelPAAxioms` combines the
two recognizer branches, invokes fixed-level soundness for all nonstandard
restricted derivations, and applies arithmetic completeness.  Its headline
theorem is the externally indexed family

```lean
theorem pa_proves_restrictedConsistency (n : ℕ) :
    Peano ⊢ (paRestrictedConsistencySentence n : ArithmeticSentence)
```

The parameter remains metatheoretic; this is not a PA proof of one universal
closure over all levels.

### Rocq natural codes and executable checker

`CodedSyntax.v` gives canonical natural-number codes for the phase-one PA
terms and formulae, total fuelled decoders, round trips and injectivity, coded
renaming and instantiation, and exact agreement of the coded hierarchy rank
with the typed rank.  `CodedProof.v` gives an unindexed mirror of all 17 proof
rules, an executable endpoint checker, canonical proof codes and total
decoding, and exact preservation of `proofOccurrenceRank` when a typed
`ProvTree` is quoted.

`RawCodedProofConstructors.v` gives a separate, model-internal bridge for the
same syntax.  It writes the polynomial list code of each of the 17 proof
constructors as an ordinary PA term, combines them into one transparent local
constructor relation, and proves exact evaluation without assuming any
arithmetic laws.  In every raw PA model, recursively quoting a standard proof
tree through these terms agrees with the executable `rawProofCode`.  A global
proof traversal and rule validator for arbitrary nonstandard codes remains a
separate obligation.

`RawCodedProofDescent.v` establishes the order-theoretic fact needed by that
global traversal.  It proves inside arbitrary PA models that each coordinate
is below the polynomial pair code and hence that every member of a coded list
is strictly below the enclosing list node.  One transparent formula enumerates
the premise fields of all fourteen recursive proof constructors and has exact
raw semantics.  Consequently every locally recognized recursive premise code
is smaller than its parent, and raw-model completeness closes the uniform
descent assertion into `PA_proves_rawProofConstructorDescentFormula`.

`RawCodedProofTraversal.v` assembles those local constructors on an honest
nonstandard syntax domain.  A beta support table marks proof codes, every live
code exposes a constructor occurrence, and a universal local clause closes
every constructor tuple denoting that same code.  Consequently all recursive
premises are supported and strictly smaller, certificates restrict to child
proofs, and unrelated certificates close the same arithmetic occurrence.
The public realizability predicate hides the support parameters without
claiming that arbitrary carrier elements are proof codes.  Exact raw semantics
and raw-model completeness yield the object theorem
`PA_proves_proofSyntaxOccurrenceTotalityFormula`; inference-rule endpoint
validation and soundness remain the next layers.

The PA wrapper records explicit witnesses for the six fixed axiom schemes and
for induction instances.  Every phase-one restricted PA derivation has an
accepted code, and every accepted code erases to an ordinary PA derivation.
This is still a computation performed by Rocq on standard `nat` values.  The
checker has an extracted computability witness and a representing PA formula
whose correctness theorem is exact in the standard `nat` model.  It has not
been proved correct for nonstandard codes in arbitrary PA models; that
distinction is exactly the remaining internalization boundary.

There is an additional reason this particular representing formula is only a
checkpoint: the generic computability bridge selects, by classical choice,
an arbitrary formula with the right `natModel` extension.  That contract does
not determine its behavior in nonstandard models or provide a PA-provable
graph theorem.

`CanonicalCheckerTrace.v` removes that opacity.  It constructively extracts
the checker to a closed lambda term, compiles that term to a fixed nine-counter
Minsky program, and builds a fully transparent PA formula asserting the
existence of beta-coded initial, transition, final-state, and output traces.
Its arbitrary-raw-model theorem unfolds the outer certificate into the exact
finite list of trace conditions.  `CanonicalCheckerStandardAgreement.v`
uses deterministic machine semantics to prove, on ordinary naturals, that
the concrete machine accepts exactly when `checkRestrictedPAProofCode`
returns true.  The audits show that the compiler and standard-agreement
theorems are closed; only the generic environment extensionality lemma used
by the raw certificate shell assumes functional extensionality.  The missing
step is now mathematical rather than representational: prove in every raw PA
model that an accepting nonstandard trace would yield a sound bounded proof,
and hence cannot end in falsity.

`RawModelCompleteness.v` supplies the other endpoint: a sentence valid under
every valuation in every raw model of the PA axioms has an object-level
`Formula.BProv Formula.Ax_s []` proof.  This theorem is intentionally
conditional on arbitrary-model validity.  Combining it with the standard
checker-formula correctness theorem would be unsound; the missing fixed-level
partial-truth argument is precisely what must establish that validity for
nonstandard model elements.

`CanonicalCheckerRawReduction.v` fixes the hierarchy bound in the transparent
canonical trace formula, universally closes the candidate-certificate input,
and proves exact satisfaction in every raw arithmetic structure.  Combining
that semantics with raw-model completeness and soundness yields an iff: PA
proves this canonical fixed-bound sentence exactly when every raw PA model
rejects every (including nonstandard) accepting trace.  This is a reduction,
not a proof of rejection; its statement deliberately exposes the remaining
nonstandard soundness obligation.

`CanonicalCheckerRawTraceReflection.v` unfolds the finite transition
disjunction into an explicit raw-carrier Minsky step relation.  It proves
exact semantics for increment, decrement, program-counter, and unchanged
register conditions, and beta-decodes a related current/next state at every
model-internal index below the trace length.  Thus every complete canonical
graph witness contains an internally stepwise trace, even when its length is
nonstandard.

`CanonicalCheckerRawTraceCoherence.v` uses beta functionality in a raw PA
model to prove that all descriptions of one trace position agree on the
program counter and every one of the nine live registers.  Consecutive local
steps therefore share the same finite middle state.  From a single complete
graph witness it also reflects the exact initial checker state (including the
fixed bound and certificate inputs), the accepting output entry, and the
final program counter lying outside the compiled program.  PA's
zero-or-successor theorem obtains either the initial state at a zero-length
trace or the endpoint of the single preceding reflected step; beta
functionality then joins the output and program-counter entries into that one
genuine full final state.  This closes the local coherence and boundary
bookkeeping without externally iterating across a possibly nonstandard trace
length.

`CanonicalCheckerDefinableInvariant.v` supplies the missing internal
iteration principle.  It turns any fixed PA formula on the ten machine-state
components into a beta-trace point predicate, proves exact raw semantics, and
uses PA's own induction axiom to propagate that predicate to the model-valued
final time.  Its `RawCanonicalDefinableSafetyCertificate` isolates exactly
three checker-specific obligations: the invariant holds in the initial
bound/certificate state, every concrete compiled-program step preserves it,
and it excludes the accepting final state.  Such a certificate now implies
both rejection in every raw PA model and the existing object-level canonical
consistency theorem.  The remaining Rocq task is to construct and verify that
concrete safety invariant; the nonstandard-time induction mechanism itself is
complete.

`CanonicalCheckerConcreteInvariant.v` chooses the explicit formula saying
that a state outside the compiled program cannot have output register zero
equal to one.  Its raw semantic equivalence, canonical initial-state truth,
and contradiction with an accepting final state are fully proved.  Every
purported accepting trace is also shown to have nonzero length and a genuine
last transition whose current program counter names an instruction of the
concrete compiled program.  The remaining premise is named
`CanonicalCheckerNoAcceptingExitPreservation n`: the checker-specific theorem
that this formula survives every such step.  Conditional rejection and
object-level PA corollaries consume this premise, but it is deliberately a
`Prop` parameter to those theorems rather than an axiom or a completed proof.
Discharging it is exactly where the missing raw-model fixed-level partial
truth/compiler-soundness argument must enter.

`RawCodedSyntaxConstructors.v` starts that internal argument independently of
the compiled-machine presentation.  It writes the repository's actual
polynomial list node, term-code constructors, and formula-code constructors as
transparent PA terms and formulae, and proves their exact semantics in every
law-free raw arithmetic structure.  Standard quotation theorems then identify
the raw folds with `termCode` and `formulaCode`.  This matters because a graph
formula selected only from its standard-natural extension cannot justify a
recursive computation on a nonstandard code.

`RawCodedFormulaRankStep.v` combines those constructors with transparent
maximum and polarity-rank equations.  Each local row simultaneously recognizes
one of the seven formula constructors and computes its Sigma/Pi rank from
already certified child rows, including the two quantifier polarity switches.
These are exact arbitrary-model one-step laws; a later beta-coded postorder
traversal must still connect them into a total rank computation.

`RawCodedFormulaRankStepFunctionality.v` proves the arithmetic determinism of
those rows.  Antisymmetry makes the transparent maximum relation single-valued,
and consequently the implication, Boolean, universal, and existential
Sigma/Pi equations each return a unique rank pair for fixed child ranks.  The
same result is exposed at every constructor-wrapper relation used by a global
traversal.

`RawCodedSyntaxConstructorSeparation.v` proves the list-arity separation and
constructor consequences needed by that traversal, conditional on one sharply
named arithmetic obligation: an object-level PA derivation of injectivity for
the concrete polynomial pairing function.  The condition is a `Prop`
abbreviation, not an axiom or an admitted theorem.  Its audit therefore keeps
the remaining arithmetic proof boundary visible.

`PolynomialPairInjectivity.v` closes that boundary.  It places
`(a+b)^2+a` between the consecutive diagonal squares `(a+b)^2` and
`(a+b+1)^2`, proves that different diagonal sums give strictly ordered pair
codes in every raw PA model, and then uses additive cancellation on a common
diagonal.  Raw-model completeness converts this semantic argument into the
actual checked derivation `PA_proves_polynomialPairInjectiveFormula`.

`RawCodedAssignment.v` provides the environment interface needed by coded term
evaluation and quantified partial truth.  An assignment is a pair of
Goedel-beta parameters; lookup, defined-prefix, and prepend are genuine PA
formulae with exact raw-model semantics.  Beta functionality makes lookup
unique.  More importantly, the PAHF Chinese-remainder development yields an
object-level PA proof that prepending a binder value is possible through an
arbitrary model element, not merely through a standard numeral.  The module
proves the expected zero/successor lookup equations and transports prefix
definedness from `bound` to `succ bound`.

`RawCodedContextLists.v` gives proof contexts their own honest model-internal
list interface.  Synchronized beta tables follow successive canonical
polynomial tail codes from the public context code down to zero and record the
head formula at every live position.  The row, complete traversal, realizable
domain, indexed membership, and public membership predicates are all genuine
PA formulae with exact semantics in arbitrary raw arithmetic structures.  In
particular, later assumption and sequent clauses need not apply the external
list decoder to a possibly nonstandard context code.

`RawCodedFormulaRankTraversal.v` packages the seven local rank rows into three
synchronized beta tables: formula codes, Sigma ranks, and Pi ranks.  Child
rows must occur at strictly smaller indices, and the existentially closed root
graph is a genuine PA formula with exact semantics in every raw arithmetic
structure.  Prefix restriction exposes any earlier row as its own certificate.
Constructor injectivity and induction on an externally given formula prove
that every certificate rooted at a standard quotation returns exactly the
metatheoretic `sigmaRank` and `piRank`, so independent certificates agree on
standard codes.  The module deliberately names, but does not assume, the two
stronger obligations needed for arbitrary nonstandard roots: existence of a
traversal and agreement between different traversals.

`RawCodedFormulaRankRealization.v` discharges the latter obligation in full.
An actual PA formula expresses agreement below a model-valued traversal index;
its successor proof decodes the seven constructor shapes, restricts unrelated
certificates to matching child rows, and invokes the already functional local
rank equations.  PA induction therefore proves cross-certificate Sigma/Pi
agreement for every possibly nonstandard root.  Raw-model completeness turns
that semantic result into `PA_proves_codedFormulaRankFunctionalFormula`.  A
separate realizability formula honestly names the graph domain: malformed
carrier elements are not incorrectly claimed to possess a constructor row.

`RawCodedFormulaRankTotality.v` discharges the existence obligation on an
independently characterized domain.  A beta-coded postorder syntax traversal
allows arbitrary equality-term payloads and requires every recursive formula
child to occur at a strictly earlier row.  Its definitions are genuine PA
formulae with exact arbitrary-model semantics.  The construction derives a
single sufficiently large CRT step from PA's beta-coding theorem, maintains
the sharp row bound `sigma, pi <= S(index)`, and extends both rank tables by
PA-definable induction through the possibly nonstandard traversal bound.
Together with cross-certificate functionality this gives unique ranks, and
raw-model completeness closes the result into the checked object theorem
`PA_proves_codedWellFormedFormulaRankTotalFormula`.

`RawCodedTermEvaluationStep.v` connects that environment to the transparent
term constructors.  It defines exact local evaluator rows for variables, zero,
successor, addition, and multiplication.  Variable values come from the coded
assignment; recursive child values come from a separate beta-coded evaluation
table.  Both the witness-exposing rows and their four-witness existential
closure are genuine PA formulae with exact arbitrary-model semantics.  The
global theorem that constructs and validates a complete table over a possibly
nonstandard term code remains separate.

`RawCodedTermEvaluationStepFunctionality.v` proves that the unified row is
single-valued.  It first derives every cross-constructor disjointness fact from
list-arity separation and distinct standard tags.  For two rows of the same
constructor, list-node injectivity recovers identical child codes and beta
functionality recovers identical child values.  Consequently independently
chosen existential row witnesses cannot change the proposed term value.

`RawCodedTermEvaluationTraversal.v` packages those rows into transparent
support and value beta tables.  Every supported recursive child is explicitly
smaller than its parent and supported in the same certificate.  A PA-definable
prefix-agreement predicate compares two possibly nonstandard tables by PA's
own induction, proving their root values equal; raw-model completeness then
produces the checked theorem
`PA_proves_termEvaluationCertificateFunctionalFormula`.  The module also
isolates the CRT append capacity used by a later realization proof.  At this
layer, an arbitrary nonstandard well-formed term code still needs a
model-internal topological support trace from which the complete tables can be
constructed.

`RawCodedTermEvaluationRealization.v` supplies that topological interface and
the nonstandard construction itself.  A genuine PA formula describes a
supported term-syntax traversal and assignment adequacy; its raw semantics
requires recursive term children to be supported at smaller codes.  At each
successor stage a local value is computed, the old beta table is transported
through a CRT extension, and `raw_definable_induction` iterates this argument
through a possibly nonstandard bound.  The resulting certificate exists and
has a unique value provided one fixed beta step is a common multiple through
the traversal and every newly computed value fits its target modulus.  That
capacity condition is transparent and unassumed, and is kept separate so that
the source of the common-modulus obligation is explicit.

`RawCodedTermEvaluationCapacity.v` discharges that obligation internally.  A
PA-definable trace assigns each prefix a capacity that works parametrically
for every sufficiently large common beta step.  At a successor, a probe step
discovers the next value; cross-traversal functionality shows that all larger
steps discover the same value, and finite beta coding appends it.  PA induction
iterates this through an arbitrary model-valued bound.  Restricting one
complete traversal then bounds every admissible local output, yielding the
required fixed-step capacity and unconditional existence and uniqueness of
term-evaluation certificates for arbitrary nonstandard syntax codes.

`RawCodedTermEvaluationStandardAdequacy.v` separately realizes the global
certificate on every externally quoted typed term.  A checked decoder marks
canonical standard codes, finite beta coding constructs the assignment,
support, and value vectors, and structural term induction verifies every live
row.  A fixed-assignment interface can reuse one assignment pair across
independently generated term tables; in particular, the two sides of an
equality receive certificates over literally identical assignment parameters.
This independently checks standard-quotation adequacy; the preceding capacity
module supplies the stronger arbitrary-nonstandard realization theorem.

`RawCodedRankZeroTruthStep.v` supplies the next local Tarski layer.  Equality
rows read evaluated arithmetic values from a term table; Boolean rows read
child truth bits from a formula table and enforce the usual truth tables.
Falsity always returns zero, successful rows always return a zero/one bit, and
quantifier constructors have no rank-zero row.  The witness-exposing and
existentially closed forms again have exact semantics for arbitrary raw-model
elements and form the local interface consumed by the global traversal.

`RawCodedRankZeroTruthStepFunctionality.v` proves determinism of that local
truth evaluator.  PA distinguishes zero from one, making each explicit Boolean
truth table functional.  Formula-constructor tags recover identical child
codes, and beta functionality recovers identical term values or child truth
bits.  Thus two independently witnessed rows for the same code and tables
necessarily return the same truth bit.

`RawCodedRankZeroTruthTraversal.v` packages the local rows into synchronized
support and truth beta tables.  Equality atoms must supply two complete term
evaluation certificates over the same coded assignment; recursive Boolean
rows must support both children and place their codes strictly below the
parent.  A PA-definable prefix-agreement predicate and PA induction prove that
two arbitrary, possibly nonstandard traversals agree wherever both tables are
supported.  This yields unconditional root-output functionality and the
checked object theorem `PA_proves_rankZeroTruthCertificateFunctionalFormula`.
The module also isolates simultaneous CRT table extension and names the
remaining admissible-root totality obligation without assuming it.

`RawCodedRankZeroTruthRealization.v` carries out that nonstandard construction
on an independently arithmetized quantifier-free syntax domain.  The support
certificate requires every Boolean child to be supported at a strictly
smaller code and supplies term-syntax certificates for both operands of every
equality under one assignment.  Local truth rows are realized, preserved by
beta extension, and assembled through a possibly nonstandard bound by
`raw_definable_induction`.  Since every output is zero or one, PA's own
beta-coding theorem supplies a common truth-table step with sufficient
moduli.  Existence and uniqueness therefore remain conditional only on the
explicit `RawRankZeroAtomicTermCapacity`, which is precisely the outstanding
fixed-step capacity for evaluating the equality operands—not an assumed truth
table or an external decoder.

`RawCodedRankZeroTruthTotality.v` discharges that final condition by applying
the term-evaluation capacity theorem to each equality payload's independently
arithmetized term-syntax certificate.  It obtains unconditional existence and
uniqueness for every realizable model-internal rank-zero syntax code and coded
assignment.  The module also exposes a closed PA formula expressing this
totality, proves its exact arbitrary-model semantics and validity, and derives
the checked object theorem
`PA_proves_rankZeroTruthTotalityOnSyntaxFormula`.

`RawCodedRankZeroTruthStandardAdequacy.v` validates that global graph on every
externally typed quantifier-free formula.  A checked decoder and classical
zero/one semantic vector generate finite support and truth tables, while the
fixed-assignment term interface ensures that both operands of every equality
use the same environment.  The resulting certificate output is uniquely one
iff raw satisfaction holds and uniquely zero iff it fails.  This theorem is a
standard-quotation realization audit, not a substitute for nonstandard-root
totality.

`RawCodedFixedLevelTruth.v` defines the next, externally indexed local layer.
Sigma evidence denotes truth and Pi evidence denotes falsity; synchronized
state tables carry polarity, formula code, and both coded-assignment
parameters.  The successor rows implement every Boolean constructor and the
preferred existential/universal clauses through strictly earlier states.  For
the polarity-switching clauses, a scoped counterexample formula quantifies a
binder value and a freshly prepended assignment, then recursively evaluates
the quantified child at the preceding external level.  Mutual recursion gives
exact raw semantics for these genuine PA formulae.  This module intentionally
claims only local rows and their introduction/domain laws: assembling a
globally closed table and proving semantic soundness remain separate steps.

`RawCodedContextBounds.v` turns the polarity domains into the actual
all-occurrences restriction on a proof-node context.  At a fixed external
level, every value read from every live head slot of one complete context
traversal must lie in either the Sigma or the Pi domain.  The table-relative
and existentially closed forms have exact arbitrary-model semantics, share
the terminating traversal with the head condition, and therefore do not
accept a malformed context vacuously.  A shared-table membership lemma exposes
the boundedness of each indexed assumption.

`RawCodedContextStructure.v` proves that this context representation supports
the structural operations used by natural deduction even at nonstandard
lengths.  A complete spine defines its terminal tail slot; two applications
of PA's beta-prepend theorem then add the new public list node and head formula
without external recursion.  Empty and cons contexts are realizable, the new
head and every old member belong to the extended context, and all-occurrences
boundedness is preserved by adjoining a bounded formula.

`CodedCheckerRawReduction.v` makes this boundary exact.  It proves the chosen
checker assertion is a sentence, unfolds its semantics in every raw PA model,
and shows that its object-level PA provability is equivalent to rejection of
the graph formula at every (including nonstandard) model element.  It does not
assert that rejection; the opaque formula's standard-model specification is
insufficient to prove it.

## The standard partial-truth argument

For each fixed external `n`, the full proof should implement the classical
partial-truth argument as follows.

1. **Code the hierarchy.**  Define delta-zero/primitive-recursive predicates
   `IsSigma(n, p)` and `IsPi(n, p)` on formula codes.  Prove constructor,
   inversion, negation, substitution, shift, and monotonicity lemmas, as well
   as correctness on quotations of standard formulae.
2. **Restrict derivations structurally.**  Arithmetize a derivation predicate
   whose recursive clauses require the hierarchy bound at every node.  This
   must include formulae introduced only in premises or as cut formulae.
3. **Evaluate coded terms.**  Define the value of a coded arithmetic term under
   coded bound- and free-variable environments.  Prove totality,
   functionality, and compatibility with weakening and substitution in PA.
4. **Construct partial satisfaction.**  For the fixed `n`, define dual
   satisfaction predicates for `Sigma_n` and `Pi_n` codes.  Establish the
   Tarski clauses for atoms, Boolean connectives, bounded quantifiers, and each
   permitted unbounded quantifier block.  Prove that the two predicates are
   complementary under coded negation.
5. **Verify the logical rules.**  Induct internally on the restricted
   derivation code and prove that every derived sequent contains a partially
   true formula.  The induction predicate has a fixed finite hierarchy level,
   so full PA supplies the required induction for each external `n`.
6. **Verify PA axioms.**  The finitely many non-induction axioms are immediate.
   An induction axiom is true because PA induction applies to the formula
   saying that its coded body is partially satisfied.  This step must also
   handle nonstandard pseudo-formulae accepted by PA's delta-one axiom
   recognizer in a nonstandard model; correctness merely for standard quoted
   axioms is insufficient.
7. **Exclude the false sequent.**  The compositional falsity clause shows that
   a restricted derivation whose final sequent is the singleton containing
   falsity cannot exist.  Package this statement as the arithmetic sentence
   `Con_n(PA)` and construct its PA proof.

One viable Lean endpoint is model-theoretic: prove `Con_n(PA)` in every model
of PA, including nonstandard models, and apply the foundation library's
first-order completeness theorem.  A direct syntactic PA derivation is equally
acceptable but does not remove the need to reason about arbitrary coded
derivations inside PA.

## Gödel-II boundary

The target does not contradict Gödel's second incompleteness theorem.

- Each standard `n` is fixed outside PA, and its partial truth predicate is a
  separate finite construction.
- No one of the sentences `Con_n(PA)` rules out PA proofs using formulae of
  greater complexity.
- There is no claim that PA proves the universal closure over all `n`.

With the intended coding, PA can verify that any alleged proof code has some
formula-complexity bound.  Therefore a single PA proof of
`forall n, Con_n(PA)` would yield ordinary `Con(PA)`.  Likewise, a purported
uniform truth predicate covering all levels would cross Tarski's
undefinability boundary.  The numeralwise family avoids both uniformizations.

## Internal provability of the bounded-consistency instances

The sentence

```text
forall n, Prov_PA(code(Con_n(PA)))
```

is different from the forbidden universal consistency statement above.  Its
inner assertion is PA's represented proof predicate, so it asks PA to verify
that a proof code exists; it does not reflect that proof back to
`Con_n(PA)`.  The outer quantifier is nevertheless an object-language
quantifier and therefore includes nonstandard levels in nonstandard models.

`BoundedPAConsistency.UniformInternalProvability` defines this literal Lean
sentence using Foundation's numeral-substitution graph `ssnum` and represented
predicate `provable Peano`.  It proves exact arbitrary-model semantics, exact
agreement with `paRestrictedConsistencySentence n` at every standard numeral,
and the externally indexed D1 consequence

```lean
theorem provable_paRestrictedConsistency_standard_point (n : Nat) :
    Provable Peano
      (substNumeral (quote paRestrictedConsistencyTemplate) (numeral n))
```

The module also isolates the strictly stronger obligation as
`PARestrictedConsistencyProofSelectorInAllModels` and proves that it is
equivalent, by soundness and completeness, to the requested one-sentence PA
derivation.  This selector must provide proof certificates for arbitrary
model elements, not only for standard numerals; an externally recursive
semantic-completeness proof does not construct it.

### The Lean selector, and the resulting object theorem

The selector is now constructed, so the uniform sentence is an unconditional
Lean theorem.  The construction is a *dynamic truth-certificate family*
indexed by the ambient model rather than by an external natural number.  At
each index the six-field master certificate records the local Tarski bundle,
cross-level coherence, shift invariance, substitution invariance, PA-axiom
soundness, and — forced into the last coordinate, so that no easier conclusion
can be certified — the corresponding bounded-consistency instance.

Three facts about that family are proved:

- its master code has a `Sigma`-one graph
  (`compiledDynamicTruthCertificateFamily_code_definable`);
- index zero carries a genuine typed PA derivation of the master certificate
  (`compiledDynamicTruthBaseCertificateProof`);
- every index carries a dependency-ordered successor step whose public target
  is the family's next master certificate
  (`compiledDynamicTruthCertificateFamily_hasStagedSuccessor`).

`Sigma`-one induction *inside* an arbitrary model of PA then yields a proof
code at every element, nonstandard ones included, and the forced sixth
coordinate converts each such code into a proof code for the matching
restricted-consistency instance.  That is the selector, and arithmetic
completeness returns

```lean
theorem pa_proves_uniformRestrictedConsistencyProvability :
    Peano ⊢ paUniformRestrictedConsistencyProvabilitySentence
```

in `BoundedPAConsistency.UniformInternalProvabilityTheorem`, audited to depend
on exactly `[propext, Classical.choice, Quot.sound]`.  No recursion on
external natural numbers occurs anywhere in this chain; that is precisely what
separates the single sentence from the numeralwise schema.

Two structural facts shaped the construction and are worth recording.  First,
the successor step is *not* uniform in the index.  The represented
derived-level sources identify `numeral (x + 1)` with `numeral x + 1`, which
holds internally only for `0 < x` — internally `numeral 1` is the one-symbol
code while `numeral 0 + 1` is a sum code — so the cross-level and
axiom-soundness slots need separate productions out of index zero, where all
syntax is standard and the field is obtained by ordinary completeness plus D1
transport.  The axiom-soundness slot additionally needs the split because the
semantic laws package requires existential laws for the *lower* orbit member,
which are available only at positive members.  Second, the staged compiler
states each slot's context through the closures of the preceding kernels while
each production states its kernel through the corresponding orbit field.
These agree definitionally, but confirming that by unification inside a
structure literal is not feasible on represented-syntax terms; the assembly
therefore transports kernels along proved context equations
(`PAInductionKernel.ofEq`) so every rewrite stays an equation between named
formulas.

### Rocq/Coq status: conditional, with the constructive boundary named

The Rocq modules `RawCodedPAProvability.v`,
`RawCodedPAProvabilityRestrictedConsistency.v`,
`RawCodedPAUniformProvability.v`, and `CompactPAUniformProvability.v` provide
the parallel transparent proof predicate, the fixed-standard-instance D1
theorem, and the exact uniform target
`compactUniformRestrictedPAConsistencyProvabilityFormula`.  The object-level
derivation of that sentence is **not** established.  The older files expose a
formally valid implication from
`RawCodedPALocalProofConsTransplantInAllModels` and
`RawRestrictedPADynamicSoundnessBaseProofInAllModels`, but those two premises
are now retained as historical reduction seams rather than advertised as
constructive endpoints.  Neither is an axiom or an admitted theorem, and
neither has been proved.

The unrestricted transplant quantifies over an arbitrary carrier value as the
new assumption.  That is too broad for this encoding: All-I and Ex-E shift the
whole context below a binder, while `RawCodedFormulaShift` is deliberately
partial on malformed carrier values.  `RawCodedPALocalProofContextInsertInduction.v`
therefore states the honest invariant with
`RawCodedFormulaAtomicallyAdequate` as a guard, represents the complete
below-proof-code predicate by a PA formula, and performs the strong induction
inside every raw PA model.  The arbitrary-depth assumption-leaf case is
proved.  `RawCodedContextInsertShiftCommutation.v` now proves the full binder
commuting square by another represented induction over the carrier-valued
depth.  `RawCodedPALocalProofContextInsertRootStep.v` then rebuilds all
seventeen rules, using the dedicated Or-I1, Or-I2, Or-E, Ex-I, Eq-Refl, and
Eq-Elim coverage constructors alongside the older generic infrastructure.
Imp-I and both Or-E branches increment insertion depth; All-I shifts the
inserted formula at the same depth; Ex-E first performs that shift and then
increments depth for its body premise.

`RawCodedFormulaOperationTraceConcatenation.v` closes the last generic input
to this guarded transplant route.  A PA-definable copy-state induction
concatenates the synchronized source/target/depth tables of two nonstandard
binary child traces, offsets every edge in the copied trace while retaining
the first root, and appends binary or quantified parent rows.  This proves
`RawCodedFormulaShiftCompositional` in every raw PA model.  Together with
`RawCodedFormulaShiftTotality.v`, arbitrary adequate formula unit shifts no
longer depend on a trace-splicing callback.

`RawCodedPALocalProofContextInsertUnconditional.v` instantiates the complete
seventeen-rule proof induction with that theorem.  Adequate unit formula
shifts, arbitrary carrier-depth context insertion, and the guarded
single-cons transplant are therefore unconditional in every raw PA model.

`RawCodedPALocalProofPropositionalRules.v` exposes implication introduction
and both disjunction introductions and elimination directly at the
`RawCodedPALocalProofOf` interface.  These rules retain arbitrary carrier-
coded contexts literally, including the two distinct cons contexts required
by disjunction elimination.  They let the dynamic successor compiler perform
case analysis over nonstandard formula codes without routing a purely
propositional tree through formula shift or opening infrastructure.

`RawCodedPALocalProofFiniteDisjunction.v` builds that case analysis for an
arbitrary metatheoretic finite list of carrier formula codes.  It represents
the empty disjunction by bottom, preserves a singleton literally, and folds
longer rows into a genuine right-associated Or tree, so the native six- and
seven-branch rows acquire no artificial trailing case.  Every assumption
leaf is certified against its exact carrier-coded context, and the exported
closed rule and open elimination rule require neither decoding nor an
adequacy premise on the branch codes.

`RawCodedPALocalProofFiniteDisjunctionDerivedCases.v` applies those finite
case trees when the row and every branch implication have already been
derived in one arbitrary carrier-coded context.  Each Or-E child is rebuilt
by the guarded cons-transplant theorem.  The recursive resource predicate
therefore requests realizability of the original context and atomic adequacy
of exactly the branch and suffix-disjunction codes that become new context
heads; empty and singleton rows require no such resources.  Generic and
literal six-/seven-way endpoints preserve the original context and avoid any
decoder or unrestricted weakening principle.

`RawCodedPALocalProofFiniteDisjunctionMatrix.v` nests that eliminator for two
rows already proved in one carrier-coded context.  Given a local proof of
every curried pair implication `Ai -> Bj -> C`, it derives `C` from the two
right-associated rows without decoding either row.  The resource predicate
is shape-sensitive: empty dimensions use bottom elimination, the one-by-one
case uses two direct implication eliminations, and every larger matrix tracks
only the context realizability and atomic adequacy needed by the guarded
temporary-assumption transplants.  Its concrete seven-by-six endpoint is the
structural assembler for the native Sigma/Pi successor collision matrix; the
individual constructor-pair proofs remain explicit inputs.

`RawCodedPALocalProofTripleUniversalElimination.v` packages the matching
three-binder consumer.  Three explicit represented substitution traces build
three checked All-E nodes without decoding the intermediate formula codes or
changing the carrier-coded proof context.  Companion endpoints first project
either conjunct and then specialize it, so a current local
decision/exclusivity certificate can be instantiated at one concrete formula
and assignment triple while all later matrix proofs remain in the same
witnessed PA context.

`RawCodedAssignmentShiftTail.v` also exposes PAHF's represented beta-tail
shift through the raw assignment interface.  It constructs, inside every raw
model and through an arbitrary carrier-valued bound, a target table whose row
`k` is the source table's row `k + 1`.  This is the table operation needed to
compare context traversals after descending through a binder; it does not
decode a nonstandard context in Rocq.

The pre-existing fixed dynamic-soundness source is now exposed through
`RawCodedRestrictedPADynamicSoundnessFormulaGraph.v` as an output-first field
graph.  It internally chooses a numeral-term code for an arbitrary model
element and performs represented substitution into the fixed source; the
explicit substitution tree proves graph totality with the intended
six-premise implication code as a witness.  This graph is reusable by a
concrete master family, although it is not by itself the five-field
Lean-style successor package.

`RawCodedDynamicLocalFieldGraph.v` supplies the exact model-indexed splice
needed by the first Lean-style field: a fixed zero graph is selected at zero,
while every successor exposes its predecessor and evaluates a positive-orbit
graph there.  The de Bruijn remapping, arbitrary-model totality reduction,
and exact zero/successor views are complete.  Its honest concrete inputs are
still missing: model-coded truth-formula output graphs and code graphs for the
four augmented-local laws.  The existing fixed-level Coq syntax is indexed by
external `nat`, so it cannot be substituted for those nonstandard graphs.

`RawCodedStandardClosedFormulaCodeGraph.v` discharges the generic fixed-base
half of such splices.  Any external formula has a canonical output-first graph
for its exact internal quotation, with law-free numeral totality, PA-model
quoted-code semantics, the base-totality interface above, and a convenience
bridge from a standard closed `BProv` derivation to a graph-selected raw proof
certificate.

`RawCodedOutputFirstFormulaGraphCombinators.v` closes the corresponding
constructor layer.  Given total output-first child graphs, it builds total
output-first graphs for implication, conjunction, disjunction, universal
quantification, and existential quantification.  Explicit de Bruijn maps keep
each child at the common model-coded level and tail environment, while exact
arbitrary-model semantics identify the selected output with the appropriate
raw formula constructor code.  These combinators let the remaining dynamic
fields be assembled structurally without decoding nonstandard syntax in Coq.

`RawCodedOutputFirstFormulaNegationGraph.v` adds the constant bottom graph and
the derived negation graph needed by the truth successor.  It forwards a
possibly nonstandard child code through an explicit binder renaming and then
selects the transparent implication-to-bottom code.  Exact semantics and
totality are law-free and introduce no well-formedness or standardness side
condition on that child.

`RawCodedNumeralTermCodeOutputFirstGraph.v` exposes the existing nonstandard
numeral-term beta trace in the common `output :: input :: tail` convention.
Its representation theorem is exact in arbitrary raw structures, PA proves
totality for every carrier input, and the zero and successor lemmas provide
canonical base output and existential orbit closure without rebuilding the
underlying trace.

`RawCodedDynamicTruthTernaryApplicationGraph.v` represents the recurring
application of a carried ternary truth-formula code beneath five binders.  Its
three checked single-substitution steps use variable codes `#6`, `#4`, and
`#0`; on ternary-scoped standard syntax their composite is proved literally
equal to the intended `[#4,#3,#0]` renaming.  The graph has exact law-free
carrier semantics and standard PA-model witnesses.  Totality for an arbitrary
nonstandard input remains dependent on the separate internally adequate
single-substitution totality construction.

`RawCodedDynamicTruthTernaryApplicationTotality.v` now connects that graph to
the completed substitution construction.  The fixed replacement codes `#6`,
`#4`, and `#0` receive internal term-syntax certificates from the universally
defined zero assignment; three represented substitutions then produce two
adequate intermediate codes and an adequate final output.  Consequently the
actual output-first application graph is total on every atomically adequate,
possibly nonstandard input formula code in an arbitrary PA model.

`RawCodedFormulaSingleSubstitutionTotality.v` supplies the formula half of
that construction.  It composes substitution traces at all binary and unary
syntax constructors, runs PA-definable induction over the carrier-valued code
bound, and obtains a substitution output for every atomically adequate
possibly nonstandard formula code and syntax-realizable replacement.  Its
only explicit lower-level premise is total represented term opening on an
internally syntax-realizable input; that exact term operation is isolated for
the next construction rather than hidden behind a standard quotation.

`RawCodedTermOpeningTotality.v` now discharges that premise.  It first copies
and offsets arbitrary represented opening traces so independently built child
traces can be concatenated, then performs a second PA-definable induction over
the internal term-syntax support.  The resulting theorem opens every
syntax-realizable possibly nonstandard term code at an arbitrary carrier
cutoff with an arbitrary lifted replacement.  The discharge module packages
this as `RawCodedTermOpeningTotal` and makes adequate formula substitution
existence unconditional in every raw PA model.

`RawCodedFormulaSingleSubstitutionAtomicAdequacy.v` proves that such a target
remains in the same honest atomic-adequacy domain.  It inverts equality rows
inside an arbitrary nonstandard operation trace, excludes every other syntax
constructor by code separation, and transfers term-syntax certificates to
both target equality fields.  Consequently three substitutions can be
chained with adequate intermediate outputs.  The only remaining preservation
premise is the exact term-level statement that represented opening after the
replacement shift produces a syntax-realizable term under the target table.

`RawCodedTermOpeningAfterShiftSyntaxStability.v` discharges that preservation
premise without restricting the opened term to a standard quotation.  It
constructs a PA-definable merged support table containing both the target
trace occurrences and the guarded support of the shifted replacement; the
guard is essential because a represented operation trace may contain rows
disconnected from its selected root.  Thus opening after shift preserves
syntax realizability in every raw PA model, and the exact three-substitution
chain now has unconditional totality and adequate intermediate outputs on
possibly nonstandard formula codes.

`RawCodedDynamicTruthFixedSyntaxFragments.v` supplies the fixed Coq-side
syntax used around the orbit.  Coq stores local truth states in four
synchronized beta tables rather than Lean's HFS record, so the module records
the semantic correspondence without asserting a false equality of concrete
codes.  It defines the ternary rank-zero truth base, carrier-term-indexed
Sigma/Pi domains, state membership, positive constructor branches, and the
universal leaf, with exact semantics, scoping, standard application, and an
output-first base-code graph.  In particular, its rank bounds remain
meaningful at nonstandard model levels.

`RawCodedDynamicTruthSigmaSuccessorRowGraph.v` constructs the positive half of
the native four-table successor.  Its output-first graph maps the preceding
Pi-falsity predicate code to the next Sigma-truth predicate code, represents
the eight-witness row and all positive constructor cases, and applies the
lower predicate through three checked substitutions.  The large fixed domain
template code is named opaquely only to keep kernel conversion bounded; exact
law-free semantics and standard quotation agreement remain explicit, and
nonstandard totality exposes the two genuine formula-operation inputs.

`RawCodedDynamicTruthPiSuccessorRowGraph.v` constructs the genuine negative
successor coordinate for that four-table certificate.  Its output-first graph
maps the preceding Sigma-truth formula code to the next Pi-falsity formula
code, represents all six native Pi branches, and applies the lower predicate
through three checked substitutions beneath the row binders.  Exact semantics
is law-free at carrier-valued levels; the totality theorem exposes the domain
substitution and lower-Sigma application operations explicitly instead of
using a dummy polarity or default code.

`RawCodedCarrierIndexedCodeOrbitGraph.v` supplies the model-internal recursion
engine for those fields.  A three-witness Goedel-beta table starts from an
arbitrary output-first base graph and checks a represented successor graph at
every adjacent pair through a carrier-valued bound.  Explicit row append,
prefix preservation, and lookup functionality prove the exact zero and
successor equations.  PA-definable induction then proves graph totality at
every model element, including nonstandard indices; all fixed parameters are
forwarded unchanged in the graph's tail environment.

`RawCodedCarrierIndexedPairedCodeOrbitGraph.v` lifts that recursion engine to
two visible coordinates, as required by Coq's mutually polarized Sigma-truth
and Pi-falsity hierarchy.  The implementation stores each adjacent pair with
the transparent polynomial pair term but performs PA induction on the public
two-coordinate invariant; this avoids the invalid assumption that the
injective pairing polynomial is surjective on a nonstandard model.  Exact
base and successor views, totality, and arbitrary carrier-level existence are
all exposed in the public output convention `first :: second :: level ::
tail`.

`RawCodedDynamicTruthPairedSuccessorRowGraph.v` combines the two polarity
transformers in the paired-orbit convention.  Its explicit de Bruijn
projections send `previousPi` only to the Sigma row and `previousSigma` only
to the Pi row, while forwarding the common lower level and tail unchanged.
The exact law-free relation therefore retains both cross-dependencies, and
paired totality follows from precisely the four visible domain-substitution
and lower-application interfaces of the component graphs.

`RawCodedCarrierIndexedPairedAdequateCodeOrbitGraph.v` strengthens the same
unchanged public graph with the invariant actually needed for represented
formula substitution.  Its base produces two atomically adequate codes, and
its successor is required only on the adequate coordinate pairs reachable
from that base while returning adequate next codes.  Both adequacy assertions
are part of the PA-definable existential induction formula, so the resulting
totality theorem retains them at arbitrary nonstandard carrier levels without
inventing a fallback result for malformed inputs.

`RawCodedDynamicTruthPairedSuccessorAdequacy.v` discharges that strengthened
successor interface.  It proves PA-internal identity shifts by zero and uses
them to derive constructor closure of atomic adequacy without decoding a
nonstandard formula code.  Represented successor-numeral substitution and
both three-step lower-polarity applications preserve adequacy; the transparent
Sigma/Pi row assemblers do as well.  Hence every adequate preceding pair has
a checked adequate paired successor, with no operation premise left open.

`RawCodedDynamicTruthPairedBaseFormulaCodeGraph.v` supplies the exact seed for
the local-row iteration.  Its first coordinate is the ternary local
Sigma-zero predicate and its second coordinate is the distinct ternary local
Pi-zero predicate; both are selected by literal internal formula-code
numerals in the base environment.  The graph has law-free numeral semantics
and totality, agrees with structural formula quotation in every PA model, and
includes the scoped Pi-base application lemma needed by the represented
successor construction.  These two formulas still refer to the surrounding
four-table state and are not yet the globally closed ten-witness truth
certificates.

`RawCodedDynamicTruthPairedBaseAdequacy.v` proves the stronger base condition
used by the adequacy-preserving orbit.  In a PA model the two literal numeral
outputs are the structural quotations of the fixed Sigma and Pi predicates,
so the existing quotation construction supplies internal atomic-adequacy
certificates for both coordinates in the same checked base row.

`RawCodedDynamicTruthPairedFormulaCodeOrbitGraph.v` specializes the paired
recursion engine to that checked local base and the mutually polarized local
successor row.  It exposes exact output-first semantics and literal
zero/successor views for `sigmaCode :: piCode :: level :: tail`.
PA-definable induction yields adequate syntax-code witnesses at every carrier
level—including nonstandard levels—and the successor-adequacy construction
discharges its last explicit operation interface.  This is a genuine internal
orbit, but its positive iterates code eight-witness row predicates with free
table/state variables.  They are not the globally closed ten-witness truth
predicates and must not be wired directly into the five certificate fields.

`RawCodedDynamicTruthPolarityFormulaCodeGraphs.v` exposes ordinary
`output :: level :: tail` projections of that same local-row iteration.  The
Sigma projection explicitly swaps its hidden Pi witness back into the paired
order, while the Pi projection can use the existential body directly.  Both
have exact law-free semantics and zero/successor views, and both have
unconditional arbitrary-model totality with atomic adequacy of the selected
possibly nonstandard local-row code.  These projections are useful audits,
not the final truth-predicate graphs; the latter must project a paired orbit
whose base and successor have first been closed by the global four-table
wrapper.

`RawCodedOutputFirstFormulaGraphComposition.v` provides the generic one-step
plumbing needed for such wrappers and later field graphs.  It existentially
composes `intermediate :: level :: tail` with
`output :: intermediate :: level :: tail`, using explicit de Bruijn
renamings to expose `output :: level :: tail`.  Its exact semantics is
law-free, and its dependent totality theorem transports an arbitrary indexed
invariant from the source witness to the transformed output.

`RawCodedDynamicTruthPairedGlobalSuccessorGraph.v` now performs the missing
closure step directly.  It places both thirteen-slot local polarity rows
under one four-beta-table traversal, restricts every stored row to mode zero
or one, and selects the requested root polarity.  The ten existential table
witnesses are intentionally reordered so that each local row can be inserted
literally, without a carrier-code shift or metatheoretic decoding.  A
transparent constructor polynomial computes both resulting global formula
codes.  Exact graph semantics is law-free, while constructor closure turns
atomic adequacy of the local pair into atomic adequacy of the global pair.
The row-aligned rank-zero base is realized unconditionally in every PA model;
although its witness order differs syntactically from the older native
rank-zero certificates, explicit witness permutation proves the two
presentations semantically equivalent.

`RawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph.v` instantiates the
adequacy-preserving paired carrier recursion with that global base and global
successor.  Its public `globalSigmaCode :: globalPiCode :: level :: tail`
coordinates therefore code complete ternary traversal predicates rather than
free-table local rows.  Represented induction gives an atomically adequate
pair at every carrier element, including nonstandard levels, and the exposed
zero and successor views remain exact.

`RawCodedDynamicTruthGlobalPolarityFormulaCodeGraphs.v` provides the two
ordinary `output :: level :: tail` projections of the global orbit.  The
Sigma projection performs the explicit hidden-coordinate transposition and
the Pi projection hides Sigma directly.  Both projections have law-free
semantics, concrete zero/successor views, and unconditional adequate totality
at arbitrary carrier levels.  These are the closed truth-predicate graphs to
be consumed by the five certificate-field constructors; atomic adequacy alone
does not yet supply those proof certificates, so the final Coq endpoint
remains deliberately conditional.

The first proof-producing master-field slices are now explicit rather than
hidden behind that remaining condition.  At level zero,
`RawCodedDynamicTruthLocalDecisionExclusiveBase.v` quotes the native local
decision/exclusivity bundle, while
`RawCodedDynamicTruthTransportFieldBaseGraphs.v` quotes the native
cross-level, formula-shift, and single-substitution laws.  Every base graph
pins its output to the exact formula code accepted by a concrete
`RawCodedPAProofOf` certificate.
`RawCodedDynamicTruthAxiomSoundnessBaseGraph.v` supplies the fifth base
coordinate as the genuine first truth transition: every transparently
witnessed PA axiom in the level-zero admissible domain has a level-one Sigma
truth certificate under Coq's total zero beta assignment.  Its derivation
uses the unconditional nonstandard induction-axiom truth theorem, then quotes
the exact sentence into the standard zero graph; it is not a placeholder
tautology.  For the positive local field,
`RawCodedOutputFirstPairedFormulaGraphComposition.v` preserves the joint
Sigma/Pi orbit witness while composing a proof-producing transform, and
`RawCodedDynamicTruthLocalProofFieldGraph.v` specializes that construction
to the globally closed paired orbit.  The transform remains intentionally
parametric: compiling the carrier-coded positive law formula and its raw PA
proof is the next honest proof obligation, not a consequence of semantic
truth-code adequacy.

Positive fields cannot soundly be compiled by reserving a sentinel inside
ordinary PA syntax: a closed sentinel is itself a substitution instance of
other PA syntax, so replacing it by an arbitrary predicate or carrier
parameter would break the substitution equations used by quantifier and
equality rules.  `RawCodedTemplateSyntax.v` therefore supplies an honest
extended source language with named carrier parameters, opaque finite-arity
predicate applications, capture-avoiding renaming/substitution, an embedding
of ordinary PA syntax, and an unindexed tree for all seventeen natural-
deduction constructors.  `RawCodedTemplateProofCompiler.v` translates such a
fixed finite tree under an abstract model-coded specialization and builds
every raw proof node through the coverage-certified constructors.  Its public
result is an exact `RawCodedPALocalProofOf`; nonstandard predicate codes are
never decoded.  `RawCodedTemplateProofCompilerSelfShiftTail.v` generalizes
that compiler from the raw-zero context tail to an arbitrary realizable,
self-shifting carrier-coded tail.  All seventeen constructor cases are
rebuilt with their literal tail-based contexts; a witnessed PA-axiom context
supplies both tail hypotheses, including the binder-rule self-shift invariant.
`RawCodedTranslatedProofCompiler.v` provides the corresponding
homomorphic compiler for ordinary PA proof trees and will be used by the
lifted-PA axiom bridge.  `RawCodedTemplatePAEmbedding.v` makes that bridge
literal: it embeds all seventeen ordinary raw-proof constructors, proves
context/conclusion/validity preservation, and attaches the unchanged finite
list of witnessed ordinary PA axioms to the compiled template tree.  Opaque
template atoms therefore cannot leak into the PA axiom base.
`RawCodedPAAxiomWitnessPrefix.v` supplies the corresponding common-context
operation.  A finite metatheoretic batch of standard PA-axiom witnesses is
folded over arbitrary carrier-valued witness-list and context tails in
lockstep.  Iterated guarded cons transplant rebuilds an existing local proof
over that exact extended context, and the strongest endpoint returns the
extended witness traversal and proof root together.  Prefix concatenation
laws let independently selected finite axiom batches be accumulated without
decoding the nonstandard base.
`RawCodedTemplatePAEmbeddingSelfShiftTail.v` joins these two operations.  Any
fixed ordinary `BProv` theorem is converted to a finite raw proof tree,
compiled above the caller's witnessed PA context, and returned together with
the exact synchronized prefix of standard axiom witnesses used by that tree.
Agreement of the template translation with ordinary quotation proves literal
equality of the compiler's context and the extended witnessed context; no
post-hoc context identification or unrelated proof certificate is used.
`RawCodedFolTemplateProofCompiler.v` supplies the reusable source-side bridge
into this template language.  It structurally embeds the repository's generic
first-order formulas (equality plus one binary membership relation), proves
the required de Bruijn renaming, opening, and context-shift equations, and
compiles every constructor of `FirstOrder.Calculus.Prov` to an explicit finite
valid `TemplateRawProof`.  The structural compiler is constructive; its
optional semantic-completeness corollary separately exposes the classical
assumptions inherited from the generic first-order completeness theorem.  The
fixed opaque binary predicate is only a source-proof interface, not the still
missing arbitrary-carrier dynamic-truth soundness construction.
`RawCodedRestrictedTargetTemplateContext.v` connects the transparent
restricted-consistency syntax family to the same template language.  It
fills the family's distinguished restriction-level hole with an arbitrary
template term and proves that structural translation is exactly
`rawRestrictedTargetFormulaContextCode` at the translated term code.  Thus a
named carrier parameter yields the genuine nonstandard restricted-proof and
consistency shapes without decoding it as a host numeral.  A separate theorem
recovers ordinary context instantiation only for closed host terms, keeping
the arbitrary-carrier and standard-quotation boundaries distinct.
`RawCodedTemplateLogicalSchemas.v` records the small
finite source trees needed by the dynamic fields—conjunction projection and
introduction, existential projection, and universal specialization followed
by modus ponens—so their model-coded proofs do not rely on an unexposed
semantic-completeness step.  `RawCodedTemplateProjectionSchemas.v` extends
those atoms with transparent arbitrary conjunction selection/repacking,
witness-preserving existential towers, universal closure, and the exact
two-universal/five-existential projection used by the dynamic universal-leaf
law.  `RawCodedTemplateDisjunctionCaseSchemas.v` supplies the complementary
all-branch rule for a right-associated finite disjunction.  Its transparent
tree proves `(A1 or ... or Ak) -> (A1 -> C) -> ... -> (Ak -> C) -> C`, with
named seven- and six-branch wrappers matching the native Sigma and Pi rows.
This closes the structural case split without assuming that a represented
row is metatheoretically decidable; each branch-specific implication remains
an explicit input to the positive local compiler.
`RawCodedTemplateClosedProofCompilation.v` packages any closed compiled
template tree as an ordinary `RawCodedPAProofOf` with a literally empty
witnessed-axiom list, and exposes that exact universal-leaf certificate.
`RawCodedTemplateStructuralTranslation.v`
recurses over the honest syntax and grafts client-supplied operation trees at
opaque leaves, thereby realizing full represented shift and opening traces
without decoding a carrier formula.  Its companion PA-agreement module proves
that this structural interpretation is exactly ordinary quotation on the PA
fragment.  That finite-tree interface applies when an opaque leaf itself has
a metatheoretic finite decomposition.  For genuinely nonstandard opaque
formula codes, `RawCodedFormulaOperationCompositionality.v` generalizes trace
concatenation to arbitrary represented formula operations, while
`RawCodedTemplateDirectStructuralTranslation.v` assembles the finite
surrounding template directly from relational opaque shift/opening traces.
No nonstandard opaque leaf is decoded into a Coq inductive tree.
`RawCodedTemplateDirectStructuralPAAgreement.v` proves that this direct
translation still agrees with ordinary PA quotation on embedded PA syntax:
parameters and opaque leaves cannot occur there, so the existing transparent
constructor recursion applies unchanged.  The restricted-soundness adapter
`RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.v` then packages
two exact five-argument selectors, one for context truth and one for
conclusion truth, together with numeral-parameter term traces.  Predicate
names zero and one dispatch to those selectors only at the advertised arity;
every malformed arity and every unused name is represented by bottom.  This
is an abstract operation interface, not an existence or semantic-adequacy
claim for either truth selector.
`RawCodedTemplateNumeralParameters.v` separately builds exact term shift and
opening traces for named parameters represented by model-internal numeral
codes.  `RawCodedTemplateNumeralTermSyntax.v` uses the zero-shift instance of
those traces to place every interpreted template term, including renamed and
opened terms, in the honest syntax domain required by opaque selectors.
`RawCodedTemplateTernaryApplication.v` supplies the honest
five-trace application relation for a possibly nonstandard ternary formula,
proves totality and preservation of atomic adequacy on represented term
syntax, and names the exact shift/opening commuting diagrams required at an
opaque leaf.  `RawCodedTermOperationCrossTraceFunctionality.v` and
`RawCodedFormulaOperationCrossTraceFunctionality.v` prove that arbitrary
successful represented traces for the same operation inputs agree, and the
ternary specialization gives unique selector outputs on honest term syntax.
`RawCodedTermShiftProtection.v` and
`RawCodedTermOpeningShiftInterchange.v` establish the term-level protection
and opening/shift square over arbitrary carrier parameters.  The formula
square is proved by a seventeen-parameter represented invariant and
`raw_definable_induction` in
`RawCodedFormulaShiftSubstitutionInterchange{Invariant,Induction}.v`.
`RawCodedFormulaOperationConcreteLaws.v` packages the result as protective
stability and single-substitution interchange for `FormulaShift`.  These laws
solve the shift-operation side of an opaque application once the predicate is
deeply closed.  The legacy unguarded opening contract still permits an
arbitrary replacement carrier value, so its corresponding concrete law is
kept separate rather than inferred from atomic adequacy or honest-syntax deep
closure.

`RawCodedTernaryPredicateRootClosure.v` strengthens the standard scoped
substitution identity from numeral replacements to every honestly
represented, possibly nonstandard term.  Represented shift totality chooses
the unused lifted replacement; a structural diagonal trace then proves that
any quoted ternary-scoped formula is fixed by both the depth-three shift and
depth-three substitution operations.  Applying this interface to the exact
row-aligned global rank-zero quotations,
`RawCodedDynamicTruthGlobalBaseRootClosure.v` proves root closure for both
outputs of the paired global base graph.

`RawCodedDynamicTruthGlobalSuccessorRootClosure.v` proves the corresponding
constructor and wrapper preservation theorem without decoding either
possibly nonstandard local row.  The ten existential traversal witnesses and
five universal row witnesses move the two local leaves from the public root
cutoff three to cutoff eighteen.  Fixed standard wrapper leaves are closed at
their checked scopes, and the existing adequate successor graph supplies
atomic adequacy of the local rows.  The resulting relation-level theorem and
orbit callback therefore assume exactly that the actual local Sigma and Pi
rows are operationally fixed at cutoff eighteen.  This is a fixed-cutoff
successor result, not a promotion of root closure to every deeper cutoff; the
all-depth opaque-application obligation remains separate.

`RawCodedTernaryPredicateRootClosureFormula.v` now makes that carrier-level
root certificate an actual formula of PA, including the explicit lift across
the three binders used to recognize honestly represented replacement terms.
`RawCodedCarrierIndexedPairedRootClosedCodeOrbitGraph.v` uses this formula as
the invariant of `raw_definable_induction`, so a closure-preserving base and
successor select both orbit coordinates at every element of an arbitrary PA
model, including its nonstandard elements.  The dynamic specialization in
`RawCodedDynamicTruthPairedGlobalRootClosedFormulaCodeOrbitGraph.v` discharges
the concrete rank-zero base and retains the ordinary global orbit together
with both root certificates; its successor hypothesis is deliberately
guarded by closure of the actual predecessor pair.  This invariant still
means exactly unit shift at cutoff three and represented substitution at
depth three.  It is not the stronger all-cutoff property needed by the
opaque-leaf commuting diagrams, so no arbitrary-depth interchange theorem is
inferred from it.

`RawCodedDynamicTruthPairedGlobalRootClosedFormulaCodeOrbitBridge.v` connects
the concrete wrapper-preservation theorem to that represented invariant.  An
actual successor edge transports both predecessor root certificates, and the
cutoff-eighteen local-row callback supplies the guarded successor interface
expected by paired-orbit induction.  Consequently every carrier level has a
selected ordinary global Sigma/Pi orbit pair together with both cutoff-three
root certificates.  The bridge retains the local callback as a visible
premise and does not strengthen either fixed-cutoff certificate.

The stronger invariant is now represented separately in
`RawCodedTernaryPredicateDeepClosure.v`.  Its PA formula quantifies over every
carrier cutoff and amount for shifts and over every carrier depth and honestly
represented replacement for substitution, guarding both operations by the
cutoff bound three.  Exact raw semantics confirms that these are genuine
object-language quantifiers, so they include nonstandard parameters.  For a
standard ternary-scoped quotation, the module builds an identity term-shift
tree at an arbitrary carrier cutoff and lifts it structurally to a diagonal
formula trace; together with arbitrary-depth scoped substitution this proves
the full deep certificate.  A final bridge projects deep closure to the older
root certificate, while the converse is deliberately absent.
`RawCodedTernaryPredicateDeepClosureShiftInterchange.v` combines this
all-cutoff fixedness with the concrete `FormulaShift` laws.  Since ternary
application opens three arguments, the required predicate cutoff is exactly
three successors above the client cutoff; PA proves that this is at least
three even for a nonstandard client value.  The resulting theorem discharges
the complete unguarded ternary shift-interchange contract.

The parallel opening algebra is now discharged by
`RawCodedTermShiftAmountComposition.v`, the term-opening protection,
opening/opening interchange and lift-cancellation modules, and the
represented seventeen-parameter formula induction in
`RawCodedFormulaSubstitutionAtomSubstitutionInterchange{Invariant,Induction}.v`.
`RawCodedFormulaSubstitutionAtomConcreteLaws.v` packages the resulting
protective and single-substitution laws.  The legacy opening relation is
sound even though it displays an arbitrary carrier replacement: any incoming
substitution atom itself recovers represented source syntax, so malformed
values cannot satisfy its antecedent.
`RawCodedTernaryPredicateDeepClosureOpeningCommuting.v` therefore proves both
the unguarded relation-level opening interchange and the exact honest-domain
selector law from PA satisfaction and deep closure alone.  No outstanding
opening-commutation premise remains.

`RawCodedCarrierIndexedPairedDeepClosedCodeOrbitGraph.v` uses the represented
deep formula, rather than the fixed root formula, as a paired orbit invariant
and proves its all-carrier totality by `raw_definable_induction`.
`RawCodedDynamicTruthGlobalSuccessorDeepClosure.v` proves every transparent
global wrapper constructor and its five-, seven-, and ten-node folds preserve
arbitrary-cutoff closure.  Atomic adequacy of actual local rows comes from the
successor relation itself; the remaining callback asks only that those two
rows are operationally fixed for every shift cutoff/amount and substitution
depth at least eighteen.  The dynamic specialization discharges the quoted
rank-zero base unconditionally and carries both deep certificates through the
ordinary global orbit at every, including nonstandard, hierarchy level under
that explicit local-row premise.

`RawCodedDynamicTruthSuccessorDomainDeepClosure.v` handles the first opaque
piece of each genuine local row.  It proves that substituting an honestly
represented, possibly nonstandard numeral into either fixed successor-domain
template is invariant under every shift and substitution operation from
cutoff 26 onward.  The proof uses the concrete single-substitution
interchange laws and numeral fixedness, so both native Sigma and Pi domain
witnesses are deeply closed without a standardness assumption.

`RawCodedDynamicTruthLowerApplicationDeepClosure.v` handles the second opaque
piece.  It identifies each native three-opening chain with the public ternary
application at variables `#9`, `#1`, and `#0`; deep predicate commutation and
application functionality then show that the native output is fixed by every
operation above cutoff 26.  Both the lower-Pi application in a Sigma row and
the lower-Sigma application in a Pi row therefore inherit deep closure from
the preceding global predicate.

`RawCodedDynamicTruthPairedSuccessorLocalDeepClosure.v` assembles those two
opaque leaves with the transparent row constructors.  It tracks the genuine
eight existential row witnesses and the three extra binders around the lower
application, weakens cutoff-26 closure to cutoff 29 where required, and
proves both actual local successor rows operationally fixed from the global
wrapper's cutoff 18.  The formerly explicit paired local-row callback is
therefore now an unconditional consequence of `RawPASatisfies`.

`RawCodedDynamicTruthUniversalLeafSourceTemplate.v` records the actual Rocq
Sigma successor-row syntax: eight existential table witnesses around a domain
check and a seven-way disjunction, whose final branch contains the opaque
lower-Pi application.  It supplies an honest eight-witness projection from an
explicitly restricted universal row and proves in the kernel that the older
five-witness, conjunction-only candidate is not this table row.  Concrete
instantiation therefore cannot silently identify the Lean-shaped schema with
Rocq's different encoding.

`RawCodedDynamicTruthPiUniversalLeafSourceTemplate.v` records the genuine
dual source rather than erasing polarity.  Its native Pi-falsity row has the
same eight table witnesses but six alternatives; the last is the existential
case and applies the preceding Sigma-truth predicate at variables `#9`, `#1`,
and `#0`.  Structural translation is proved equal to a transparent carrier
polynomial and, in PA models, to the existing native Pi row code.  The module
also supplies an honest restricted-existential projection from an explicitly
selected final branch.  As on the Sigma side, it does not project that branch
from the full disjunction and does not assume commutation for the nonstandard
opaque atom.

`RawCodedDynamicTruthTemplateNumeralParameters.v` instantiates the source
template's designated lower- and upper-level names at arbitrary carrier
elements.  Represented numeral-code totality selects both possibly
nonstandard numeral terms, and the package exposes their exact validity plus
the direct translator's complete term shift/open fields.

`RawCodedDynamicTruthTemplateDirectInputs.v` supplies the remaining opaque
interpretation.  Predicate zero at exactly three arguments is the selected
lower-Pi ternary application; every other predicate or arity is mapped to a
transparent bottom fallback with one-node operation traces.  The record asks
only for shift/opening commutation on honest structural syntax and proves
that all source, renamed, and opened terms meet that guard.  Its exact code
equations identify the translated Sigma-domain leaf with the native domain
substitution and the opaque atom with the native lower-Pi application.  Deep
closure now discharges the shift half of this guarded record; the honest
opening half remains the explicit seam.

`RawCodedDynamicTruthPiTemplateDirectInputs.v` provides the polarity-dual
identification without reusing the Sigma row as a dummy.  The shared numeric
parameter and predicate names are audited by literal equalities, the direct
translator's Pi-domain opening trace is identified with the native domain
substitution by cross-trace functionality, and the designated lower-Sigma
atom is transported through the exact Pi/Sigma application equivalence.  The
resulting package identifies both the full native Pi successor-row code and
the restricted existential projection code.  Its only remaining operation
input is the same honest-syntax commuting record used by the Sigma direct
translator.

`RawCodedDynamicTruthUniversalLeafProofCompilation.v` sends the honest
eight-witness restricted projection through that direct relational
translator and the closed-template packer.  It produces an exact ordinary PA
certificate both before and after the native thirteen-variable row
environment is universally closed.  Code-identification equalities remain
separate from the operational opaque traces, and the endpoint deliberately
continues to name the restricted universal branch rather than the full
seven-way disjunction.

`RawCodedDynamicTruthSigmaDomainProjectionProofCompilation.v` begins the
honest passage back to that full row.  A fixed template proof projects
`Ex^8 (domain /\ Or7 branches)` to `Ex^8 domain`, preserving all eight table
witnesses and discarding only the branch disjunction.  Direct structural
translation, thirteen-variable closure, and native-code identification yield
an exact coded PA proof of the resulting Sigma domain field; this is one
full-row eliminator, not yet the complete local bundle.

`RawCodedDynamicTruthPiExistentialLeafProofCompilation.v` supplies the exact
polarity-dual compiler.  It transports the honest eight-witness projection
of the explicitly restricted existential branch through the direct
translator, retargets the proof by the native Pi domain and lower-Sigma
identification, and universally closes the thirteen ambient row columns.
The exported certificate remains a proof of that restricted final branch;
it is not presented as a consequence of the full six-way Pi disjunction.

`RawCodedDynamicTruthPiDomainProjectionProofCompilation.v` supplies the
genuine full-row dual: `Ex^8 (domain /\ Or6 branches)` entails `Ex^8 domain`.
It preserves Pi's six-way polarity-specific syntax, closes the result over
the thirteen native row columns, and retargets the direct template proof to
the exact native Pi polynomial.  Together with the Sigma projection this
closes both domain eliminators, while the remaining full-disjunction case
analysis is still explicit work.

`RawCodedDynamicTruthUniversalLeafTransformGraph.v` exposes that restricted
certificate as an output-first transform over the paired global Sigma/Pi
truth-code orbit.  The graph selects the successor numeral, the instantiated
native Sigma-domain code, and the lower-Pi ternary application, then equates
its output with the transparent thirteen-times-universally-closed projection
code.  Its law-free semantics and relational totality are proved separately
from proof totality: the latter consumes direct structural inputs identifying
the graph's exact witnesses and returns an ordinary PA proof targeted at that
same output.  This is one checked restricted-row field, not yet the complete
local decision/exclusivity field required by the six-field master.

`RawCodedDynamicTruthPiExistentialLeafTransformGraph.v` provides the dual
output-first transform without swapping away the polarity.  Its lower opaque
application consumes the selected global Sigma code, its domain is the native
Pi-domain substitution at the successor numeral, and its transparent output
is the thirteen-fold closure compiled by the restricted Pi proof module.
Relational totality and proof-producing totality again remain separate, with
the latter requiring direct inputs that identify the graph's exact witnesses.

`RawCodedDynamicTruthRestrictedExistentialLocalProofFieldGraph.v` composes
that transform with the actual paired global truth-code orbit.  The hidden
Sigma and Pi codes therefore come from one adequate orbit witness, and the
direct compiler is required only along such witnesses.  A guarded ternary
shift/opening interchange package for the selected global Sigma coordinate
yields the exact proof-producing local field.  As with its Sigma dual, this
is still a restricted row component rather than the complete local law.

`RawCodedDynamicTruthRestrictedUniversalLocalProofFieldGraph.v` composes that
transform with the genuine paired global Sigma/Pi orbit and requires its
proof-producing compiler only for the Pi codes selected by an actual adequate
orbit witness.  Cross-trace functionality identifies both the native domain
substitution and lower application with the direct-template outputs before
the closed compiler is invoked.  The strongest endpoint consumes shift and
opening interchange only along those orbit witnesses and returns the exact
ordinary PA certificate selected by the public field graph.  This remains a
restricted-universal component: it does not upgrade the branch to the full
seven-way local law.

`RawCodedDynamicTruthSigmaDomainProjectionTransformGraph.v` returns to the
genuine full Sigma row.  Its output-first transform selects the successor
numeral, native domain instance, and lower-Pi application, then emits the
exact thirteen-closed certificate for `full Or7 row -> Ex^8 domain`.  The
transform composes with the paired global orbit into a predecessor-indexed
positive field.  Its sharp endpoint reuses the restricted-universal direct
compiler only along an adequate orbit and therefore needs shift/opening
interchange only for the actually selected Pi code.  This is a full-row
domain eliminator, not yet the branch-by-branch local decision law.

`RawCodedDynamicTruthPiDomainProjectionTransformGraph.v` is the polarity-dual
full-row field.  It compiles `full Or6 row -> Ex^8 domain`, with the lower
application taken from the selected global Sigma code, and composes it with
the same paired orbit at the predecessor level.  Its strongest proof-total
endpoint likewise reuses the restricted-existential structural compiler only
along an adequate orbit and is discharged by guarded interchange for the
selected Sigma code.  The symmetric pair now supplies honest positive graph
witnesses for both domain eliminators; the remaining row branches and their
decision/exclusivity assembly are still separate obligations.

`RawCodedDynamicTruthDeepClosedRestrictedLocalProofFields.v` selects the
actual deeply closed paired-orbit witness instead of transporting closure to
an arbitrary adequate witness.  The concrete shift and opening commutation
theorems then discharge both restricted compilers directly, without an orbit
functionality or uniqueness assumption.  The resulting Sigma-universal and
Pi-existential proof fields combine with the concrete paired-row closure
theorem to become unconditional in every PA model.  They are still only the
two advertised restricted branches, not the complete local
decision/exclusivity field.

`RawCodedDynamicTruthDeepClosedDomainProjectionFields.v` applies the same
selected-witness discipline to the two full-row domain projections.  For the
actual deeply closed paired orbit, it constructs concrete PA proof codes for
both the Sigma `Or7 -> Ex^8` eliminator and its Pi `Or6 -> Ex^8` dual.  The
deep-closure and substitution-algebra theorems discharge all structural
premises, so both projection graphs are proof-total in every PA model without
an extra orbit-wide interchange hypothesis.  This closes the two full-row
domain coordinates only; assembling every constructor branch into the local
decision/exclusivity field remains a separate obligation.

`RawCodedDynamicTruthNativeLocalPositiveGraph.v` now constructs the exact
carrier-indexed target for that complete positive local field.  A predecessor
`p` selects the genuine paired global orbit at `S p`; one real paired
successor then exposes the native Sigma `Or7` and Pi `Or6` evidence rows at
`S(S p)`.  Represented numeral substitution and ternary application build
the two input domains and evidence applications, and a transparent formula
polynomial assembles the literal decision/exclusivity bundle.  The module
proves exact law-free semantics, standard-index alignment, row exposure,
adequacy, and relational totality.  Its proof-total endpoint remains
conditional on the sharply stated compiler that must return a represented PA
proof of this exact selected carrier code; semantic validity is not used as a
substitute for that compiler.

`RawCodedDynamicTruthNativeLocalProofCompilation.v` compiles the complete
logical shell of that local field.  It explicitly introduces the
admissibility and evidence implications, closes both bodies under three
universal binders, and joins decision with exclusivity by conjunction.  Its
replacement compiler asks only for two same-context leaves: the evidence
disjunction under admissibility and bottom under admissibility plus both
evidence assumptions.  An exact trace adapter then discharges the original
nonstandard-index field compiler from this narrower interface.

`RawCodedDynamicTruthNativeCrossLevelPositiveGraph.v` constructs the adjacent-
level coherence coordinate with the same native indexing discipline.  For a
carrier predecessor `p`, it selects the genuine current orbit at `S p`, runs
the actual paired successor to `S(S p)`, applies all four global predicates,
and transparently builds the exact guarded Sigma/Pi coherence formula.  The
graph has law-free exact semantics, exposes the native successor rows, and is
relationally total in every PA model.  Every externally fixed standard level
has a represented PA proof; proof totality at a possibly nonstandard carrier
index remains conditional only on the explicit
`RawDynamicTruthNativeCrossLevelCoherenceProofCompiler`.

`RawCodedDynamicTruthNativeCrossLevelProofCompilation.v` compiles the complete
outer shell of that coherence field.  Four same-context directional roots—
the forward and backward implications for each polarity—are combined with
explicit implication, conjunction, and universal-introduction proof nodes.
The resulting adapter discharges the original field compiler without assuming
the field certificate or its semantic validity; the exact residual seam is a
local-root compiler indexed by the adequate orbit and literal construction
trace.

`RawCodedDynamicTruthNativeCrossLevelLeafRootCompilation.v` exposes the
actual successor rows behind that construction trace, retaining their row
domains, lower applications, shared global wrapper, and all four ternary
applications in one linked relation.  The trace supplies every atomic-
adequacy fact needed by the proof constructors.  One represented guarded-
equivalence root per polarity is then compiled, over an arbitrary visible
base tail, into the four directional leaves by checked context insertion,
assumption, implication-elimination, and conjunction-elimination nodes.  The
literal-empty adapter consequently reduces the original field compiler to
exactly two trace-linked guarded roots; no successor relation is mistaken for
a proof and no nonempty witnessed context is erased.

`RawCodedDynamicTruthNativeCrossLevelGuardRootCompilation.v` joins those two
guards at the dependency boundary used by Lean.  One coherence-body root over
an arbitrary visible base yields both polarity guards structurally.  In the
staged form, the current six-field master and the newly proved local field
already share one witnessed PA context; their checked conjunction is applied
to a single trace-linked implication whose consequent is the coherence body.
This produces both guard roots without changing that context.  Construction
of the implication root remains the exact positive cross-level kernel
obligation.  The module deliberately makes no unrestricted fixed-level
opening claim, semantic truth-to-proof inference, or empty-context
identification.

`RawCodedDynamicTruthNativeCrossLevelStagedRootCompilation.v` carries that
same body to the graph-facing certificate boundary.  It applies the staged
implication in the literal shared context, retains the witnessed PA-axiom
package while introducing the three universal binders, and proves an
ordinary represented certificate of the exact code selected by the native
cross-level transform.  Thus body decomposition and empty-base repackaging
are no longer needed by the successor assembler; the only remaining
cross-level content is still the explicitly named trace-linked staged kernel.

`RawCodedDynamicTruthNativeShiftPositiveGraph.v` constructs the third native
positive coordinate.  It selects the genuine paired truth orbit at `S p`,
builds the six source/target domain and certificate applications through
represented substitution traces, and assembles the literal eight-variable
formula-shift Tarski law.  Exact graph semantics is law free, while PA proves
adequacy-preserving relational totality and genuine certificates at every
standard level.  The public proof-total endpoint retains atomic adequacy of
the selected field code and depends only on the explicit
`RawDynamicTruthNativeShiftProofCompiler` for possibly nonstandard carrier
indices; semantic validity is never converted into proof syntax.

`RawCodedDynamicTruthNativeShiftProofCompilation.v` compiles the complete
eight-variable shift-law shell.  Four Sigma/Pi forward and backward leaves
share the exact one-assumption `shift-data` context; explicit conjunction
nodes build the two equivalences, implication introduction discharges that
common assumption, and eight universal-introduction nodes close the field.
The trace adapter retains the adequate orbit, numeral, domain substitutions,
and four application traces while eliminating any premise that already
mentions a completed field certificate.

`RawCodedDynamicTruthNativeShiftLeafRootCompilation.v` retains an arbitrary
visible base tail beneath that one-assumption context.  It derives adequacy
for both global predicates, both input domains, and all four trace-selected
application outputs, then projects each of the five nested shift-data members
with concrete assumption and conjunction-elimination roots.  Represented
implication introduction reduces the two Sigma/Pi equivalences to exactly
four trace-indexed directional leaves.  The empty-tail endpoint remains a
conditional specialization of those leaves, while the witnessed-tail form
keeps its PA context literal rather than silently discarding it.

`RawCodedDynamicTruthNativeShiftStagedRootCompilation.v` places that shell at
the dependency boundary used by the staged successor.  The current six-field
master, next local field, and next cross-level field are assembled in their
one witnessed PA context and applied to a single trace-linked implication
whose consequent is the synchronized shift body.  Checked decomposition
recovers all four directional laws, while eight universal-introduction nodes
retain the witnessed tail and package an ordinary proof of the exact
transform-selected field.  The one remaining arithmetic obligation is named
`RawDynamicTruthNativeShiftLinkedStagedBodyImplicationRootCompiler`; no
empty-context erasure or semantic truth-to-proof step is used.

`RawCodedDynamicTruthNativeSubstitutionCarrier.v` fixes the exact syntax for
the fourth positive master coordinate.  Its transparent polynomial closes
exactly the seven single-substitution parameters and combines the carried
Sigma/Pi source domains and certificate applications with the represented
substitution, assignment, target-admissibility, and rank-agreement relations.
At every standard predecessor `p` this code is literally the quotation of the
existing fixed-level substitution Tarski law at `S p`, and the module supplies
its represented PA proof.  The genuine arbitrary-carrier orbit transform and
uniform proof compiler are intentionally left to the subsequent positive
graph rather than inferred from this standard family.

`RawCodedDynamicTruthNativeSubstitutionPositiveGraph.v` supplies that genuine
orbit transform.  At predecessor `p` it selects the paired global Sigma/Pi
codes at `S p`, constructs the source applications `#1,#3,#4` and target
applications `#2,#5,#6` through their literal sequential replacement traces,
instantiates both current-level domains, and assembles the carrier polynomial.
Its graph semantics is law free, and PA proves adequacy-preserving relational
totality plus represented proofs at every externally fixed standard level.
The arbitrary-carrier proof-total endpoint retains field-code adequacy and is
conditional only on `RawDynamicTruthNativeSubstitutionProofCompiler`; it does
not infer proof syntax from semantic validity.

`RawCodedDynamicTruthNativeSubstitutionProofCompilation.v` compiles the
seven-variable substitution field around four directional transport leaves.
All four leaves share the literal side-condition context; explicit
conjunction and implication nodes assemble the two equivalences, seven
universal-introduction nodes close the field, and an empty witnessed context
packages the result as an ordinary PA certificate.  The exact trace adapter
reduces the former field compiler to these four roots without mentioning the
finished field code or assuming its truth.

`RawCodedDynamicTruthNativeSubstitutionLeafRootCompilation.v` refines those
four roots over an arbitrary visible base tail.  The construction trace
supplies adequacy for both current global predicates, both numeral-instantiated
domains, and all four application outputs; concrete assumption and
conjunction-elimination nodes project the five substitution side conditions.
Four directional target leaves are discharged by implication introduction,
after which three conjunction nodes and the outer implication assemble the
complete open substitution body over the same tail.  A resource-explicit
adapter ties every remaining leaf to one trace and hands it all derivable
adequacy and side-condition roots.  Literal-empty adapters remain conditional,
and the witnessed-tail endpoints never erase their PA context.

`RawCodedDynamicTruthNativeSubstitutionStagedRootCompilation.v` installs that
body after the exact dependency prefix `(((current master /\ next local) /\
next cross-level) /\ next shift)`.  One trace-linked implication in the
shared witnessed context yields the complete body; checked projections
recover all four directional resources and replay the public leaf shell.
Seven carried universal introductions then package an ordinary proof of the
literal transform-selected substitution field.  The sole remaining
mathematical seam is the named staged body-implication compiler, rather than
four unrelated empty-context leaf compilers.

`RawCodedDynamicTruthNativeAxiomSoundnessPositiveGraph.v` constructs the fifth
native positive coordinate from the same genuine paired orbit.  At predecessor
`p` it reads the lower domains at `S p`, takes the actual paired successor to
obtain the Sigma predicate at `S(S p)`, and forms the literal universal claim
that every transparently recognized PA axiom in the lower domain has a next-
Sigma certificate at arguments `(axiom, 0, 0)`.  The graph has law-free exact
semantics, adequate relational totality, and represented PA proofs for every
externally fixed standard predecessor.  At an arbitrary carrier predecessor,
proof totality is isolated in the explicit
`RawDynamicTruthNativeAxiomSoundnessProofCompiler`; model truth is not treated
as a coded PA derivation.

Its three sequential openings now make the de Bruijn argument order explicit:
the surviving axiom variable enters the first opening as `#2`, followed by two
closed zero terms, so the resulting application is exactly the global truth
predicate at `(axiom, 0, 0)`.  The definitional regression theorem records this
order, and
`RawCodedDynamicTruthNativeAxiomApplicationTernaryAlignment.v` proves that the
native trace is equivalent to the repository's generic represented ternary
application.  The reverse implication uses represented term-shift
functionality, so it also covers arbitrary witnesses of the relational shift
graphs rather than only their canonical quotations.

`RawCodedDynamicTruthPairedGlobalOrbitFunctionality.v` proves that the five
positive graphs really do refer to one paired global orbit.  Numeral and
substitution functionality make each Sigma/Pi successor row deterministic;
the transparent wrapper then makes the paired global successor deterministic.
A represented definable-induction invariant propagates pair uniqueness to
every carrier level, including nonstandard ones, and adequate totality upgrades
any law-free orbit witness to the adequate view.  Consequently five
independently exposed local, cross-level, shift, substitution, and axiom-
soundness graph witnesses can be rewritten onto one common adequate orbit and
their exact transforms.  This is relational coherence only: it assumes no
proof-producing field compiler or soundness principle.

`RawCodedDynamicTruthNativeAxiomSoundnessProofCompilation.v` compiles the
non-dynamic shell of that remaining proof.  From a covered local proof of the
selected next-Sigma evidence under the literal singleton axiom/admissibility
antecedent, checked implication- and universal-introduction constructors build
an ordinary represented proof of the exact carrier field code over an empty
witness context.  The original arbitrary-carrier compiler is thereby reduced
to `RawDynamicTruthNativeAxiomSoundnessLocalRootCompiler`, indexed only by the
adequate orbit and the actual successor, numeral, substitution, and
application trace.  This smaller interface asks for neither the final field
certificate nor semantic validity.

`RawCodedDynamicTruthNativeAxiomSoundnessLeafRootCompilation.v` exposes the
actual paired-successor rows, lower applications, wrapper, domain
substitutions, and next-Sigma application behind that trace.  It derives all
needed adequacy, projects the recognition, atomic-syntax, assignment, and
domain-disjunction conjuncts, and constructs every formula shift required by
the eigenvariable rule.  Represented `Or-E` splits the two lower-domain cases;
inside each case a represented `Ex-E` opens the actual PA-axiom witness body.
The exact residual is therefore two trace-linked proof leaves in the fully
shifted witness contexts.  The witnessed-tail endpoint uses the PA context's
proved self-shift, while a separate conditional adapter handles the literal
empty base; neither path erases a nonempty context or converts semantic truth
into proof syntax.

`RawCodedDynamicTruthNativeAxiomWitnessBodyRootCompilation.v` identifies the
Lean-aligned dependency boundary behind those two leaves.  One synchronized
kernel root over the visible shifted base proves the curried implication from
the shifted axiom-soundness antecedent and the opened witness body to the
shifted next-Sigma application.  Adequacy-guarded context insertion,
assumption leaves, and two checked implication eliminations specialize that
single root to both the Sigma- and Pi-domain witness branches.  Every row,
application, wrapper, context shift, and formula shift remains tied to the
same trace.  The module deliberately leaves construction of this one staged
kernel root explicit; it asserts neither an empty-base instance nor a
semantic truth-to-proof conversion.

`RawCodedDynamicTruthNativeAxiomStagedRootCompilation.v` carries that boundary
through the actual dependency order of the native successor.  In one
witnessed PA-axiom context it conjoins the six current master roots with the
already compiled local, cross-level, shift, and substitution roots, applies
one trace-linked implication from this ten-root prefix to the curried
witness-body kernel, and then reuses the checked `Ex-E`, `Or-E`, `Imp-I`, and
`All-I` shell to obtain an ordinary proof of the exact transform-selected
axiom field.  All formula shifts and the witnessed context self-shift remain
explicit.  The staged implication compiler is intentionally still a
premise: the module performs the complete proof-code assembly after that
arithmetic kernel without claiming to have constructed the kernel itself.

`RawCodedDynamicTruthNativeFinalStagedRootCompilation.v` extends that prefix
by the selected next axiom-soundness root, yielding the literal eleven-root
antecedent for the sixth field.  One graph trace binds the current and next
compact-consistency targets, the successor numeral code, and substitution in
the fixed dynamic-soundness source.  The sole residual compiler returns the
source-linked six-premise implication root in the canonical third-
existential context.  After that boundary, represented field projections,
six implication eliminations, triple existential descent, and carried
implication/universal closure produce an ordinary proof of the exact compact
graph target while preserving the original witnessed base.  The source-
linked implication compiler remains explicit; no uniform semantic soundness
or consistency-successor premise is asserted.

`RawCodedDynamicTruthNativeFinalUniversalSoundnessComposition.v` refines that
single final residual into the three proof roots used by the Lean argument,
all in the exact canonical candidate-proof context: a proof of one concrete
universal derivation-soundness code, an implication from that code to the
trace-selected `nextFinal`, and an implication from `nextFinal` to falsity.
Two checked implication eliminations and one bottom elimination compose those
roots into the existing source-linked six-premise endpoint.  This is a strict
syntactic decomposition, not a discharge: arbitrary-carrier soundness
induction, the fixed consistency-from-soundness source compiler, and the
structural opening/refutation of the sealed target remain the three explicit
proof-producing obligations.

`RawCodedDynamicTruthNativeFinalTargetRefutationCompilation.v` discharges the
third of those roots without adding a compiler premise.  The final graph
trace identifies `nextFinal` with the exact sealed restricted-consistency
target.  In the canonical third-existential context, the module assumes that
target, removes its fixed closure prefix using represented identity
substitutions, instantiates the genuine certificate quantifier with object
variable `3`, and applies the result to the literal three-times-shifted proof
assumption already present in the context.  Implication elimination and
introduction yield the required local proof of `nextFinal -> bottom`.  No
carrier decoding, semantic truth-to-proof conversion, dynamic-soundness
producer, or consistency successor is used; the universal-soundness and
consistency-from-soundness roots remain separate obligations.

`RawCodedRestrictedPAConsistencyFromUniversalSoundness.v` gives the middle
root an arbitrary-carrier structural formula instead of reusing the
metatheoretically expanded fixed-level invariant.  Its two opaque truth atoms
carry two named carrier-level parameters explicitly.  Because the
invariant preserves truth from a proof context rather than asserting truth of
PA axioms by itself, the boundary also requires the graph-selected
`nextAxiomSoundness` proof, its implication to the witnessed PA-context truth
law, and a bottom-truth refutation law in the exact implication-tail context.
The final adapter consumes the graph trace and all staged prerequisites and
produces only the consistency-from-soundness root.  It remains conditional on
the compiler that opens the universal invariant and on the compiler that
constructs those selected-axiom support proofs; neither obligation is hidden
or manufactured.

`RawCodedDynamicTruthNativeFinalSelectedAxiomSupportTransport.v` removes the
context mismatch from the selected-axiom part of that support boundary.  It
extracts the staged `nextAxiomSoundness` root from the witnessed base,
reconstructs the three canonical existential-descent shifts, proves inclusion
of the base through the four final bridge heads, and uses binder-ready checked
weakening to transport the root to the exact fields context.  The adapter
leaves only atomic adequacy of the last fields head as a separate syntactic
premise, together with the two genuine truth-coherence roots: the implication
from selected pointwise axiom soundness to witnessed-context truth and the
bottom-truth refutation law.  It proves no semantic truth producer and does
not discard any graph or staged prerequisite.

`RawCodedDynamicTruthNativeFinalBridgeFieldsHeadAdequacy.v` discharges that
last syntactic transport premise.  Six checker fields are ordinary quoted PA
formulae.  For the seventh, occurrence-bound field, the existing restricted-
target shift tree realizes the arbitrary-carrier numeral instance as a shift
target; scope below cutoff three proves that this shift leaves the field code
unchanged.  Shift-target adequacy and conjunction closure then prove atomic
adequacy of the exact seven-field head, and the graph trace supplies its
nonstandard numeral witness.  Consequently the selected-axiom transport now
has no residual premise beyond the two explicitly named truth-coherence proof
roots.

`RawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessBridge.v` handles the
different witnessed context hidden by an ordinary proof of the exact
universal-soundness code.  It opens that certificate, merges its witnessed
PA-axiom context with the eleven-root final staged context, and transports all
eleven existing roots into the merged base.  It then weakens the accumulated
soundness root through the canonical shifted proof contexts and regenerates
the consistency-from-soundness root over that same merged base.  The endpoint
is deliberately existential in the enlarged context: it does not pretend
that an induction axiom used by the ordinary certificate was already present
in the caller's original context.  Atomic adequacy of the projected-fields
head, exact lower-level alignment, the ordinary universal-soundness
certificate, and the existing consistency compiler remain explicit inputs.

`RawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessBridgeAdequacy.v`
specializes that honest enlarged-context endpoint to the final staged graph.
It invokes the unconditional fields-head adequacy compiler on the very same
trace and eleven-root prerequisite package, thereby removing the remaining
atomic-adequacy parameter without changing either returned context or proof
target.  The exact ordinary universal-soundness certificate, lower-level
code alignment, and consistency-from-soundness compiler remain explicit.

`RawCodedDynamicTruthNativeStagedPrerequisiteAccumulation.v` connects these
stage-local interfaces to the ordinary certificates returned by the public
dependency-ordered callbacks.  Starting with the six current master roots,
it opens and merges the local certificate to construct the cross-level
prerequisite package, then incrementally adds the cross-level, shift, and
substitution certificates to construct the next three packages, and finally
adds the axiom-soundness certificate to construct the eleven-root final
package.  At every
step all existing roots are rebuilt in the newly merged witnessed context
before the record is formed.  Consequently no later staged implication may
conjoin proof roots taken from unrelated hidden certificate contexts.

`RawCodedDynamicTruthNativeCrossLevelStagedCallbackCompilation.v` carries the
first accumulated package all the way to the public dependency-ordered
cross-level callback.  It selects one adequate paired-global orbit and one
cross-level transform output together, uses those same witnesses to certify
the positive graph and the exact proof target, merges the preceding local
certificate into the current master context, and invokes the staged body-
implication compiler.  Thus the callback has no additional context or graph-
coherence premise; its only remaining proof-producing input is the explicit
trace-linked cross-level arithmetic kernel.

`RawCodedDynamicTruthNativeShiftStagedCallbackCompilation.v` exposes the third
public callback from the trace-linked staged shift implication.  It merges the
local certificate into the current six-root context and then accumulates the
cross-level certificate, transporting every preceding root into one literal
witnessed context.  One adequate paired-global orbit and one exact shift
transform are retained for both the positive graph assertion and the carried
proof compiler.  The callback therefore adds no graph equality or context
identification premise; its only proof-producing residual is
`RawDynamicTruthNativeShiftLinkedStagedBodyImplicationRootCompiler`.

`RawCodedDynamicTruthNativeSubstitutionStagedCallbackCompilation.v` exposes
the fourth public callback from the linked staged substitution implication.
It accumulates current-plus-local, cross-level, and shift certificates in
that order, transporting the whole prefix after each witnessed-context merge.
One adequate paired-global orbit and one exact substitution transform remain
shared between graph membership and proof compilation.  Consequently the
adapter's only arithmetic residual is
`RawDynamicTruthNativeSubstitutionLinkedStagedBodyImplicationRootCompiler`;
it assumes neither context equality nor semantic validity.

`RawCodedDynamicTruthNativeAxiomStagedCallbackCompilation.v` exposes the fifth
public callback from the linked staged axiom kernel.  It keeps one adequate
paired-global orbit, its exact axiom transform, and the resulting positive
graph target in a single package, then accumulates the local, cross-level,
shift, and substitution certificates in dependency order.  The carried axiom
root compiler receives those ten synchronized roots and returns the ordinary
certificate for that same transform-selected target.  Its sole remaining
proof-producing premise is
`RawDynamicTruthNativeAxiomLinkedStagedKernelImplicationRootCompiler`; no
context equality, empty-base replacement, or semantic truth-to-proof
principle is introduced by the adapter.

`RawCodedDynamicTruthNativeFinalStagedCallbackCompilation.v` exposes the
sixth public callback from the final source-linked implication compiler alone.
It opens the five preceding graph/proof pairs, preserves their graph halves,
and feeds their ordinary certificates through the complete accumulation chain
in production order.  The resulting eleven roots inhabit one witnessed
context and are passed to the carried final wrapper, which returns the exact
compact-target graph/proof pair.  Every merge and transport is already proved;
the adapter adds no context equality, empty-base replacement, or semantic
premise beyond the named source-linked kernel.

`RawCodedDynamicTruthNativeDependencyOrderedCallbackCompilation.v` collects
the exact six residual kernels behind the public adapters.  A model-local
bundle contains the concrete template translation agreement, the local staged
root builder, and the linked cross-level, shift, substitution, axiom, and
final compilers.  From that bundle the module derives the literal six-callback
family, the positive master successor, and—under an all-model instance—the
compact headline.  This is an exact conditional endpoint, not the missing
unconditional Coq theorem: every arithmetic residual, especially the final
source-linked derivation-soundness compiler, remains visible in the bundle.

`RawCodedDynamicTruthNativeDependencyOrderedUniversalSoundnessBoundary.v`
sharpens that complete conditional boundary at its final coordinate.  The
translation agreement and the local, cross-level, shift, substitution, and
axiom kernels are unchanged, while the last source-linked compiler is
replaced by the three exact same-context roots above.  The module reconnects
this refined bundle to the literal callback family, positive master
successor, and compact headline.  It remains conditional on every listed
kernel; its value is that the headline boundary now exposes universal
derivation soundness, consistency-from-soundness, and target refutation
separately instead of hiding them behind one final premise.

`RawCodedDynamicTruthNativeDependencyOrderedUniversalSoundnessBridgeBoundary.v`
uses the canonical final target-refutation compiler to discharge the third of
those roots.  Its refined final interface preserves one shared soundness code
and asks only for a proof of universal restricted-derivation soundness and a
proof of the implication from that same code to the selected consistency
target.  All earlier staged kernels remain explicit, so the resulting compact
headline is still conditional precisely on those kernels and these two final
proof-producing obligations.

`RawCodedRestrictedPADerivationSoundnessPredicate.v` isolates the first exact
proof-code induction slice behind that final compiler.  For each fixed
metatheoretic `level`, it defines the unary invariant `P(d)` saying that every
admissible endpoint of a restricted derivation code preserves Sigma truth,
defines the literal strong prefix `K(d) = forall e < d, P(e)`, and proves its
arbitrary-model semantics and equivalence to the existing constructor-local
soundness invariant.  The module then quotes `K` and constructs the complete
diagonal-substitution and closure-induction data consumed by the represented
PA induction compiler.  Its formula-scope premise remains explicit because
the downstream scope development cannot be imported here without creating a
dependency cycle.  More importantly, this is still a standard-`nat` level
slice: it neither replaces `level` by an arbitrary model carrier nor supplies
the opaque successor-truth application needed by the uniform nonstandard
theorem.

`RawCodedRestrictedPADerivationSoundnessScope.v` discharges exactly that
metatheoretic formula-scope premise for every external fixed truth level.  It
proves the Sigma/Pi truth-certificate scopes simultaneously, composes them
through admissibility and context truth, and then closes the complete
restricted-proof checker and strong-prefix formula.  The large proof
constructor table is handled through list-level scope lemmas so that its
arithmetic graphs are not repeatedly expanded.  This removes a syntactic
premise from the represented proof-code induction interface, but deliberately
does not turn the external `nat` level into an arbitrary element of a
nonstandard PA model.

`RawCodedRestrictedPADerivationSoundnessScopeDischarge.v` applies that theorem
to the quoted closure-induction data, eliminating the scope argument from its
public fixed-level adapter.  It also specializes the generic local and global
PA induction compilers to the exact soundness codes.  Those compiler theorems
remain conditional on explicit local proofs of the zero instance and the
universally quantified successor step; they expose rather than manufacture
the two remaining proof-producing obligations.

`RawCodedRestrictedPADerivationSoundnessCarrierInductionShell.v` performs the
corresponding finite syntactic assembly for the arbitrary-carrier soundness
template.  It derives the shifted, successor, zero, universally quantified,
and compound induction codes from one structural translation, packages the
three genuinely nonstandard closure operations as an explicit remainder, and
turns supplied zero and successor roots into an ordinary PA proof certificate
of the exact universal soundness code.  Returning an ordinary certificate is
essential: its witnessed context may contain the newly introduced induction
axiom and can later be merged with the staged final base.  This shell remains
conditional plumbing, not the soundness proof itself.  In particular, its
direct successor premise `forall d, P(d) -> P(S d)` is not silently identified
with the strong-prefix premise naturally supplied by recursive proof
soundness, and neither induction case nor the three closure operations is
manufactured here.

`RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixInductionShell.v`
replaces that direct induction shape with the one required by recursive proof
soundness.  It defines `K(d) = forall e, e < d -> P(e)`, represents the genuine
strong step `forall d, K(d) -> P(d)`, and assembles ordinary PA induction on
`K`.  Supplied `K(0)` and `forall d, K(d) -> K(S d)` roots produce an ordinary
certificate of `forall d, K(d)`; a separately supplied, exact finalizer root
then yields the bridge's literal `forall d, P(d)` code.  The module exposes
three honest remaining interfaces rather than conflating them: construction
of the two induction cases from the genuine strong step, the nonstandard
bound/closure/self-opening remainder, and the finalizer that instantiates
`K(S d)` and uses `d < S d`.  In particular, it never assumes the unavailable
direct implication `P(d) -> P(S d)`.

`RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerCompilation.v`
checks that finalizer's complete logical proof tree.  Under the assumed
`forall d, K(d)`, it performs represented universal elimination first at
`S d` and then at `d`, applies the resulting guarded conclusion to
`d < S d`, and closes the eigenvariable and implication with literal All-I
and Imp-I constructors.  Both substitution traces and the open context's
self-shift are proved.  PA's ordinary proof of `d < S d` is also compiled to
a raw certificate, leaving only the precise context-alignment question:
placing that arithmetic root in the already fixed context containing the
strong-prefix premise and the freshly adjoined induction axiom.  Thus the old
finalizer hypothesis is reduced to a strictly smaller syntactic arithmetic
leaf and is never assumed circularly.

`RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixGrowingFinalizer.v`
resolves that context mismatch by allowing PA's proof of `d < S d` to choose
its finite standard axiom prefix first.  It lifts the incoming strong-step
root through the same induction axiom into the enlarged witnessed context,
moves the arithmetic root beneath the temporary closed `forall d, K(d)`
premise using an explicit binder-readiness square, invokes the checked
finalizer tree, and returns an ordinary proof of `forall d, P(d)`.  Its full
package exposes the prefix, all transported roots, both induction cases, and
the final certificate.  The endpoint remains honestly conditional on the
separate strong-prefix case compiler; it removes the fixed-context finalizer
boundary but does not disguise the still-unconstructed zero/successor cases.

`RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixGrowingCaseCompilation.v`
constructs those two cases without a fixed-context assumption.  PA proves the
closed arithmetic kernels `forall e, not (e < 0)` and
`x < e -> e < S d -> x < d`; an explicit template proof uses them to derive
`K(0)` and `forall d, K(d) -> K(S d)` from the genuine strong step.  The
compiler selects one finite standard-axiom prefix for both kernels, transports
the incoming strong-step root and both arithmetic roots through the same
adjoined induction context, and returns the exact pair required by the shell.
Its substitution and renaming lemmas record finite support structurally, so
kernel checking does not normalize the large soundness predicate merely to
verify a de Bruijn identity.

`RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixGrowingIntegration.v`
composes that growing case package with the growing finalizer directly.  It
chooses the finalizer's arithmetic prefix above the case prefix, transports
the strong step and both case roots through that common extension, and
flattens the two witnessed bases to the single prefix
`finalizerPrefix ++ casePrefix`.  The compact corollary now produces an
ordinary PA certificate of the universal derivation-soundness formula without
the former separate case-compiler premise.  This is still not the unconditional
Coq headline: the concrete carrier truth interpretation, the nonstandard
closure remainder, and the genuine recursive strong-step proof remain explicit
inputs to the later soundness construction.

`RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell.v`
ports the same `P`/`K` induction graph to direct opaque traces.  It proves the
shift, successor-opening, and zero-opening fields, projects only the genuinely
nonstandard bound/closure/self-instantiation remainder, and packages supplied
case and finalizer roots as an ordinary PA certificate of the exact direct
universal-soundness code.  The companion direct growing-case module reuses
the already checked 1,630-line finite case metaproof through the generic
template compiler, then selects and transports one honest finite PA-axiom
prefix for both arithmetic kernels.  It does not infer a finite structural
tree from a direct trace.  These modules remove a translation mismatch but do
not yet construct the context-truth selector, the recursive strong-step root,
or the arbitrary-carrier closure remainder; the Coq headline therefore
remains conditional.

`RawCodedDynamicTruthNativePositiveLocalProofTotals.v` strengthens the five
individual endpoints in the form required for common-context assembly.  For
each native positive graph it selects the actual carrier field and returns a
proof root in the literal empty context, then bundles all five totals.  The
construction uses the same adequate orbit and exact transform trace consumed
by each local-root compiler; it never opens an ordinary certificate or merges
independently chosen proof contexts.

`RawCodedDynamicTruthNativeMasterEndpoint.v` fixes all five native graphs in
the previously verified zero/positive splice and six-field master assembler.
It discharges the complete level-zero callback and shows that the single exact
all-model positive-component successor compiler implies the literal Coq
headline
`Formula.BProv Formula.Ax_s [] compactUniformRestrictedPAConsistencyProvabilityFormula`.
This endpoint is intentionally conditional: it pins the remaining work to the
common-context successor compiler without hiding a truth, completeness, or
proof-transplant assumption.

`RawCodedDynamicTruthNativeMasterSuccessorFromProofTotals.v` assembles the
strongest successor currently justified by the five native proof totals and
the compact-consistency certificate successor.  It produces the exact six
next graph targets and six ordinary proofs unconditionally.  Its sharper
adapter keeps the five native roots in the empty context, opens only the
sixth certificate's witnessed context, and isolates the remaining operation
as transport of one empty-context local proof into that supplied context.
No identification or implicit merge of existentially chosen contexts is used.

`RawCodedPALocalProofEmptyContextTransport.v` discharges that isolated
operation.  Every formula in a witnessed PA-axiom context is atomically
adequate by its represented self-shift, and PA-definable reverse induction
over the context's certified tail table iterates the checked one-head proof
transplant through a possibly nonstandard context length.  The conclusion
code and supplied witnessed context remain literal; only the proof root is
rebuilt.  This proves the exact empty-to-witnessed transport interface in
every PA model without decoding a context or assuming semantic completeness.

`RawCodedPALocalProofWitnessedContextMerge.v` handles the genuinely harder
case of two independently chosen, possibly nonstandard witnessed contexts.
A PA-definable reverse fold prefixes the complete left witness/axiom traversal
onto the right package, proves represented membership inclusion for both
inputs, and unconditionally transports every proof from the literal right
context into the merged context.  The opposite direction is isolated as the
single named `RawCodedPALocalProofWitnessedContextInclusionWeakening`
operation: rebuilding a proof over an inclusive witnessed target must also
handle binder-induced context shifts.  Conditional only on that exact
syntactic operation, a fixed five-step fold synchronizes all six ordinary
master-field certificates while preserving their literal conclusions.  The
module does not claim an assumption-free arbitrary-context merge.

`RawCodedPALocalProofWitnessedContextInclusionWeakening.v` expands that
single proof-tree operation into all seventeen raw natural-deduction rule
cases.  Assumptions use literal membership inclusion; propositional,
quantifier-elimination, and equality rules recursively rebuild their checked
children; `All-I` and the body branch of `Ex-E` alone require a shifted target
context.  Parallel source/target shifts preserve membership inclusion by
represented formula-shift functionality, and PA-definable strong induction
then covers every carrier-valued proof root, including nonstandard ones.  The
remaining `RawContextListIncludedTargetShiftExists` premise is exactly target
shift existence under nested binders.  It is proved for a top-level witnessed
target but intentionally remains explicit for arbitrary temporary contexts,
where formula shift is partial on malformed carrier codes.

`RawCodedPALocalProofWitnessedContextMergeTransportComplete.v` eliminates
that last premise at the witnessed endpoint without asserting that malformed
arbitrary contexts can be shifted.  Its representable `RawContextBinderReady`
invariant says that every concrete source shift can be mirrored in the target
while preserving inclusion.  The invariant survives adding the same temporary
assumption to both contexts.  After a binder, the shifted target is entirely
atomically adequate; a PA-definable reverse traversal therefore constructs
its next unit shift and regenerates binder readiness.  Object-level strong
induction applies the invariant to all seventeen rule cases, including
nonstandard proof roots.  The resulting theorems give unconditional witnessed
context inclusion weakening, merge two independently witnessed proof
contexts, and synchronize all six ordinary master-field proofs in one literal
witnessed context.

`RawCodedPALocalProofAdjoinedContextTransport.v` packages the two context
extensions needed by carrier-level induction compilers.  It lifts witnessed
base inclusion and proof weakening through the same newly adjoined induction
axiom.  It also transports a proof beneath a temporary open-context head from
an explicit unit-shift trace for that head, which supplies the precise binder
readiness needed by All-I and Ex-E descendants.  Combined endpoints handle an
induction extension followed by a closed temporary premise, while keeping the
premise distinct from PA-axiom witnessing.  These lemmas support honest
grow-the-witnessed-base-first constructions; they do not assert that an
arbitrary fixed or empty axiom context already proves every PA theorem.

`RawCodedPAOrdinaryProofWitnessedContextAccumulation.v` exposes the incremental
form needed by dependency-ordered callbacks.  It opens one ordinary proof
certificate, merges the hidden witnessed axiom context with an existing
witnessed base, and returns both the new local root and a uniform transport
for every root already in that base.  A fixed metatheoretic `Forall2` helper
moves a finite family of old roots together; it never recurses over a coded,
possibly nonstandard context.  Thus later successor fields may consume exact
earlier field certificates in one literal context without identifying their
original hidden contexts or assuming an empty-context proof.

`RawCodedDynamicTruthNativeMasterSuccessorTransportComplete.v` applies that
theorem to the staged native successor.  Its public adapters no longer ask
for any context transport or common-context lift: they require only the five
named native leaf compilers and the nonstandard compact-consistency
certificate successor.  Those remaining proof-producing inputs stay visible;
the module does not repackage them as an unconditional endpoint.

`RawCodedDynamicTruthNativeStagedPositiveSuccessor.v` removes the circular
compact-consistency-successor premise from the assembly boundary.  Six exact
callbacks follow Lean's dependency order: local receives the current master;
cross-level also receives local; shift also receives cross-level;
substitution also receives shift; axiom soundness also receives substitution;
and the final callback receives all five new fields and directly returns the
graph-selected next consistency target with its proof.  The callbacks may
choose dependent targets and certificates, so none must work in isolation.
After all six stages, completed witnessed-context merging synchronizes those
same ordinary proofs without changing a target.  The module derives the
native positive component successor and the requested PA headline from this
non-circular, all-model callback family; construction of the six represented
stage producers remains explicit.

`RawCodedDynamicTruthQFBranchExclusivity.v` closes the first genuine cell of
that constructor matrix.  The native Sigma and Pi quantifier-free branches
use the same formula and assignment inputs but demand rank-zero outputs one
and zero, so the represented functionality theorem yields their exact
curried contradiction.  The construction tracks the literal eight-witness
branch closures, proves the corresponding fixed PA theorem and carrier code,
and exposes both common-context modus ponens and guarded nested-assumption
endpoints.  It deliberately claims only the QF/QF collision; the remaining
constructor pairs and the full decision/exclusivity assembly are still open.

`RawCodedDynamicTruthImpBranchExclusivity.v` adds the two same-constructor
implication cells.  Sigma's false-left and true-right branches each collide
with Pi's false-implication branch once an explicit exclusivity law for the
synchronized predecessor-state table is supplied.  Constructor injectivity
aligns the relevant child codes, and fixed PA proofs of the two conditional
cells are exposed as exact carrier codes with common-context and guarded
three-assumption endpoints.  The predecessor-state exclusivity root remains
an explicit obligation: this module neither identifies table membership with
a global-predicate application nor claims the completed matrix.

`RawCodedDynamicTruthBooleanBranchExclusivity.v` proves the two remaining
same-level Boolean cells under that identical predecessor invariant.  Sigma
conjunction supplies both positive children while Pi conjunction supplies one
negative child; Sigma disjunction supplies one positive child while Pi
disjunction supplies both negative children.  And/Or constructor injectivity
aligns the selected child codes, after which the predecessor law closes the
collision.  Both conditional cells have exact quotation-aligned carrier
codes, represented PA certificates, and literal common-context collision
endpoints.

`RawCodedDynamicTruthConstructorBranchDisjointness.v` discharges the
lower-independent off-diagonal portion of the native collision matrix.
Binary/unary arity separation and distinct principal tags yield one generic
PA theorem, then a checked finite classification identifies exactly sixteen
matrix-ready cells.  Their formulas and carrier codes are independent of the
metatheoretic lower-formula parameters, and the module supplies represented
certificates plus common-context collision endpoints.  The classification is
deliberately strict: the eight off-diagonal cells touching Sigma-All or Pi-Ex
still embed a preceding truth formula, so the generic theorem gives only
standard-formula instances for those cells.  Turning their arbitrary carrier
codes into principal-constructor proof roots remains part of the dynamic
binder compiler rather than being hidden behind this result.

`RawCodedDynamicTruthBinderOffDiagonalExclusivity.v` gives those eight cells
their literal arbitrary-carrier shape.  Sigma-All and Pi-Ex branch codes are
built directly from the native row polynomials with the opaque lower
application left as a model element; the module enumerates exactly the eight
off-diagonal cells touching either branch and proves their atomic adequacy.
Fixed principal-witness formulas supply PA proofs of all eight constructor
collisions, and a checked local composition theorem turns two exact
branch-to-principal projection roots plus that fixed collision root into the
curried pair required by the 7-by-6 matrix.  The Ex8 projection roots remain
an explicit object-proof premise because compiling them for an opaque
carrier formula requires checked formula/context shift traces; no semantic
truth assumption is substituted for that missing compiler.

`RawCodedDynamicTruthBinderPrincipalProjectionCompilation.v` compiles those
eight branch projections with one transparent repeated-existential selection
template.  Lower-independent branches need no dynamic premise; Sigma-All and
Pi-Ex use direct structural translations whose single designated opaque atom
is the selected lower application.  The module returns both projection roots
for every classified cell in the exact existing PA context, with concrete
adapters from native selector traces and from deep ternary closure.  Thus the
projection logic itself is complete; the operational boundary is precisely
the represented shift/open commutation used to construct the direct inputs,
not a semantic truth or completeness assumption.

`RawCodedDynamicTruthQuantifierBranchExclusivity.v` isolates the two
same-constructor quantifier cells.  Sigma-Ex versus Pi-Ex is conditional on
the exact adjacent-level fact that the positive existential branch supplies
the lower-Sigma counterexample rejected by Pi; Sigma-All versus Pi-All uses
the polarity-dual premise.  Both premises, native branch formulas, and
conditional cell codes are given as literal carrier polynomials, with PA
proofs and represented certificates for every standard lower-application
formula.  At arbitrary carrier codes the module exposes the conditional-cell
compiler and cross-level proof root rather than decoding the code.  Once
those exact roots and the two selected branch roots share a context, three
checked implication eliminations derive bottom.  Restricted Sigma-universal
and Pi-existential projection helpers connect the cells to the existing
native template compilers.

`RawCodedDynamicTruthQuantifierConditionalCellCompilation.v` replaces the
standard-only proof of those two conditional cells by finite structural proof
trees.  A generic matched All-E/Ex-E kernel proves the repeated-quantifier
collision, and its two exact eight-binder native instances compile to both
ordinary represented PA certificates and local roots in an existing
self-shifting common context.  The sole remaining input is sharply limited to
the represented shift/open trace package for the selected opaque lower
application; native ternary selectors and commuting traces adapt directly to
that package.  Atomic adequacy alone is not claimed to manufacture these
traces, and no semantic-validity-to-proof shortcut is used.

`RawCodedDynamicTruthMixedQFBranchExclusivity.v` completes the eleven matrix
cells having exactly one quantifier-free branch.  Seven Boolean cells are
conditional only on the exact synchronized rank-zero replay root; the four
quantifier cells are unconditional because a rank-zero traversal has no
quantifier production rule.  All eleven have fixed PA theorems, standard
represented proofs, and common-context collision eliminators.  Nine cell
codes ignore their carrier-valued lower inputs and therefore already have
arbitrary-carrier represented proofs.  The remaining boundary consists of
exactly two lower-dependent clauses, Pi-Ex at an arbitrary lower-Sigma
application and Sigma-All at an arbitrary lower-Pi application, packaged by
`RawDynamicTruthMixedQFOpaqueQuantifierCellProofCompiler`.

`RawCodedDynamicTruthLocalCollisionMatrixAssembly.v` assembles the complete
seven-by-six exclusivity matrix from the individual cell compilers.  It fixes
the literal Sigma and Pi branch orders, audits all forty-two classifications,
and produces both every curried pair contradiction and the corresponding
finite-disjunction pair family.  Given proofs of the actual right-associated
`Or7` and `Or6` branch rows, the generic matrix eliminator now derives bottom
in the same represented context.  The input record deliberately exposes the
remaining replay, cross-level, binder-projection, fixed-helper, traversal, and
row-root obligations; this finite assembly does not claim to project an
actual successor row or to complete the whole local decision compiler.

`RawCodedDynamicTruthSuccessorRowBranchDisjunctionCompilation.v` supplies the
missing structural row projection.  A generic raw template proof distributes
an arbitrary existential tower over a finite right-associated disjunction;
its exact eight-binder Sigma and Pi instances project the branch component of
the literal successor row and produce the matrix's `Or7` and `Or6` codes in
the same represented context.  The carrier compiler requires only context
realizability, a self-shift, the existing direct structural traces, and the
literal domain/lower-application identification—never a semantic decoding of
the row.

`RawCodedTruthCertificateMasterMixedQFHelperBatch.v` synchronizes every fixed
cell needed so far.  It appends exactly the nine carrier-independent mixed-QF
theorems to the existing twenty-nine collision and binder-principal helpers,
proves position-by-position equality with their native carrier codes for
arbitrary lower inputs, and places all thirty-eight helper roots together with
the six current master roots in one literal witnessed context.  The two
lower-dependent mixed cells are explicitly absent, so their structural
compilers remain measurable rather than being folded into a quoted helper.

`RawCodedTruthCertificateMasterHelperLookup.v` supplies the structural
eliminator for those synchronized batches.  Membership of a named fixed
helper now recovers its corresponding local proof root without destructing
all thirty-eight roots or changing the shared represented context.  The
lemma follows the helper and root lists position-for-position and introduces
no proof, weakening, or semantic premise of its own.

`RawCodedDynamicTruthMixedQFHelperRootExtraction.v` applies that lookup to the
mixed quantifier-free suffix.  It recovers the exact nine carrier-independent
cell roots from the synchronized helper batch, and then exposes a finite
adapter from those roots plus the two explicitly lower-dependent opaque roots
to the complete eleven-cell family required by the local collision matrix.
The module therefore records, without hiding it in a broad interface, the
precise two-cell boundary still requiring structural compilation.

`RawCodedDynamicTruthMixedQFOpaqueQuantifierCellCompilation.v` closes that
two-cell structural boundary.  A transparent proof preserves all eight outer
witnesses while replacing an opaque negative three-binder lower application
by the fixed-bottom instance, without decoding the carrier formula.  The two
fixed-bottom PA theorems are explicit seeds appended after the synchronized
thirty-eight-helper batch, so the six master roots, forty helpers, and both
transported arbitrary-cell roots can inhabit one literal witnessed context.
Ordinary and adequacy-indexed compilers require only their exact direct
shift/open trace; the all-carrier interface honestly retains the stronger
trace-totality premise rather than deriving it from atomic adequacy.

`RawCodedDynamicTruthNativeLocalLeafRootCompiler.v` moves the local-field
assembly to the correct witnessed-tail boundary.  It extracts the fixed
collision roots from the synchronized forty-helper batch, builds both opaque
mixed-QF cells in that same context, transports the complete matrix package
through the admissibility and evidence assumptions, projects concrete Sigma
and Pi successor rows to `Or7` and `Or6`, and runs the full seven-by-six
eliminator.  The residual record explicitly retains only carrier-dependent
replay, projection, trace, adequacy, and fixed-pair resources.  Its literal
empty-tail endpoint is a conditional adapter: no nonempty witnessed PA
context is erased.  The module's broad row-root callback is intentionally
parametric in four row values and is therefore stronger than the eventual
trace-linked evidence compiler; the exact concrete endpoint consumes row
roots and matrix resources indexed by the same values.

`RawCodedDynamicTruthNativeGlobalEvidenceRootCompilation.v` replaces that
broad callback with the exact trace-linked boundary.  Destructing the paired
global successor exposes the actual Sigma/Pi row domains and lower-predicate
applications together with their wrapper and ternary-application links.  A
corrected evidence compiler may return roots only for those existentially
selected rows, and a dependent resource callback must build the collision
matrix at precisely the same four parameters.  General witnessed-tail and
literal-empty-base adapters feed this package into the completed local leaf
compiler.  The module does not manufacture the two row proofs: their
represented global-evidence elimination remains an explicit compiler rather
than an invalid request for every arbitrary row.

`RawCodedDynamicTruthNativeLocalDecisionRootCompilation.v` compiles the
propositional shell of the other local leaf.  From the literal admissibility
assumption it performs two checked conjunction-right projections to recover
the rank-domain disjunction, then applies represented `Or-E` to two
trace-linked case roots.  Crucially, each rank case proves the same target
`sigmaEvidence or piEvidence`; a rank-domain formula is not confused with a
truth polarity.  Realizable, witnessed, and literal-empty-base endpoints are
separated explicitly.  The final empty-base adapter combines these case
roots with the trace-linked row and matrix packages without reintroducing the
older all-carrier decision callback.  The two dynamic rank-case roots remain
the precise decision obligation.

`RawCodedDynamicTruthNativeLocalStagedRootCompilation.v` reunites those two
local leaves over a visible witnessed base without forcing that base to be
empty.  One exact successor trace supplies the linked row domains, lower
applications, adequacy facts, and positional parameters.  The synchronized
forty-helper batch discharges all sixteen valid fixed constructor pairs, and
generic `Or7`-by-`Or6` resources build the finite collision matrix.  The
remaining staged package records only the two domain-case roots, two actual
row roots, seven genuinely current-field kernel components, two dependent
row-projection packages, and the three temporary-context self-shifts.  From
that package checked implication and universal introduction construct the
carried local field root.  No proof equality, unlinked row choice, semantic
truth-to-proof conversion, or hidden empty-context transport is used.

`RawCodedDynamicTruthNativeLocalStagedCallbackCompilation.v` connects that
carried root to the first public dependency-ordered callback.  It extends the
actual current six-field proof package with the ordered forty-helper batch,
retaining one witnessed context and all current graph witnesses.  The exact
residual builder sees this package, the one selected local transform trace,
and its linked row parameters, and returns only the staged root package.
Adequate orbit selection, transform extraction, carried-root certificate
packaging, and positive-graph satisfaction are then concrete.  Thus the
callback neither assumes an empty-base leaf compiler nor permits an unrelated
helper context.

The old dynamic-soundness base premise is also too rigid as a construction
target.  It ranges over every witnessed base, including the empty context, but
the raw local calculus has no PA-axiom rule: adding an induction axiom
necessarily grows the witnessed assumption context.  The safe replacement is
`RawRestrictedPAConsistencyGrowingOpenContradictionCompiler` in
`RawCodedRestrictedPAConsistencyGrowingOpenCompiler.v`.  Its output may choose
an enlarged, honestly witnessed and self-shifting PA base.  A verified bridge
closes the open contradiction and feeds the compact certificate successor
directly, without asserting a uniform dynamic-soundness truth formula and
without transplanting an unrelated finished tree.

The preferred final architecture now mirrors the completed Lean proof.  A
model-internal induction package should retain six fields: five reusable
dynamic-truth laws and a forced final bounded-consistency target.  The Coq
module `RawCodedTruthCertificateFinalProjection.v` defines the corresponding
right-associated six-field master code and proves that five checked And-E2
steps project an ordinary PA certificate for its final coordinate while
preserving the same witnessed axiom list and base context.  What remains is to
port the five represented dynamic field graphs, base certificate, and staged
successor compiler; their outputs are proof codes, never a uniform truth
assertion.

The structural outer graph is now represented explicitly by
`RawCodedTruthCertificateMasterGraph.v`: four hidden conjunction-tail codes
select exactly the right-associated six-field master code, and the associated
direct package requires that very code to carry an ordinary PA proof
certificate.  Its generic extraction theorem feeds the final projection
above.  The still-missing graph work is therefore the five concrete
level-indexed dynamic-truth field graphs, not the conjunction wrapper or the
forced final-coordinate connection.

`RawCodedTruthCertificateMasterInduction.v` closes the generic outer
induction as well.  For any fixed output-first master graph it represents the
direct package “the graph-selected master code has a PA proof”, performs PA
induction over arbitrary model elements from explicit zero and successor
callbacks, decomposes the graph into six fields, and feeds the forced final
field into the compact selector.  Raw-model completeness then yields the
exact uniform object theorem conditional only on the concrete graph's
decomposition, base, and successor callbacks.

`RawCodedTruthCertificateMasterIntroduction.v` supplies the complementary
constructor direction.  Six component proofs over one witnessed PA-axiom
context are combined by five coverage-certified And-I nodes into the exact
right-associated master proof, then repackaged as an ordinary PA certificate.
Thus the concrete zero stage only has to produce the six component roots in a
common context; it need not rebuild the structural conjunction compiler.

`RawCodedTruthCertificateMasterAssembler.v` now assembles any five concrete
output-first field graphs with the compact restricted-consistency code graph.
Its explicit de Bruijn remapping has exact arbitrary-model semantics, forces
the resulting master witness to be the six-field conjunction code, supplies
the decomposition callback used by the outer induction, and derives combined
graph totality from totality of the five dynamic inputs.

`RawCodedTruthCertificateMasterBaseBridge.v` reduces the concrete zero
callback to component-level data without losing the selected codes.  It
supports either six raw local proofs in one witnessed PA-axiom context, or
five standard closed `BProv` derivations accompanied by explicit graph views;
the compact sixth component is supplied by the proved level-zero consistency
theorem.  The standard route deliberately requires quoted-code witnesses and
never identifies an arbitrary nonstandard graph output with a quotation.

`RawCodedDynamicTruthMasterBasePackage.v` instantiates that bridge with the
five concrete level-zero dynamic-truth slices, in the master constructor's
exact order: local decision/exclusivity, adjacent-level coherence, shift
invariance, substitution invariance, and witnessed PA-axiom soundness.  Each
slice contributes both its standard quoted-code graph witness and its closed
`BProv` theorem, yielding the exact unconditional base callback consumed by
master induction.  This is deliberately only the level-zero package; it does
not stand in for the carrier-indexed component families still needed at
positive, possibly nonstandard, levels.

`RawCodedDynamicTruthMasterSplicedBasePackage.v` lifts the same five checked
zero coordinates through `dynamicLocalFieldGraph`, parameterized by arbitrary
future positive/predecessor graphs.  Its exact zero views and `BProv`
derivations therefore establish the master-induction base callback for the
eventual nonstandard-safe field splices without assuming any positive
totality or successor compiler.  This is the base graph actually compatible
with the remaining carrier-indexed construction.

`RawCodedTruthCertificateMasterSuccessorBridge.v` gives the matching
nonstandard-safe successor interface.  A component compiler consumes the
current concrete master graph assertion and a coded PA proof of that exact
selected master, and must return six successor graph witnesses together with
either common-context local proofs or an ordinary proof targeted at their
transparent master conjunction.  Both routes assemble the concrete package
successor while preventing an unrelated proof target or standard-only `BProv`
instance from entering the carrier-indexed step.

`RawCodedTruthCertificateMasterComponentProjection.v` opens an exact current
master certificate with checked And-elimination trees and recovers all six
component proofs in the certificate's original witnessed PA context.  Its
graph-facing theorem simultaneously exposes the six coordinates selected by
the concrete master graph.  This closes the current-package decomposition
seam needed by a staged successor compiler; it does not manufacture any next
field or merge independently chosen proof contexts.

`RawCodedDynamicTruthMasterSplicedSuccessorBridge.v` packages the remaining
successor obligation at the right abstraction boundary.  After projecting
the current master, a staged compiler receives its six selected codes and
common-context roots and must return five positive predecessor-graph
witnesses, the next compact target, and six next roots in one honestly chosen
context.  The bridge applies all five splice successor equations and yields
the exact public master-package successor callback.  It performs no positive
field construction itself.

`RawCodedTruthCertificateMasterFixedHelperExtension.v` lets that staged
compiler add one fixed ordinary PA helper without breaking the shared-context
invariant.  It compiles the helper above the current witnessed PA base, uses
the one selected finite axiom prefix to transplant all six existing roots,
and returns the original six proofs plus the helper proof in literally one
extended witnessed context.  This is directly applicable to fixed lemmas
such as the native quantifier-free branch collision.

`RawCodedTruthCertificateMasterQFHelperExtension.v` performs that concrete
specialization.  Its seventh root concludes the literal native Ex8 QF/QF
collision code, and its public theorem needs no abstract template translation
parameter.  A represented zero-term trace and bottom fallback for opaque
template atoms construct a PA-agreeing structural translation internally;
ordinary embedded PA syntax never visits either fallback case.  Thus every
six-field common-context package can be extended with the proved QF helper
while retaining one exact synchronized witnessed context for all seven
roots.

`RawCodedTruthCertificateMasterFixedHelperBatchExtension.v` generalizes that
operation to an ordered finite batch of fixed ordinary PA theorems.  Each
dependent batch entry carries the proof of its own formula.  When compiling a
new entry chooses a finite axiom prefix, the construction transplants all six
master roots and every earlier helper root through that one exact prefix, so
the final family has one root per helper and one literal synchronized context
for the entire package.  A concrete first batch contains the unconditional QF
collision and both conditional implication cells; it deliberately does not
discharge their predecessor-state premise.

`RawCodedTruthCertificateMasterCollisionHelperBatch.v` expands that concrete
prefix to all twenty-one collision theorems currently ready for common-context
use: QF/QF, the two conditional implication cells, the conditional And/Or
cells, and the sixteen lower-independent constructor cells.  A generic map
lemma identifies every translated target with its ordinary PA quotation, and
the batch theorem places all twenty-one helper roots beside the six current
master roots in one literal witnessed context.  The count is intentionally
not forty-two: the conditional antecedents, carrier-sensitive binder cells,
and mixed QF/non-QF cells remain separate proof-producing obligations.

`RawCodedTruthCertificateMasterBinderPrincipalHelperBatch.v` appends the
eight fixed constructor facts needed by the carrier-sensitive binder cells to
that synchronized helper family.  The resulting twenty-nine roots share the
same witnessed context as all six master fields and have quotation-aligned
target codes.  The final eight roots are deliberately principal collision
facts rather than completed matrix cells: each still needs a compiler that
projects its opaque Sigma-All or Pi-Ex branch to the corresponding principal
constructor before the fixed fact can be applied.

`RawCodedTruthCertificateConcreteEndpoint.v` connects that successor bridge,
the zero bridge, the concrete assembler, and the generic PA-internal
induction.  Its single remaining all-model premise is exactly the five-field
zero component package plus either checked component-successor interface.
Discharging that premise yields the literal compact `BProv` theorem; no
additional graph decomposition, induction, projection, or completeness seam
remains after it.

`CompactPAUniformProvabilityTightness.v` still proves that the compact selector
successor is equivalent to the requested object theorem, so only a concrete
proof-producing construction can close the endpoint.
`RawCodedPAInternalizedUniversalInstance.v` remains available for fixed
universally quantified helper theorems: it internalizes one object theorem by
D1 and instantiates it at an arbitrary, possibly nonstandard, carrier element.

What blocks the remaining work is recorded in the Coq sources themselves.  The
beta-coded support certificate `RawProofRuleCoverageWithSupport` is keyed on
node *code values*, and every node code stores its own context, so changing a
context changes every code: support cannot be transported, and re-indexing it
would be the very map one is constructing.  That is not fatal, because the
constructor-level coverage lemmas already build a parent's coverage from its
children's, so a transplanted tree re-derives coverage bottom-up.  The
transplant statement is indexed by an insertion *depth* that is itself a model
element, since a nonstandard proof code may have nonstandard nesting depth.

`RawCodedContextInsert.v` supplies that missing relation.  Insertion at a
carrier-valued depth is stated pointwise against the two head tables, exactly
as `RawContextShiftRows` is, so nothing is decoded and no host-language
recursion appears: rows below the insertion point are copied, the point itself
carries the new formula, and rows from the point on move up one index.  The
relation is a genuine PA formula with exact arbitrary-raw-model semantics,
realizability transports in both directions, and the target is recorded as
exactly one longer than the source — the fact that distinguishes insertion from
shift, whose two traversals share one bound.  The context layer is complete:
insertion at depth zero is the single cons, the successor clause pushes an
insertion underneath one more list node, and both membership transports are
proved — the inserted formula belongs to the target, and so does every member
of the source.  The representation layer is axiom-free; only the construction
and transport theorems use classical logic.  Insertion is deliberately *not*
proved
functional: `RawContextShift` is not functional anywhere in this development
either, and its consumers use it existentially.

`RawCodedAdditionLaws.v` supplies the small arithmetic and order facts these
clauses need — both additive identities, `0 < succ b`, successor reflection for
the order, and the lt-then-le step in the form the descent consumes, so the
additive definition of the order is never unfolded at the use sites.  The left
identity needs no definable induction, since raw addition is already known to be
commutative.

The corrected Coq interfaces stay on the safe side of Gödel's second theorem:
every obligation asks for a proof *code*, never for uniform truth of a
dynamic-soundness statement.  The header of
`RawCodedRestrictedPADynamicSoundnessInductionData.v` records the latter dead
end explicitly.

## Implementation checklist

The numeralwise theorem is complete in both ports, and the uniform sentence is
complete in Lean.  Unchecked items below include the remaining constructive
Rocq/Coq compiler work for the uniform sentence.

- [x] Instantiate the existing Lean and Coq PA/HF formula and proof datatypes
  with independent restricted-proof wrappers.
- [x] Define mutually recursive syntactic `Sigma`/`Pi` polarity ranks in the
  phase-one host syntax.
- [x] Require the phase-one bound at every formula occurrence.
- [x] Add faithful `Type`-valued proof trees, erasure/completeness,
  monotonicity, and metatheoretic cofinality in both ports.
- [x] Prove conclusion-only collapse and external standard-model consistency
  of the restricted PA calculus without a separate consistency hypothesis.
- [ ] Prove and audit the exact relationship between the phase-one rank pair
  and the foundation library's typed `Sigma_n`/`Pi_n` hierarchy, including the
  treatment of bounded quantifiers.
- [x] In Lean, define a Delta-one code-level hierarchy bound over Foundation
  codes and prove exact quotation correctness for its NNF syntax.
- [ ] Internalize the Rocq code-level hierarchy computation in arbitrary PA
  models and complete the cross-syntax/typed-hierarchy correspondence.
- [x] In Rocq/Coq, define transparent term/formula-code constructors and prove
  exact local Sigma/Pi rank-step semantics over arbitrary raw-model elements.
- [x] In Rocq/Coq, prove every local Sigma/Pi rank equation functional.
- [x] In Rocq/Coq, prove PA injectivity of the polynomial pairing constructor.
- [x] Assemble the local rank rows into a synchronized model-internal global
  traversal, prove exact raw-model semantics, and prove soundness and
  functionality on standard quotations.
- [x] Prove cross-certificate functionality of the rank traversal for
  arbitrary nonstandard roots by PA induction and close it into an
  object-level PA theorem.
- [x] Prove model-internal realization/totality of the rank traversal on an
  independently characterized domain of arbitrary nonstandard well-formed
  formula codes.
- [ ] Prove closure of the code-level bound under every syntactic operation
  used by the proof calculus: negation, shift, bound-variable opening,
  substitution, universal closure, and formation/inversion of principal
  formulae.
- [x] In Lean, prove nonstandard-code negation, shift, substitution, and
  free-variable-opening preservation for the coded hierarchy rank.
- [x] In Lean, split the minimum-based bound into nonstandard-code Sigma- and
  Pi-oriented domains with exact constructor and polarity-switching laws.
- [x] In Lean, define the all-occurrences restricted derivation predicate over
  Foundation's actual Gödel coding and prove it Delta-one, with Sigma-one
  restricted provability and Pi-one restricted consistency.
- [x] Build the corresponding arbitrary-model restricted derivation predicate
  in Rocq/Coq.
- [x] In Rocq/Coq, expose all 17 proof-code constructors as transparent PA
  terms, prove their exact arbitrary-model semantics, and prove standard
  quotation agreement.
- [x] In Rocq/Coq, prove that every premise field of all 14 recursive proof
  constructors is strictly smaller than its parent code, and close the
  uniform descent formula into an object-level PA theorem.
- [x] Assemble the local proof constructors into an honest beta-supported
  traversal, prove child-certificate extraction and cross-certificate closure,
  and close constructor-occurrence totality into PA.
- [x] Validate every inference rule and its context/conclusion endpoints on
  arbitrary nonstandard proof codes.
- [x] Formalize coded environments and term evaluation, including totality and
  substitution lemmas in PA.
- [x] In Rocq/Coq, formalize beta-coded environments with functional lookup and
  PA-provable binder extension through arbitrary nonstandard prefixes.
- [x] In Rocq/Coq, arithmetize canonical context-list traversal and membership
  with exact arbitrary-model semantics and no external decoding.
- [x] In Rocq/Coq, define exact local coded-term evaluation rows for every
  arithmetic term constructor over arbitrary raw-model elements.
- [x] In Rocq/Coq, prove full functionality of the unified local term row,
  including constructor disjointness and independently chosen witnesses.
- [x] In Rocq/Coq, define a global supported beta-table term-evaluation
  certificate and prove cross-certificate value functionality by PA induction.
- [x] In Rocq/Coq, realize term-evaluation certificates for every standard
  quoted term, including two-term certificates over one shared assignment.
- [x] In Rocq/Coq, characterize model-internal term syntax and carry out the
  full PA-inductive construction of its value table from an explicit
  fixed-step beta-capacity premise.
- [x] Prove model-internal realization/totality of term-evaluation certificates
  for arbitrary nonstandard well-formed term codes by a step-parametric
  capacity trace and PA induction, discharging the beta-capacity premise.
- [x] In Rocq/Coq, define transparent local rank-zero truth rows for atoms and
  every Boolean constructor, with exact arbitrary-model truth tables.
- [x] In Rocq/Coq, prove the unified local rank-zero truth row functional.
- [x] In Rocq/Coq, build a global supported rank-zero truth certificate, prove
  cross-certificate functionality by PA induction, and close functionality
  into an object-level PA theorem.
- [x] In Rocq/Coq, realize that certificate on every standard
  quantifier-free quotation and prove exact one/zero semantic adequacy.
- [x] In Rocq/Coq, construct rank-zero truth tables by PA induction through
  arbitrary nonstandard quantifier-free syntax bounds and discharge their
  truth-bit beta capacity internally.
- [x] Prove model-internal realization/totality of rank-zero truth certificates
  for arbitrary nonstandard admissible formula codes and assignments, discharge
  equality-atom term capacity, and close totality into an object-level PA
  theorem.
- [x] In Rocq/Coq, define externally indexed local Sigma-truth and Pi-falsity
  formulae with exact arbitrary-model Boolean and quantifier rows, including
  correctly scoped opposite-polarity binder complements.
- [x] In Rocq/Coq, express the all-occurrences quantifier-group restriction
  over every head of an arbitrary nonstandard context traversal.
- [x] In Rocq/Coq, prove model-internal empty/cons context realization,
  membership introduction, and preservation of all-occurrences boundedness.
- [x] Assemble the Rocq/Coq fixed-level rows into globally closed nonstandard
  truth tables and prove their Tarski soundness interface.
- [x] In Lean, construct represented coded term evaluation and the rank-zero
  partial-truth evaluator with atomic and Boolean clauses.
- [x] In Lean, prove internal term shift/substitution transport and the
  structural/Boolean rank-zero Tarski interface on nonstandard codes.
- [x] In Lean, construct externally indexed fixed-level Sigma/Pi satisfaction
  predicates over nonstandard codes and prove hierarchy definability,
  oriented Boolean/quantifier clauses, and polarity changes at quantifier
  heads.
- [x] Complete polarity coherence, negation, and semantic transport for Lean
  fixed-level truth, including nonstandard shift and simultaneous
  substitution environments.
- [x] In Lean, generalize arithmetized fixed-point induction from level-one
  invariants to every externally fixed positive hierarchy level and specialize
  it to models of full PA.
- [x] Build or port the corresponding coded-derivation induction machinery in
  Rocq/Coq.
- [x] In Rocq/Coq, construct a transparent canonical Minsky-trace formula for
  the executable checker and prove exact standard-natural compiler agreement.
- [ ] Prove the canonical trace checker's bounded-proof soundness in every raw
  PA model, including nonstandard trace lengths and formula/proof codes.
- [x] In Lean, prove soundness of every rank-zero logical inference for
  arbitrary nonstandard restricted-derivation codes, conditional on the exact
  theory-axiom truth premise.
- [x] Extend logical-inference soundness to every fixed external level,
  conditional on the exact internally recognized theory-axiom truth premise.
- [x] In Lean at rank zero, prove truth of all internally recognized PA-minus
  axioms and structurally exclude every induction-axiom code.
- [x] In Lean, generalize PA-minus and internally recognized induction-axiom
  truth to every fixed positive level, including nonstandard instances.
- [x] In Lean, define the fixed-external-`n` object sentence `Con_n(PA)` and
  prove its arbitrary-model representation theorem.
- [x] Define and represent the matching canonical object sentence in
  Rocq/Coq, with exact arbitrary-raw-model semantics and a conditional
  completeness reduction.
- [x] In Lean, construct and audit the checked rank-zero object derivation
  `PA |- Con_0(PA)`.
- [x] In Lean, construct for every external `n` a checked object-level
  derivation `PA |- Con_n(PA)`.
- [x] Construct the corresponding externally indexed object-level derivations
  in Rocq/Coq.
- [x] In Lean, add audits that print/check the assumptions of the final theorem
  and reject admissions, project-local axioms, or semantic soundness hypotheses
  at the headline boundary.
- [x] Add the corresponding final-theorem audit in Rocq/Coq.
- [x] Record parity explicitly: theorem statements and mathematical coding
  contracts must coincide even when the concrete Gödel encodings differ.
- [x] In Lean, construct the model-indexed dynamic truth-certificate family,
  its `Sigma`-one master-code graph, its typed base certificate, and a
  dependency-ordered successor step at every model element, including the
  separate base-index productions forced by the internal numeral convention.
- [x] In Lean, assemble the staged successor, build the model-internal proof
  selector, and derive the unconditional object theorem
  `PA |- forall n, Prov_PA(code(Con_n(PA)))` with an audit of its assumptions.
- [x] In Rocq/Coq, prove the tightness equivalences showing the reduction
  targets are equivalent to the uniform object theorem, so that only a
  construction — never a further reduction — can close it.
- [x] In Rocq/Coq, build and verify the internalization engine: one fixed
  universally quantified object theorem, internalized by D1 and instantiated
  by internal universal elimination at an arbitrary carrier element.
- [x] In Rocq/Coq, record the historical reduction to single-cons transplant
  plus an exact-context dynamic-soundness base proof, and identify why those
  two unguarded premises are not suitable construction targets.
- [x] In Rocq/Coq, define the represented context-insertion-at-depth relation
  with exact arbitrary-model semantics, two-way realizability transport, the
  depth-zero and successor clauses, and both membership transports.
- [x] In Rocq/Coq, restate the transplant obligation over insertion-at-depth
  with the necessary atomic-adequacy guard, represent its strong
  below-proof-code invariant, run PA-definable induction, and re-derive the
  arbitrary-depth assumption-leaf row.
- [x] Add coverage-certified raw constructors for Or-I1, Or-I2, Or-E, Ex-I,
  Eq-Refl, and Eq-Elim, including exact endpoint and support-extension audits.
- [x] Prove the insertion/unit-shift commuting square at every carrier-valued
  depth and assemble all seventeen constructor cases into the represented
  proof-code induction.
- [x] Prove arbitrary model-coded term-shift totality and reduce adequate
  formula unit-shift totality to the exact nonstandard trace-composition
  interface `RawCodedFormulaShiftCompositional`.
- [x] Prove `RawCodedFormulaShiftCompositional` by synchronized beta-table
  concatenation and parent append; this makes the guarded arbitrary-depth
  transplant unconditional.
- [x] Replace the impossible exact-context base seam by a growing witnessed-base
  open compiler, verify its bridge to certificate successor, and prove the
  structural final projection from a six-field master PA certificate.
- [x] Represent the structural six-field conjunction graph and its direct
  PA-provability package, with exact arbitrary-model semantics and forced
  final-field extraction.
- [x] Build the generic PA-internal master-package induction and its bridge to
  the exact compact uniform theorem from graph decomposition, base, and
  successor callbacks.
- [x] Add an honest extended proof-template syntax and compile every one of
  its seventeen natural-deduction constructors to exact coverage-certified
  raw PA local proofs under an abstract model-coded specialization.
- [ ] Port the six-field dynamic-truth master-code graph, checked base
  certificate, and staged proof-code successor from Lean to Rocq/Coq; apply
  internal PA induction and the final projection to make the uniform object
  theorem unconditional.

## Building the final theorem

From the repository root, the Lean library is registered as
`BoundedPAConsistency`:

```bash
lake build BoundedPAConsistency.Basic BoundedPAConsistency.Internal \
  BoundedPAConsistency.CodedHierarchyAudit \
  BoundedPAConsistency.OrientedHierarchyAudit \
  BoundedPAConsistency.QuantifierFreeTruthAudit \
  BoundedPAConsistency.QuantifierFreeTarskiAudit \
  BoundedPAConsistency.QuantifierFreeTransportAudit \
  BoundedPAConsistency.QuantifierFreeSoundnessAudit \
  BoundedPAConsistency.TermEvaluationTransportAudit \
  BoundedPAConsistency.RestrictedDerivationAudit \
  BoundedPAConsistency.RestrictedConsistencyAudit \
  BoundedPAConsistency.FixedLevelPAAxiomsAudit \
  BoundedPAConsistency.Audit \
  BoundedPAConsistency
```

`BoundedPAConsistency.Audit` now also reports the assumptions of the uniform
object theorem.  To check that endpoint on its own, together with the
productions it rests on:

```bash
lake build BoundedPAConsistency.UniformInternalProvabilityTheoremAudit \
  BoundedPAConsistency.DynamicTruthStagedSuccessorAssemblyAudit \
  BoundedPAConsistency.DynamicTruthCrossLevelBaseRankProductionAudit \
  BoundedPAConsistency.DynamicTruthAxiomSoundnessBaseRankProductionAudit \
  BoundedPAConsistency.DynamicTruthAxiomSoundnessPositiveRankProductionAudit \
  BoundedPAConsistency.DynamicTruthRestrictedSoundnessProductionAudit
```

On a memory-constrained machine set `LEAN_NUM_THREADS=0` first; the generated
represented-syntax modules can make each concurrent `lean` worker consume
gigabytes.

The Rocq/Coq logical path is `BoundedPAConsistency`.  The root `_CoqProject`
registers both the implementation and audit; note that it also registers the
compact-selector, dynamic-soundness, and scope files, and that building any of
the checker-facing modules requires the
`lib/Coq-Library-Undecidability-current` submodule to be initialized.  The
final theorems can be checked directly against the already-built dependencies
with:

```bash
opam exec --switch=proofs-rocq92 -- rocq compile \
  -Q Logic/FirstOrder/Coq FirstOrder \
  -Q Logic/Interpretability/PAHF/Coq PAHF \
  -Q Logic/PeanoArithmetic/NotFinitelyAxiomatizable/Coq PAFiniteBasisReduction \
  -Q Logic/PeanoArithmetic/ListCoding/Coq PAListCoding \
  -Q Logic/PeanoArithmetic/BoundedConsistency/Coq BoundedPAConsistency \
  -Q lib/Coq-Library-Undecidability-current/theories Undecidability \
  Logic/PeanoArithmetic/BoundedConsistency/Coq/RawCodedRestrictedPAConsistencyTheorem.v

opam exec --switch=proofs-rocq92 -- rocq compile \
  -Q Logic/FirstOrder/Coq FirstOrder \
  -Q Logic/Interpretability/PAHF/Coq PAHF \
  -Q Logic/PeanoArithmetic/NotFinitelyAxiomatizable/Coq PAFiniteBasisReduction \
  -Q Logic/PeanoArithmetic/ListCoding/Coq PAListCoding \
  -Q Logic/PeanoArithmetic/BoundedConsistency/Coq BoundedPAConsistency \
  -Q lib/Coq-Library-Undecidability-current/theories Undecidability \
  Logic/PeanoArithmetic/BoundedConsistency/Coq/RawCodedRestrictedPAConsistencyTheoremAudit.v
```

The audit modules, rather than this README, are the authority for the exact
kernel assumptions and public theorem surface.
