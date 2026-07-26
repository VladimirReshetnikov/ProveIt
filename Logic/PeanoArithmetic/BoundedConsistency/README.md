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
`RawCodedPAProofOf` certificate.  For the positive local field,
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
never decoded.  `RawCodedTranslatedProofCompiler.v` provides the corresponding
homomorphic compiler for ordinary PA proof trees and will be used by the
lifted-PA axiom bridge.  `RawCodedTemplatePAEmbedding.v` makes that bridge
literal: it embeds all seventeen ordinary raw-proof constructors, proves
context/conclusion/validity preservation, and attaches the unchanged finite
list of witnessed ordinary PA axioms to the compiled template tree.  Opaque
template atoms therefore cannot leak into the PA axiom base.
`RawCodedTemplateLogicalSchemas.v` records the small
finite source trees needed by the dynamic fields—conjunction projection and
introduction, existential projection, and universal specialization followed
by modus ponens—so their model-coded proofs do not rely on an unexposed
semantic-completeness step.  `RawCodedTemplateProjectionSchemas.v` extends
those atoms with transparent arbitrary conjunction selection/repacking,
witness-preserving existential towers, universal closure, and the exact
two-universal/five-existential projection used by the dynamic universal-leaf
law.  `RawCodedTemplateClosedProofCompilation.v` packages any closed compiled
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
`RawCodedTemplateNumeralParameters.v` separately builds exact term shift and
opening traces for named parameters represented by model-internal numeral
codes.  `RawCodedTemplateNumeralTermSyntax.v` uses the zero-shift instance of
those traces to place every interpreted template term, including renamed and
opened terms, in the honest syntax domain required by opaque selectors.
`RawCodedTemplateTernaryApplication.v` supplies the honest
five-trace application relation for a possibly nonstandard ternary formula,
proves totality and preservation of atomic adequacy on represented term
syntax, and names the exact shift/opening commuting diagrams required at an
opaque leaf.  Those diagrams are intentionally left as contracts: proving
them needs cross-trace substitution/shift interchange, which the current raw
operation library does not yet expose.  What remains at this layer is that
interchange theorem; atomic adequacy alone is intentionally not mistaken for
the missing scope-sensitive operation contract.

`RawCodedTernaryPredicateRootClosure.v` strengthens the standard scoped
substitution identity from numeral replacements to every honestly
represented, possibly nonstandard term.  Represented shift totality chooses
the unused lifted replacement; a structural diagonal trace then proves that
any quoted ternary-scoped formula is fixed by both the depth-three shift and
depth-three substitution operations.  Applying this interface to the exact
row-aligned global rank-zero quotations,
`RawCodedDynamicTruthGlobalBaseRootClosure.v` proves root closure for both
outputs of the paired global base graph.  The corresponding preservation
theorem for the nonstandard successor orbit is still required before the
opaque application laws are available at every carrier level.

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

`RawCodedDynamicTruthUniversalLeafSourceTemplate.v` records the actual Rocq
Sigma successor-row syntax: eight existential table witnesses around a domain
check and a seven-way disjunction, whose final branch contains the opaque
lower-Pi application.  It supplies an honest eight-witness projection from an
explicitly restricted universal row and proves in the kernel that the older
five-witness, conjunction-only candidate is not this table row.  Concrete
instantiation therefore cannot silently identify the Lean-shaped schema with
Rocq's different encoding.

`RawCodedDynamicTruthTemplateNumeralParameters.v` instantiates the source
template's designated lower- and upper-level names at arbitrary carrier
elements.  Represented numeral-code totality selects both possibly
nonstandard numeral terms, and the package exposes their exact validity plus
the direct translator's complete term shift/open fields.  Only the separate
opaque-predicate operation traces remain to form the full direct input.

`RawCodedDynamicTruthUniversalLeafProofCompilation.v` sends the honest
eight-witness restricted projection through that direct relational
translator and the closed-template packer.  It produces an exact ordinary PA
certificate both before and after the native thirteen-variable row
environment is universally closed.  Code-identification equalities remain
separate from the operational opaque traces, and the endpoint deliberately
continues to name the restricted universal branch rather than the full
seven-way disjunction.

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

`RawCodedTruthCertificateMasterSuccessorBridge.v` gives the matching
nonstandard-safe successor interface.  A component compiler consumes the
current concrete master graph assertion and a coded PA proof of that exact
selected master, and must return six successor graph witnesses together with
either common-context local proofs or an ordinary proof targeted at their
transparent master conjunction.  Both routes assemble the concrete package
successor while preventing an unrelated proof target or standard-only `BProv`
instance from entering the carrier-indexed step.

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
