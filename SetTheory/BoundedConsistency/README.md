# Bounded-complexity consistency for ZFC

This project targets the **numeralwise consistency scheme** for Zermelo–Fraenkel
set theory with choice: for every natural number `n` chosen in the metatheory,
ZFC proves that no ZFC derivation in which every formula occurrence has at most
`n` quantifier groups derives falsity.

```text
for each metatheoretic n : Nat, construct a derivation ZFC |- Con_n(ZFC).
```

As in the companion project
[`Logic/PeanoArithmetic/BoundedConsistency/`](../../Logic/PeanoArithmetic/BoundedConsistency/README.md),
the phrase “every formula occurrence” and the metatheoretic status of `n` are
part of the specification, not presentation.  The parameter is specialized by
the proof assistant before the resulting ZFC derivation is read; it must not be
strengthened to the single object-level assertion `ZFC |- forall n, Con_n(ZFC)`,
which would yield ordinary `Con(ZFC)` and contradict Gödel's second theorem.

> **Current status.**  Early, but past the first internal brick.  Phase one —
> the metatheoretic rank and restricted-derivation development — is complete and
> checked:
> `BoundedZFCConsistency.Basic` supplies the polarity ranks, the `Type`-valued
> proof-tree mirror with erasure and completeness, the every-occurrence rank,
> restricted provability with monotonicity and cofinality, and the
> conclusion-only collapse.  The axiom of choice is formalized, giving `ZFCax`,
> and `BoundedZFCConsistency.Coding` codes the syntax of `Form` inside an
> arbitrary model of ZF, with quotation proved injective.  Everything after that
> — “codes a formula” as an object-language predicate, coded derivations,
> internal satisfaction, formalized soundness, and reflection — is open.  The
> object-level theorem is **not** proved, and nothing in this project should be
> read as claiming `ZFC |- Con_n(ZFC)`.

## Why this is not a port of the PA project

The PA development proves its theorem by representing a partial truth predicate
*inside arithmetic*, over Gödel codes, in arbitrary nonstandard models of PA.
That machinery is arithmetic-specific and does not transfer.

Set theory admits a different and, for this purpose, more natural argument.  Two
routes are available:

1. **Reflection.**  For each metatheoretic `n`, ZFC proves that some `V_alpha`
   is a `Sigma_n`-elementary substructure of the universe (Levy reflection).
   Every axiom of ZFC that appears in a rank-`n`-bounded derivation is itself
   rank-bounded, hence true in `V_alpha`.  Since `V_alpha` is a *set* model,
   formalized soundness inside ZFC rules out a derivation of falsity.  This
   actually proves the stronger statement `Con(ZFC_{Sigma_n})` — consistency of
   the `Sigma_n` fragment as a theory, with *unrestricted* derivations — from
   which `Con_n(ZFC)` follows immediately, because a rank-bounded derivation
   uses only rank-bounded axioms.
2. **Partial satisfaction.**  Define, for fixed `n`, a ZFC formula that is a
   satisfaction predicate for coded formulas of rank at most `n` over the whole
   universe, prove its Tarski clauses and the truth of the rank-bounded ZFC
   axioms, and push it through the derivation by internal induction.  This is
   the direct analogue of the PA argument.

Route 1 was the intended one initially.  **The project has since switched to
route 2**, on the following reasoning.

Route 1 needs internal ordinals, transfinite recursion, the cumulative
hierarchy, and Powerset — none of which the current axiom bundle has — *and*
then still needs a `Sigma_n` truth predicate over the universe in order to state
`V_alpha ≺_{Sigma_n} V` uniformly in the infinitely many schema instances of
bounded rank.  Route 2 needs the truth predicate and nothing else.  The truth
predicate is therefore common to both routes, and everything route 1 adds on top
of it is avoidable.

Route 2 is also the architecture the repository's completed arithmetic project
uses: partial truth predicates indexed by an *external* level, defined by
recursion on that level rather than internally, so that no single formula
defines truth for all levels and Tarski's theorem is not threatened.

Because this syntax has no primitive bounded quantifier, the base case of the
hierarchy is quantifier-free truth rather than `Delta_0` truth, which makes it
simpler: atoms and Boolean combinations only.

Note the contrast with PA: for ZFC the all-occurrences restriction is *less*
load-bearing than it is for arithmetic, precisely because route 1 factors
through consistency of a fragment rather than through a restriction on
derivations.  The all-occurrences form is still what is stated and proved, since
it is the weaker and therefore safer reading.

## Base development

The project builds on the repository's own dependency-free first-order logic
rather than on a mathlib-backed library:

- [`Logic/FirstOrder/Lean`](../../Logic/FirstOrder/Lean) supplies `Form` — a
  purely relational language with `fMem` and `fEq` atoms and De Bruijn
  quantifiers — the 17-rule natural-deduction calculus `Prov`, satisfaction
  `Sat`, and Gödel completeness, including
  `godel_completeness_for_theories`, which is the bridge from “true in every
  model of the theory” to an object-level derivation.
- [`SetTheory/ZF/Lean`](../ZF/Lean) supplies the ZF axioms as formulas, the
  axiom set `ZFax`, provability `ZFprov`, the sentence theory `ZFax_s`,
  semantic bridges, and a substantial body of *internal* mathematics of an
  arbitrary model: set algebra, Kuratowski pairs, an internal omega with a
  definable-induction schema, and a finite-recursion theorem.

That internal-mathematics layer matters: coded syntax inside the object theory
lives in the hereditarily finite sets, and internal recursion is what makes a
satisfaction predicate definable.

### The alternative base, and why it was not chosen

The vendored Foundation library also formalizes set theory, in
`lib/FormalizedFormalLogic-Foundation/Foundation/FirstOrder/SetTheory/`: the
axioms including the separation and replacement schemas and choice, the theories
`𝗭`, `𝗭𝗙`, `𝗭𝗖`, `𝗭𝗙𝗖`, internal ordinals, transitive models,
Löwenheim–Skolem, and the `Universe` model with `models_zfc`.  It is
mathlib-backed and is the base the arithmetic project uses.

This project nevertheless builds on the repository's own first-order logic,
because that is where phase one's calculus, the ZF axioms as `Form`, and the
internal model mathematics already live, and because its builds are light.  The
choice is not irrevocable: the reflection layer is the point at which
Foundation's ordinals and cumulative hierarchy would start to pay for
themselves, and switching bases there — or transporting results along a language
isomorphism — should be reconsidered rather than assumed away.

## Phase one: the metatheoretic restriction

`BoundedZFCConsistency.Basic` fixes the polarity-aware syntactic meaning of “at
most `n` quantifier groups” and applies it to every judgement node of a
derivation.  It separates the four notions that are easy to conflate: the
ordinary proof relation; a data-carrying proof tree whose numeric rank bounds
every formula occurrence; the resulting restricted-provability relation; and any
semantic consequence of it.

Because `Prov` lives in `Prop`, proof irrelevance prevents the kernel from
computing a numeric rank by inspecting an ordinary derivation, so the module
mirrors the 17 rules in a `Type`-valued `ProvTree`.  Erasure maps a tree to an
ordinary proof and ordinary derivability propositionally supplies a tree, so the
mirror is a faithful presentation of the same calculus, not an added proof
system.

**A deliberate deviation from the Levy hierarchy.**  This `Form` has no
primitive bounded quantifier, so the rank counts every quantifier, including
those of the form `forall x in y`.  The rank is therefore strictly finer than
the Levy hierarchy.  The consequence is that each individual `Con_n` proved here
is *weaker* than its Levy-indexed counterpart — fewer derivations are
rank-bounded — while the family still exhausts every derivation as `n` grows,
which is what the intended theorem requires.  Closing that gap would mean either
adding bounded quantifiers to the language or proving a normalization theorem
relating the two ranks; neither is attempted.

**No external consistency claim — but not because none is possible.**  The PA
project's phase one rules out a restricted derivation of falsity outright, using
the standard model of arithmetic.  Phase one here proves no such thing, and the
modules say so.

The reason is *not* that external consistency of ZFC is unavailable in Lean.  It
is available: Lean's type theory with universes is stronger than ZFC and proves
`Con(ZFC)` outright, and the vendored Foundation library already carries a
witness — `Foundation/FirstOrder/SetTheory/Universe.lean` constructs a `Universe`
type and proves `Universe ⊧* 𝗭𝗙𝗖`.  What is missing is only a bridge: that model
inhabits Foundation's own `SetTheory` language, whereas this project is built on
the repository's dependency-free `Form`.  Constructing a model of this `ZFax` in
Lean, or transporting Foundation's along a language isomorphism, is a separate
and self-contained task.

Note also what such a theorem would and would not be worth.  Unlike the
arithmetic case, external consistency here is a statement about Lean's strength
rather than a fact provable in the object theory, and it is *not* a step toward
the target: the intended theorem is proved inside ZFC, by reflection, and never
appeals to an external model.

## Gödel-II boundary

The target does not contradict Gödel's second incompleteness theorem, for the
same three reasons as in the arithmetic case:

- each metatheoretic `n` is fixed outside ZFC, and its reflection instance or
  partial truth predicate is a separate finite construction;
- no single `Con_n(ZFC)` rules out ZFC derivations using formulas of greater
  complexity;
- there is no claim that ZFC proves the universal closure over all `n`, which
  would yield ordinary `Con(ZFC)`.

## Implementation checklist

- [x] Define polarity-aware `sigmaRank`/`piRank` on `Form`, `quantifierGroups`,
  and `QuantifierBounded`; prove invariance under renaming.
- [x] Mirror the 17 proof rules in a `Type`-valued `ProvTree` with erasure and
  completeness, and define an occurrence rank covering conclusions, contexts,
  formula-valued rule parameters, and premises.
- [x] Define `ProofAllBounded`, `RestrictedProv`, and theory-relative
  `RestrictedBProv`; prove monotonicity, metatheoretic cofinality, and the
  conclusion-only collapse.
- [x] Extend the ZF axiom set with a choice axiom, giving `ZFCax`/`ZFCax_s`
  together with its semantic bridge.
- [x] Record the model-relative consistency statements for the restricted
  calculus, keeping the model hypothesis explicit.
- [x] Code the syntax of `Form` inside the object theory as hereditarily finite
  sets: internal numerals in omega, a tagged Kuratowski-pair quotation map, and
  injectivity of quotation.
- [x] Express “codes a formula” as a `Form` by the intersection presentation of
  an inductive definition, with a full satisfaction spec, quotation soundness,
  and a definability-relative induction principle.
- [x] Construct a formula-closed set, discharging the hypothesis that both
  induction forms carried, and restate them unconditionally.
- [x] Define the polarity ranks on codes internally, prove them total and
  single-valued, and prove they agree with the metatheoretic ranks on
  quotations.
- [x] Define the all-occurrences bound on coded derivations, and prove it really
  does bound every formula-valued rule parameter and not merely conclusions and
  contexts.
- [x] Express “codes a ZFC axiom” internally — the seven fixed axioms by their
  quotations, and the Separation and Replacement schemas by an existential over
  the coded formula constructors.
- [x] Define the object-level sentence `Con_n(ZFC)` for each metatheoretic `n`,
  over contexts consisting of axiom codes, and prove its arbitrary-model
  characterization.  (A first attempt assembled the sentence over the *empty*
  context; see the warning below.)
- [x] Reduce the target to a single semantic obligation via
  `godel_completeness_for_theories`.
- [x] Supply a step-parametric recursion theorem over internal omega,
  generalizing the ZF development's `gstep`-specific finite recursion, together
  with internal linearity of omega and an internal function/application
  interface.  This is the enabling tool for everything below it: satisfaction
  must be defined by recursion on formula codes, which may be nonstandard, so
  the recursion has to be internal.
- [x] Formalize satisfaction for set-sized structures inside ZFC as a
  certificate relation: internal environments with binder extension, the local
  Tarski step as a `Form` with an exact satisfaction spec, and single-valuedness
  proved by induction over codes.
- [x] Prove totality of the satisfaction certificates and derive the internal
  satisfaction relation `SatIn` together with its Tarski clauses for atoms,
  falsity, the three connectives, and both quantifiers.
- [x] Define internal renaming of coded formulas along a coded variable map,
  with totality, single-valuedness, and agreement with the metatheoretic
  renaming on quotations.
- [x] Prove the substitution lemma for internal satisfaction: satisfaction of a
  renamed code equals satisfaction of the original under the permuted
  environment.
- [x] Code contexts and derivations inside the object theory, mirroring the 17
  rules, with derivations ranked so that premises are cited at strictly smaller
  internal rank.
- [x] Formalize soundness of the 17-rule calculus with respect to internal set
  models, including the eigenvariable rules via the shifted-context operation.
The remaining items follow route 2, partial satisfaction over the universe.  The
reflection route's own entries — the Levy scheme and `Con(ZFC_{Sigma_n})` — are
dropped, since route 2 reaches the target without a cumulative hierarchy; see
“Why this is not a port of the PA project” above.

- [x] Define quantifier-free truth over the *universe* — the base case of the
  externally indexed hierarchy, and simpler than `Delta_0` truth because this
  syntax has no primitive bounded quantifier — with its Tarski clauses and
  agreement with the metatheory on quotations.
- [x] Define the externally indexed `Sigma`/`Pi` partial truth predicates over
  the universe by recursion on the external level, with their Tarski clauses and
  the polarity switches at quantifier heads.
- [x] Prove the substitution lemmas at a fixed level, for both polarities, with
  the shift and instantiation corollaries.
- [ ] Prove the level-collapse theorem — that truth at level `n+1` on a code
  bounded at `n` already holds at level `n`.  This closes the elimination halves
  of the two polarity-switch rows, upgrades `Pi` monotonicity, and — as the
  soundness brick discovered — is on the **critical path**, since two-valuedness
  is what implication elimination needs.
- [ ] Prove every internal ZFC axiom code of rank at most `n` true at level `n`,
  including the nonstandard schema instances the internal axiom set contains.
- [ ] Push partial truth through a bounded coded derivation and conclude that
  falsity is not derivable, discharging the single remaining obligation
  `zfcprov_conZFCForm_of_no_bounded_refutation`.
- [ ] Assemble the object-level derivation `ZFC |- Con_n(ZFC)` for every
  metatheoretic `n`, and audit its assumptions.

## The internal work is over a weaker theory than ZF, and reflection will notice

`ZFAxioms`, the semantic bundle every internal result is relative to, is
Extensionality, Separation, Pairing, Union, Infinity and Replacement.  It has
**no Powerset and no Foundation**.

For everything built so far this is a strength rather than a limitation: coded
syntax, the code predicate, the recursion theorem, internal satisfaction, and
coded renaming all hold in models of that weaker theory.

It would have become a real dependency under the reflection route, whose
`V_alpha` needs Powerset and whose rank arguments want Foundation.  That is one
of the reasons the project switched to partial satisfaction over the universe,
which needs neither: the remaining work can stay over the same weak bundle that
everything so far is proved against.

Should a later brick want the stronger bundle anyway, the axioms are already
present as `Form`s in the ZF development, including `Pow_form` and `Reg_form`,
and a model of the sealed sentence theory satisfies them; what is missing is
only the semantic bundle and its extraction lemma, in the style of
`zfAxioms_of_zfcModel`.

One consequence already showed up.  The intersection presentation used for the
code predicate does *not* transfer to renaming, even though the renaming clauses
are monotone: its induction principle says nothing until some closed set exists,
and a set closed under the renaming clauses would have to record a triple for
every variable map — and the variable maps are subsets of `omega x omega`, which
without Powerset need not form a set.  Renaming therefore uses the certificate
architecture instead, where it is strictly cheaper than for satisfaction: no
clause quantifies over a carrier, so a compound certificate is a union plus one
new triple, and neither totality nor single-valuedness needs the
uniform-over-a-set strengthening.

## A near miss: the sentence over the empty context

`BoundedZFCConsistency.CodedRank` builds the internal rank machinery and then
assembles a sentence from it.  That sentence, `logicConForm n`, constrains the
derivation's context to be *empty*, so it expresses bounded consistency of pure
first-order logic — not of ZFC.  It is deliberately named for what it is.

Two things make the distinction worth stating loudly rather than quietly fixing.
First, `logicConForm n` is already provable: internal soundness rules out any
coded derivation of falsity from the empty context as soon as the model carries
an internal set structure, and a trivial one always does.  A sentence that is
provable for free is not the target — `Con_n(ZFC)` is not provable for free, and
if it looked as though it were, something would be wrong.  Second, the gap is
precisely one missing predicate: `Con_n(ZFC)` quantifies over derivations whose
context consists of codes of ZFC axioms of rank at most `n`, and nothing yet
expresses “codes a ZFC axiom” internally.  That predicate has to recognize the
six fixed axioms by their quotations and the Separation and Replacement schemas
by an existential over the coded formula constructors.

Everything else in that module — the internal ranks, their agreement with the
metatheoretic ranks on quotations, the all-occurrences bound, and the endpoint
bridge through completeness — is exactly what the real sentence needs, and is
unaffected.

`BoundedZFCConsistency.AxiomCode` closes the gap.  Its `conZFCForm n` quantifies
over the derivation's context and constrains every member to be an axiom code,
so it is the intended statement.  The internal axiom-code predicate recognizes
the seven fixed axioms by their quotations and the two schemas by an existential
over the internal code predicate.

Note what that existential means, since it is deliberate: because the code
predicate's atomic clauses range over the model's own omega, a nonstandard model
contains Separation and Replacement codes that quote no external instance.  The
internal axiom set is therefore properly larger than the quotations of the
external one, and only the direction `ZFCax f → IsZFCAxiomCode (formCode f)` is
proved.  The converse is false and is not attempted.  This is not a weakness of
the statement but a requirement on it: internal soundness will have to be
applied to the internal axiom set, nonstandard instances included, or the
argument would not cover the derivations `Con_n` actually quantifies over.

## Where the remaining work is now concentrated

`BoundedZFCConsistency.LevelSoundness` proves the fixed-level substitution
lemmas and then names what is left, rather than assuming it.  Three obligations
remain, and they are not independent:

- `LevelSoundnessAt` — that a bounded coded derivation transports level-`n+1`
  truth from its context to its conclusion.  Blocked on the next item.
- `LevelTwoValuedAt` — that the two polarities agree on the codes a bounded
  derivation can mention.  This follows from the level-collapse theorem.
- `AxiomCodesTrueAt` — that every internal ZFC axiom code of bounded complexity
  is true at the level.  This is where the content of the axioms finally enters,
  and it is independent of the other two.

The obstruction in the first is sharp and worth recording, because it says the
level-collapse theorem is not optional.  Implication elimination has
`SigmaTrue (n+1)` of an implication together with `SigmaTrue (n+1)` of its
antecedent; the Tarski clause turns the former into a disjunction whose left
half is `PiFalse (n+1)` of the antecedent, and only two-valuedness discharges
it.  Reading truth as `PiTrue` throughout moves the same obligation to the other
side of that rule, and reading it as the conjunction of both polarities moves it
to disjunction elimination.  No formulation of the rule avoids it.

## The whole remaining obligation, in one statement

With that sentence in place the project reduces to a single hypothesis:

```text
for every model of the ZF axioms, there is no coded derivation of falsity
from a context of axiom codes, with every occurrence bounded by the numeral
of n.
```

`zfcprov_conZFCForm_of_no_bounded_refutation` turns exactly that into
`ZFC |- Con_n(ZFC)` through Gödel completeness.  Discharging it is the
reflection layer's job, and is the only mathematics the project still owes.

## The truth hierarchy: certificates within a level, recursion across levels

The two mechanisms this project uses for recursion are combined in the fixed-level
truth predicates, and the split is forced.

*Across* levels the recursion is external: the level is a metatheoretic natural
consumed outside the object language, so each level is a separate definition
producing a separate, strictly larger formula — the successor level's formula
textually embeds its predecessor's.  The level never appears as a de Bruijn slot
and never as an element of the model.  That is what keeps Tarski's theorem
satisfied, and it is visible in the types rather than asserted in a comment.

*Within* a level the recursion over a possibly nonstandard code is carried by an
internal certificate, exactly as for the quantifier-free base and for internal
satisfaction.  External recursion cannot reach inside a nonstandard code.

One asymmetry in the step table is worth recording, because it looks arbitrary
and is not.  A record is a code, an environment and a bit, with the bit read as
a polarity: one means Sigma-true, zero means Pi-false.  The existential head is
certified by recording a *witness*; the universal head by recording a
*counterexample*.  The two polarity-switch rows go the other way and are guarded
by the oriented rank bounds.  A witness is a single element and can be recorded;
its absence is a statement about a proper class and cannot be.

## Why coded derivations carry a rank

A closure predicate — “this set is closed under the inference rules, and the
node in question belongs to it” — is the presentation that worked for the code
predicate and for renaming.  For derivations it is **unsound**, and the failure
is not subtle once seen.

Renaming and code formation are safe because every clause strictly decreases the
code, so closure plus inversion already pins the relation down.  Inference rules
move in both directions.  The three-element set containing `a`, `b` and their
conjunction is closed: each member is justified by the others through
conjunction introduction and the two eliminations.  Nothing in it need be
derivable.  A bare closure predicate would therefore prove everything.

Derivations are consequently certified with a **rank in the internal omega**,
every premise cited at a strictly smaller rank.  Well-foundedness of the
derivation then reduces to well-foundedness of membership on the von Neumann
naturals, which definable induction supplies and which holds of nonstandard
ranks too.

Two further asymmetries shaped the same module.  Context membership *is* safe
by certificates, because inversion comes free from tag disjointness — but it has
no descent principle, so a member of a coded context is not known to be a code,
and the shifted-context relation carries codehood of its source explicitly.  And
each derivation clause states codehood of the formulas it introduces as rule
parameters, because codehood of a compound does not yield codehood of its parts.

## How totality avoided a choice principle

The quantifier cases of totality look as though they need a certificate chosen
for each element of the carrier, collected by Replacement — and a *definable*
choice of certificate is not available.

The fix is to strengthen the induction hypothesis rather than to choose.  The
property carried through code induction is not “a certificate exists at this
environment” but “**one** certificate serves every environment in a given set”.
A quantifier case then applies the induction hypothesis exactly once, at the set
of environments extended by every carrier element, and never selects anything.
No choice principle is used at either level, and the resulting satisfaction
relation is genuinely a relation rather than a selected function.

Two smaller points fell out of the same proof.  Single-valuedness of subcode
bits is not needed for totality, because the Boolean clauses are existential in
the subbits — so the two halves of the satisfaction layer are independent.  And
`certificate_total` is stated over a set structure only because that is the
intended interface: the proof never uses it, since an empty carrier is settled
by the universal side of the quantifier clause.

## Two facts about the coded-syntax layer

Both are recorded in the modules and neither should be read away.

**The code predicate is not claimed to have the quoted formulas as its exact
extension.**  Quotation soundness — every externally quoted formula satisfies
the predicate — is proved.  The converse is *false* in nonstandard models and is
deliberately not attempted: the atomic clauses quantify over the model's own
omega, so a nonstandard model has code-like elements that are not quotations of
any external formula.  That is the intended behaviour, and it is exactly why the
eventual argument must be carried out inside the model rather than by external
recursion.

**The induction principles are relative to a definability witness.**  Separation
carves out subsets by a `Form` with parameters, not by an arbitrary Lean
predicate, so an induction principle takes its property as a formula together
with an environment.  This is intrinsic, not an artefact: separation for
arbitrary Lean predicates is not available and should not be.

They no longer carry an existence hypothesis.  With no formula-closed set the
intersection would be vacuous and no induction principle could hold, so
`BoundedZFCConsistency.FormulaClosedSet` constructs one and restates both forms
unconditionally.  The construction is worth recording, because the obvious route
fails: taking a union of stages `C_0 = omega`, `C_{k+1} = C_k` plus its pairs
does *not* give closure under a binary operation, since `a` and `b` may enter at
different stages and directedness of the stages needs internal linearity of
omega, which the ZF development does not have.  Instead the closure operator is
applied as a black box to the unary step `v |-> v` union its pair image, and the
resulting junk is removed by the same intersection presentation used for the
code predicate.  That intersection is itself step-closed, hence least, so it
carries its own induction principle relative only to definability — and two
instances of it give directedness directly, with no stage recursion and no
internal ordinal arithmetic.

## Upstream lemmas this project needed

Two facts about the internal omega are proved locally in
`BoundedZFCConsistency.CodePredicate` but belong in `SetTheory/ZF/Lean/ZF/Zf.lean`
beside `omega_spec`:

- `inductiveV H (omegaV H)` — the internal omega is itself inductive;
- `mem n (omegaV H) ↔ ∀ c, inductiveV H c → mem n c` — the *pure* intersection
  characterization.

The second matters more than it looks.  `omega_spec` states the conjunctive form
`mem n (InfSet H) ∧ …`, whose first conjunct is redundant but drags the
choice-dependent term `InfSet H` — which has no defining formula — into any
rendering.  Without the pure form there is no way to write “is a natural number”
as a `Form` at all.  Moving both upstream is a small, safe refactor that was
left out of this project's commits only to avoid destabilizing the other
consumers of `ZF.Zf` late in a session.

`BoundedZFCConsistency.FormulaClosedSet` adds a third:

- a pair image, `∀ v, ∃ r, ∀ u, mem u r ↔ ∃ a b, mem a v ∧ mem b v ∧ u = kpair H a b`,

which belongs beside `kpair`.  Two further gaps were identified but deliberately
*not* filled, since the chosen construction avoids needing them:

Both of the remaining gaps are now supplied by
`BoundedZFCConsistency.OmegaRecursion`, and both belong upstream:

- a **step-parametric** finite recursion.  `Approx`, `Theta`, `Wimg`, and
  `ClosureFO_of_ZF` hard-code `gstep`; the parametrized development gives
  existence and uniqueness of the iteration sequence for any definable
  operation.  Upstream's own machinery is now an *instance* of it — instantiating
  the step at `gstep` discharges the graph hypothesis exactly — so roughly two
  hundred lines of `ZF.Zf` could be replaced by that instantiation once the
  module moves upstream.
- **internal linearity of omega**, together with its prerequisite about
  successors and the base case for zero.  The existing arithmetic stops at
  `nat_transitive`, `nat_no_self`, `succ_le_lt`, `succ_not_le`, and
  `succ_inj_nat`.  The successor lemma came out stronger than expected: the
  induction runs on the bound alone, so no membership hypothesis on the smaller
  argument is needed.

One item remains genuinely absent and a later brick will want it: there is no
*internal* numeral function, i.e. no definable map from the metatheoretic
naturals into `omegaV`.  `Coding.natV` is an external recursion producing a
separate closed term per external index, with no claim of internal definability.
The recursion theorem is exactly the tool for building one.

`BoundedZFCConsistency.InternalSat` adds one more, proved locally and belonging
beside `nat_transitive`:

- `∀ n, mem n (omegaV H) → (n = vempty H ∨ ∃ m, mem m (omegaV H) ∧ n = vsucc H m)`

The internal arithmetic never says the successor is *onto* the nonzero naturals.
That is exactly what makes a shifted environment total on the internal omega,
and it cannot be supplied externally: a nonstandard natural is not reachable
from zero in finitely many external steps.

`BoundedZFCConsistency.InternalSoundness` adds a further one, beside
`IsFunctionOn`/`applyV`:

- **internal function extensionality**, `IsFunctionOn H F d → IsFunctionOn H F' d
  → (∀ n ∈ d, applyV H F n = applyV H F' n) → F = F'`.

The ZF development proves uniqueness of its recursion sequence by an internal
induction and never states the general fact, so every equation between internal
functions has to be reproved by hand; each composition identity of that module
is one application of it.

## Scale

This is a research-scale formalization, not a short development.  The
arithmetic counterpart required roughly two hundred Lean modules, and the
set-theoretic ingredients above — internal coded syntax, internal satisfaction,
formalized soundness, and reflection — are each a multi-module project in their
own right.  The checklist is ordered so that every entry is independently
meaningful and independently checkable.
