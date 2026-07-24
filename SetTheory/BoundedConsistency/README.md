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

> **Current status.**  Early.  Phase one — the metatheoretic rank and
> restricted-derivation development — is complete and checked:
> `BoundedZFCConsistency.Basic` supplies the polarity ranks, the `Type`-valued
> proof-tree mirror with erasure and completeness, the every-occurrence rank,
> restricted provability with monotonicity and cofinality, and the
> conclusion-only collapse.  Everything after that is open.  The object-level
> theorem is **not** proved, and nothing in this project should be read as
> claiming `ZFC |- Con_n(ZFC)`.

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

Route 1 is the intended one here.  It is more modular, it reuses “set model plus
soundness” rather than building a truth class, and the intermediate statement it
produces is of independent interest.  Route 2 remains available if the
formalized-soundness step proves more awkward than the reflection step.

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
- [ ] Arithmetize the syntax of `Form` and of derivations inside the object
  theory, as hereditarily finite sets, with absoluteness lemmas.
- [ ] Define the object-level sentence `Con_n(ZFC)` for each metatheoretic `n`
  and prove its arbitrary-model characterization.
- [ ] Formalize satisfaction for set-sized structures inside ZFC, by internal
  recursion on coded formulas.
- [ ] Formalize soundness of the 17-rule calculus with respect to internal set
  models.
- [ ] Prove the Levy reflection scheme inside ZFC: for each metatheoretic `n`,
  ZFC proves that some `V_alpha` is `Sigma_n`-elementary in the universe.
- [ ] Combine reflection with internal soundness to obtain
  `Con(ZFC_{Sigma_n})`, and derive `Con_n(ZFC)` from it.
- [ ] Apply `godel_completeness_for_theories` to obtain, for every metatheoretic
  `n`, the object-level derivation `ZFC |- Con_n(ZFC)`, and audit its
  assumptions.

## Scale

This is a research-scale formalization, not a short development.  The
arithmetic counterpart required roughly two hundred Lean modules, and the
set-theoretic ingredients above — internal coded syntax, internal satisfaction,
formalized soundness, and reflection — are each a multi-module project in their
own right.  The checklist is ordered so that every entry is independently
meaningful and independently checkable.
