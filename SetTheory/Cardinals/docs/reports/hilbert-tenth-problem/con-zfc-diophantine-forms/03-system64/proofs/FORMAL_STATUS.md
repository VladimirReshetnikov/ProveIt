# Meaning of the ZFC-provability claim

## The statement

Let `Sol` be existence of a strictly positive integer solution of the
specified seven equations, with the concrete K215 compiler coefficients.
Use the repository's precise first-order presentation of ZFC and define

\[
\operatorname{Con}_{\rm repo}(\mathrm{ZFC})
 :=\neg\operatorname{BProv}(\mathrm{ZFCax\_s},[],\bot).
\]

The mathematical conclusion is

\[
\mathrm{ZFC}\vdash
 \bigl(\mathrm{Sol}\leftrightarrow
       \operatorname{BProv}(\mathrm{ZFCax\_s},[],\bot)\bigr),
\qquad
\mathrm{ZFC}\vdash
 \bigl(\neg\mathrm{Sol}\leftrightarrow
       \operatorname{Con}_{\rm repo}(\mathrm{ZFC})\bigr).
\tag{1}
\]

Here ZFC on the left is the metatheory in which natural numbers, finite
strings, machines, polynomial evaluation, and finite proofs are represented
as sets. The consistency statement on the right is a formula about those
finite syntactic proofs. It asserts no semantic soundness principle.
There is no consistency premise in (1).

The mathematical proof in ZFC and a machine-checked derivation in a
particular formal presentation of ZFC are different deliverables. The
archive provides the former, with the exact inherited proof interfaces
identified. It does not contain an encoded ZFC proof object for (1), or a
new Lean/Rocq formalization of the whole Diophantine construction.

## Why the external endpoint alone is insufficient

The K215 README explicitly calls its Lean and Rocq results external
proof-assistant theorems and disclaims an encoded PA or ZFC derivation.
The list `propext`, `Classical.choice`, `Quot.sound` is an audit of named
Lean axioms; it is not a theorem that Lean's dependent type theory is
conservative over ZFC. In particular, the built-in type and universe rules
are not additional entries in that list. A closed Rocq axiom context
likewise does not by itself establish ZFC-provability.

Accordingly, (1) is **not** inferred from a blanket claim that ZFC proves
the soundness of either proof assistant. The relevant mathematical
arguments are interpreted directly in ZFC. There is no need to model the
whole universe hierarchy of a proof assistant, and no inaccessible-cardinal
assumption enters this interpretation.

## The actual ZFC argument

All repository paths below are relative to ProveIt at commit
`cdd582bec13f908df3711fa9e05d1ddac368a5db`.

1. **Finite arithmetic and the compiler.** Polynomial evaluation, the fixed
   coefficient sums, configurations, finite computation traces, and the
   machine compiler are definitions on integers and finite strings.
   Their correctness arguments use arithmetic identities, induction,
   finite combinatorics, and the elementary Pell theorems identified in
   `fixed_marker_review.md`. All are theorems of ZFC. The folded-machine
   simulation and literal table checks identify the accepted input with
   blank K215 halting. The fixed-marker restoration proves
   `Sol` iff that accepting computation exists.

2. **K215's finite simulation chain.**
   `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean` first
   identifies blank machine halting with derivability of code 1 in the
   `C222` calculus. The literal endpoint is `KEndpoint215.lean`.
   State renaming, initialization, source/register simulation, proof
   enumeration, and the finite derivation rules are expressed using
   finite syntax and induction. Their mathematical proofs transfer to
   ZFC without any appeal to the truth of ZFC's own axioms in an ambient
   universe.

3. **The set-theoretic calibration must also be included.** It is inaccurate
   to describe all of the K215 calibration as merely finite arithmetic.
   `KEndpoint.c222_iff_zf_refutation` combines `KUpper222` with the lower
   chain from `KSeedDirect222`, `KLowerQHyp`, and `KQ1ZF`. It uses
   first-order completeness, the seed-model construction, a bisimulation
   quotient, and the appropriate well-founded submodel to compare `C222`
   refutability with ZF refutability. These are ordinary arguments about
   **set-sized structures**. For a set domain \(D\), relations are subsets
   of \(D^2\), quotients are sets of equivalence classes, subclasses of
   \(D\) used in the argument are subsets obtained by Separation, and
   functions used in model constructions form sets. Formula syntax and
   satisfaction in a given set structure are defined recursively.
   Power Set, Separation, Replacement, Choice, and ordinary recursion
   justify these constructions in ZFC.

4. **The Choice transfer is standard set theory.**
   `ConstructibleChoice.zf_refutation_iff_zfc_refutation` uses the
   constructible submodel of an arbitrary ZF model, together with
   first-order soundness and completeness. The internal model
   constructions are developed in the `Constructible*` files. They
   establish that any set model of ZF supplies a set model of ZFC.
   Thus, if a ZFC refutation existed but a ZF refutation did not,
   completeness would give a ZF model, its constructible submodel would
   satisfy ZFC, and first-order soundness would contradict that
   refutation. The converse follows by inclusion of the ZF axioms.
   This is the ordinary ZFC proof of the relative consistency of Choice;
   it assumes neither that a ZF model exists unconditionally nor that ZFC
   is consistent.

Composing these four arguments in ZFC proves the first equivalence in
(1). Negation yields the second. The same proof applies after the stated
sum-of-squares and unrestricted-integer domain conversions.

The use of semantic model arguments here poses no Tarski obstruction:
uniform satisfaction is defined for a supplied **set structure**, not as
a truth predicate for the ambient universe of all sets. Likewise, the
proof-assistant parameters `V : Type u` in the model lemmas are read as
arbitrary sets \(D\) in this mathematical proof. One does not assert that
the collection of all such sets is itself a set. Choice is used only
for the set-indexed families occurring in these constructions; no global
choice function on the universe is required.

This identifies the foundation of the mathematical proof. It does not
claim to be a certified translation of all the Lean/Rocq proof terms, nor
does it justify an additional claim of PA-provability. A PA claim would
require a separate arithmetization or effective proof-translation analysis
of the semantic calibration.

## Matching the proof predicate to ordinary Con(ZFC)

The exact repository syntax is useful, rather than an unspecified
phrase such as “a ZFC-like theory.” In
`Logic/FirstOrder/Lean/FirstOrder/Completeness.lean`,

```text
BProv B G phi := ∃ Gb, (∀ x ∈ Gb, B x) ∧ Prov (Gb ++ G) phi.
```

`Prov` is the finite classical first-order natural-deduction calculus
with equality in `FirstOrder/Calculus.lean`.
`SetTheory/ZF/Lean/ZF/Zf.lean` defines `ZFax_s` as the universal closures
of Extensionality, Foundation, Power Set, Pairing, Union, Infinity, all
Separation instances, and all functional Replacement instances.
`SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/Choice.lean`
adjoins the universally closed Zermelo selector form of Choice.

These are standard first-order ZFC axioms. Empty Set follows from Infinity
and Separation. The partial-functional version of Replacement is
equivalent over the remaining axioms to the usual total-functional
version: totalize a partial relation using the empty set as a default,
apply total Replacement, and separate the genuine range. The reverse
implication is immediate. The selector form of Choice is equivalent to
the choice-function form: for a set-indexed family of nonempty sets,
replace its members by the disjoint sets \(\{i\}\times A_i\); the unique
selector in each disjoint set is the graph of a choice function. A choice
function conversely gives a selector for a disjoint family.

Finite formulas, rule trees, and axiom-instance annotations can be coded
by natural numbers. Including the generating formula for each schema
instance makes axiom verification a primitive-recursive calculation.
Induction on the coded tree proves that the resulting numerical proof
predicate has a witness exactly when `BProv ZFCax_s [] fBot` holds.
The standard translations between classical first-order proof calculi,
universal closures, and the axiom variants just described are provable in
ZFC. Consequently \(\operatorname{Con}_{\rm repo}(\mathrm{ZFC})\) is
provably equivalent in ZFC to ordinary syntactic \(\operatorname{Con}
(\mathrm{ZFC})\) for any explicitly chosen standard effective
presentation.

This is a syntactic consistency equivalence. No appeal to omega-consistency,
Sigma-1 soundness, the existence of a standard model, or the ambient truth
of every ZFC theorem is needed to prove it.

## Recommended concise statement for the report

> With the displayed fixed coefficient recipe, ZFC proves that the system
> has a positive integer solution exactly when its standard first-order
> proof calculus has a finite derivation of falsity. Therefore ZFC proves
> that the system has no such solution if and only if Con(ZFC). The proof
> composes the stated compiler and Pell arguments with K215's finite
> simulation and set-model calibration, interpreted as ordinary ZFC
> mathematics. The inherited K215 endpoint is externally kernel checked
> in Lean and Rocq; the new Diophantine reduction is supplied as a
> mathematical proof with reproducible arithmetic audits, without a new
> kernel-checked or internally encoded ZFC proof of the entire chain.

One should not replace this paragraph by “the Lean axiom list proves the
ZFC claim.” Conversely, the absence of an encoded ZFC proof object should
not be described as a missing mathematical consistency premise.

## Consequences and limits

If ZFC is consistent, the system has no solution in the standard positive
integers and, by Gödel's second incompleteness theorem, ZFC cannot prove
that it has no solution. Consistency alone does not also establish that
ZFC cannot prove the false existential assertion that a solution exists;
that additional unprovability follows, for example, from Sigma-1 soundness.
Thus “unprovable nonexistence under consistency” is the precise consequence
available without a stronger hypothesis. This construction does not prove
Con(ZFC).

## Source references

The principal source is the pinned ProveIt commit above. Its
`Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/README.md`
states the external formalization boundary explicitly. The named files in
this note were inspected at that commit, including the definition of
`BProv`, the rules of `Prov`, `ZFax_s`, and `ZFCax_s`.

For the distinction between named axioms and the surrounding type theory,
see Lean's official [Axioms](https://lean-lang.org/doc/reference/latest/Axioms)
and [Type System](https://lean-lang.org/doc/reference/latest/The-Type-System/)
reference chapters. No general conservativity or whole-kernel soundness
theorem is assumed here.
