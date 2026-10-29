# From cut elimination to the Σ₁ induction rule

This note records a concrete implementation route from the first-order
cut-free interface to the missing arithmetic part of Parsons' theorem. It
follows §2 of [Joosten, *Two Proofs of Parsons' Theorem*](https://www.phil.uu.nl/ozsl/articles/joosten01.pdf),
which attributes the proof to Beklemishev. The paper's mathematical proof is
not a Lean dependency. The new `ParsonsCutFree` module supplies only the first
step: it wraps Foundation's `Derivation.Canonical.hauptsatz`, preserving the
input finite theory-axiom list and giving a cut-free derivation of exactly the
same embedded end sequent. The converse forgets the cut-free certificate.
No arithmetic axiom has yet been removed.

## Height-preserving conjunction inversion proved

[`ParsonsSelection`](../Lean/DiophantineConsistency/ParsonsSelection.lean)
now proves both displayed inversion directions, simultaneous replacement of
selected occurrences and the nested three-conjunct corollary. The proof and
independent replay are recorded [here](../reviews/parsons-selection-independent.md).
The following design discussion describes the original obligation and its
motivation; induction-axiom elimination and witnessing remain open.

## Required logical inversion

For Foundation's one-sided list calculus, prove a height-preserving inversion
that works even when the principal conjunction occurs multiple times and the
last rule acts on a different formula. A convenient exact contract is:

```
cutFreeAndLeft :
  (d : Derivation ((A ⋏ B) :: Γ)) → IsCutFree d →
  ∃ e : Derivation (A :: Γ), IsCutFree e ∧ e.height ≤ d.height
```

and analogously for B. With the current explicit contraction constructor,
a naive recursion on `d` cannot assume that `(A ⋏ B)` is the displayed head
in the immediate premise. One robust proof generalizes to replacing **every**
occurrence of the chosen conjunction in a list by its selected conjunct and
inducts on the cut-free derivation, preserving context membership; alternately
use a membership-aware multiset context. Quantifier cases require proving that
replacement commutes with free-variable shift and term substitution, and that
the newly bound formula has the required eigenvariable condition. Do not
claim this interface follows from `isCutFree_and_iff`: that existing lemma
only recognizes a derivation whose outer constructor is literally `and`.

The two height bounds are essential: applying the induction hypothesis to the
three inverted premises must decrease relative to the original existential
introduction, not merely produce arbitrary cut-free derivations of unknown
height. Nested conjunctions are inverted one at a time; contractions and
weakening must preserve the relevant multiset/list invariant.

## Guarded rule client proved

[`ParsonsRule.three_disjunctions`](../Lean/DiophantineConsistency/ParsonsRule.lean)
now constructs the isolated guarded-rule conclusion from the three described
premise proofs in an explicit Σ₁ induction-rule calculus. See its
[independent replay](../reviews/parsons-rule-independent.md). The full
translation of cut-free derivations and the PRA witnessing step remain open.

## The actual induction-axiom case

After a precise normal-form translation, the negation of an induction axiom
for a Σ₁ formula `φ(x, parameters)` is an existential block whose matrix
contains `φ(0)`, `∀x (φ(x) → φ(x+1))`, and `¬φ(t)`. Universal parameters
from Foundation's `InductionScheme` cannot be dropped. Either retain the
finite parameter block explicitly or introduce pairing and projections with
proved defining axioms, as discussed in Joosten's footnote 2.

For a cut-free proof whose final rule introduces the existential in this
negative induction axiom, inversion yields strictly shorter derivations of
three sequents, each containing the remaining negative induction assumptions
and a strict Π₂ side context `Π`. To use the induction hypothesis, prove the
exact normal-form facts that each of the three displayed formulas is admissible
as a Π₂ side formula; merely having a hierarchy membership for a non-prenex
formula is not automatically the paper's strict prenex contract.

Let the finite disjunction of side formulas have a common prenex form
`∀u ∃v C(u,v)` with bounded/quantifier-free C in the chosen enriched language.
For arbitrary u, set `E(u) := ∃v C(u,v)` and
`θ(x,u) := φ(x) ∨ E(u)`. A concrete next proof-rule lemma should take actual
proofs of the three disjunctions

```
φ(0) ∨ E(u)
(∀x (φ(x) → φ(x+1))) ∨ E(u)
¬φ(t) ∨ E(u)
```

in the intermediate Σ₁-induction-rule calculus and return an actual proof of
`E(u)`. It must build both premises of the induction rule for θ, invoke that
rule with all parameters, instantiate at t, and combine with the third
premise. The Σ₁ membership of θ, eigenvariables and generalization back over u
must be checked in Lean. This is classical logical reasoning inside a precisely
specified object calculus, not a Lean-level assumption that E is true. Other
cut-free last rules and the finite axiom base need their own induction cases.

## From the rule to PRA

Joosten's Lemma 2.2 invokes Herbrand witnessing for an appropriate universal
presentation of PRA to obtain PR witnesses for the base and step of each Σ₁
induction-rule application. One primitive recursion composes those witnesses,
and open or bounded induction proves its correctness. The current PRA design
has quantifier-free induction **axioms**, so it is not automatically a universal
theory to which Herbrand applies. A precise presentation equivalence or a
separate witnessing theorem is required. The old ordered-ring language, its
bounded formulas, parameter coding and the enlarged PR-symbol language must
all be related by proved translations. None of the cut-free adapter, source
complexity theorem or existing IΣ₁ proof supplies this witnessing theorem.

The actual target remains a closed Lean derivation of PRA provability for the
exact maintained sentence, followed by separate internal transfers for other
selected equations. The result in `ParsonsCutFree` is a reusable entry point,
not a proof of either half of Parsons' theorem.
