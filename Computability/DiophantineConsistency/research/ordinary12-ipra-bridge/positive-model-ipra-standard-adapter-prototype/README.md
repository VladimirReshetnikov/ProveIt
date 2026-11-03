# Standard and equality-only iPRA from a positive model bridge

For any finite expression `e`, these conditional theorems take the same
explicit `PositiveModelBridge e` as the sibling native adapter: in every
IΣ₁ model, a strictly positive zero of `e` exists iff the encoded machine
halts in that model. They establish that:

* `standardTheory` derives the no-zero sentence for `positiveShift e` iff
  the negation of the mapped native refutation predicate;
* `standardTheory` derives the same no-zero sentence iff the Gödel–Gentzen
  translation of the selected Foundation ZFC consistency sentence; and
* the equality-only `referenceTheory` derives the erased no-zero iff the
  negation of the erased mapped refutation predicate.

The shift is the adaptive syntax substitution `x ↦ x+1`. The first theorem
uses the existing standard/native theory equivalence; the second additionally
uses the selected bounded-refutation/translated-consistency equivalence;
the third uses the existing order-erasure transfer. These are generic
proof-producing theorems **conditional on the model bridge**, not a proof
of that bridge for the compact graph. The compact theorem and this adapter
still use conflicting selected providers and have not been compiled together.
No retained coefficient, JSON, or PDF binding follows from these theorems.

The single-author bounded `observations/attempt01` exited 0 in 6.658 seconds
without warnings or `sorryAx`; all recorded direct dependency companions and
the selected nine-variable provider remained unchanged. The source SHA-256 is
`7046c2d8fde9411d517641829e3158733bfec14e778fdce6cb7d86cc9f3ccb78` and
the output object SHA-256 is
`1fb7efa7fe6adce191c37dd9fc457ca4af4dd02210b3a19e6ae110d46fea9ce5`.
All three named axiom reports are `[propext, Classical.choice, Quot.sound]`
in Lean's metatheory, not iPRA axioms. The adapter object was pinned by hash;
the successful run inherits its historical provider and package ancestry and
is not a paired replay or full transitive/dynamic audit. Guards are
point-in-time, not continuous monitoring.
