# Internal PA proves numerical head3 and head4 translations

`PA194SourceEqualityPreservation.lean` proves that the positive arithmetic
translations of every numerical head3 and head4 equality-substitution source
axiom are internally PA-provable. All numerical labels may be arbitrary,
including nonstandard, model values. The proof identifies the internal
membership and equality translations, including the membership field order,
and uses Foundation's model-uniform equality-replacement theorem on the fixed
bit-membership formula. The relevant outer and inner implication codes are
proved nonzero, so their translations have the usual implication form.

The results hold in every nonempty candidate-PRA model with equality and an
IΣ₁ arithmetic reduct. Lean reports `propext`, `Classical.choice`, and
`Quot.sound` for the printed dependencies, with no `sorryAx`.

These are two concrete numerical seed families. They do not establish the
remaining source axiom families, a machine-trace-to-lines bridge, an
object-theory iPRA theorem, or the PA194 consistency equivalence.

Run `check-source-equality-preservation.sh` with the audited
`IPRA_LEAN_OVERLAY` and `IPRA_FOUNDATION_OVERLAY` set; it rebuilds dependencies
in a fresh temporary overlay and rejects `sorryAx`.

An independent suffix replay recompiled the final theorem module against the
author's retained ordered prerequisite overlays, with no `sorryAx` in the
reported dependencies. A complete fresh rebuild is running separately.
