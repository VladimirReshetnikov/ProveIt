# Internal bit-set insertion

`PA194InternalBitInsert.ISigma1_proves_insert` gives a fixed standard IΣ₁ proof that any bit-coded set can be extended by a single element. `internal_PA_insert_explicit` quotes that proof into an arbitrary model of IΣ₁ arithmetic and internally specializes it to arbitrary model labels `a` and `b`, including nonstandard values. It proves in internal PA the explicit formula `∃s ∀x (bit(x,s) ↔ (bit(x,a) ∨ x=b))`. The two sides use the fixed quoted bit formula; `insert_subst_shape` certifies their precise substitutions. The metatheoretic completeness argument is used only to obtain the fixed standard proof, not to evaluate arbitrary internally coded formulas.

This is one ingredient for a prospective internal bounded-comprehension induction. It does not construct that induction or prove the distinct-label gate, an iPRA implication, or the machine consistency equivalence.

The author compiled the new module against the previously checked singleton and retained prerequisites in `/dev/shm/pa194-bit-insert-fresh`; its reported axioms are `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. The full nested check is `check-internal-bit-insert.sh`; it rebuilds the singleton prerequisites before the new module, and has not been rerun for this package due to the existing disk-I/O constraint.

An independent suffix replay rebuilt the insertion module against separately
checked conditional-singleton and earlier source prerequisites. It passed
without `sorryAx`; this was not a full nested replay.
