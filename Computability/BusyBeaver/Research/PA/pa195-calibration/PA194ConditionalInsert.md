# Conditional bit-set insertion in internal PA

In every arithmetic model of IΣ₁, `PA194ConditionalInsert.conditional_insert` proves inside PA that for arbitrary model labels `a`, `b` and an arbitrary internally well-formed formula `A`, there exists a bit-coded set `s` satisfying `∀x (bit(x,s) ↔ (bit(x,a) ∨ (A ∧ x=b)))`. The formula and labels may be nonstandard. The proof performs its case split in internal PA: when `A` holds it uses the fixed insertion theorem, and when `¬A` holds it chooses the original set. The preparatory modules prove and universally lift the corresponding propositional equivalences for arbitrary internal formulas.

This gives a set-extension ingredient for bounded comprehension. It does not construct the model-length induction or the induction-axiom closure, prove comprehension, discharge the distinct-label gate, establish an iPRA implication, or prove the machine consistency equivalence.

`check-conditional-insert.sh` rebuilds the dependencies and all four new modules, checking printed axioms for `sorryAx`. A focused ordered suffix replay against retained prerequisite overlays is recorded below. As with adjacent packages, the full nested rebuild is deferred because of the existing disk-I/O constraint.

The author focused replay built `PA194ConditionalInsertLogic`, `PA194ConditionalInsertLift`, and `PA194ConditionalInsert` in order in `/dev/shm/pa194-conditional-insert-fresh`, against the separately checked bit-insertion, conditional-singleton, and retained prerequisite overlays. The printed dependencies contain only `propext`, `Classical.choice`, and `Quot.sound`, and no `sorryAx`.
