# Model-length universal opening preserves provability

`PA194IteratedFree.free_of_all` proves that, in any arithmetic model of IΣ₁, internal PA provability of an internally well-formed universal formula implies internal PA provability of its Foundation `free` opening. It shifts the internal proof, then specializes at free label zero.

`PA194IteratedFree.free_history_sound` uses IΣ₁ induction to extend this implication over any internally coded sequence, including a nonstandard-length sequence. Its assumptions are an internally PA-provable first entry and, for each successor entry in bounds, an internally well-formed body whose universal closure is the preceding entry and whose `free` opening is the successor entry. It proves internal PA provability of every sequence entry.

The theorem **assumes** such a sequence and certifying bodies; it neither constructs an opening sequence for a given `qqAlls` axiom nor identifies its endpoint with `subst (fvarVec m) b`. It also does not construct the induction-axiom recognizer witnesses, prove the PA comprehension schema, discharge the gate, or establish a result in iPRA.

The author focused replay uses the pinned Foundation overlay and `check-iterated-free.sh`; printed axioms are `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
