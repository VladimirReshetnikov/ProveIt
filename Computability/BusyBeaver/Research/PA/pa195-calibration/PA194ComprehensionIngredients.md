# Internal induction rule and order facts

`PA194InternalInductionRule.induction_rule` specializes the arbitrary-code internal PA induction theorem: for any internally well-formed one-variable formula, internally PA-provable base and universal successor step imply internal PA provability of the universal conclusion. Formula codes may be nonstandard.

`PA194InternalOrder` quotes fixed standard IΣ₁ proofs into every IΣ₁ arithmetic model and specializes them inside PA. Its `internal_PA_order_explicit` proves `∀x (x < a+1 ↔ (x < a ∨ x=a))` for arbitrary model label `a`; `internal_PA_zero_explicit` proves `∀x ¬(x<0)`. The explicit typed code equations are checked and permit use under quantified arbitrary-formula templates.

These are ingredients for bounded bit-set comprehension. They do not themselves prove comprehension, the distinct-label gate, an iPRA implication, or the machine consistency equivalence.

The author focused replay rebuilt both new modules in order against retained and independently checked full-induction prerequisites; printed axioms are `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. An independent run of `check-comprehension-ingredients.sh` completed the full nested rebuild without `sorryAx`.
