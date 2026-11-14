# Internal PA bounded comprehension

`PA194BoundedComprehension.bounded_comprehension` proves that, in every arithmetic model of IΣ₁, internal PA proves `∀a ∃s ∀x (bit(x,s) ↔ (x<a ∧ P(x)))` for every internally well-formed one-variable formula `P`. The model, formula code, quantifier bounds and encoded witnesses may be nonstandard. The `predicate` definition gives the exact internal formula.

The proof uses the model-uniform internal PA induction theorem. The zero case constructs the empty set. The successor case uses the fixed order identity and equality replacement, obtains a conditional-insertion witness, and proves that the new set codes exactly the desired bounded instances. The auxiliary existential-elimination theorem and the shift equations for the quoted bit, less-than and successor templates are checked explicitly.

This establishes the internal bounded-comprehension theorem, not yet its application to the exact distinct-label numerical gate. It also does not establish an iPRA implication or the PA194 machine consistency equivalence.

The author focused replay rebuilt the five new modules in order against separately checked prerequisite overlays, with no `sorryAx`; `check-bounded-comprehension-suffix.sh` is the replay entry point. The full nested dependency rebuild has not been repeated for this suffix.
