# Symbolic low-mask population: single-side exploration

The latest exploratory source is retained in `observations/CompactLowPopulation.lean`.
Its generic finite-list lemma assumes only that a standard finite support is
contained in the given range and includes the distinguished slot. It proves the
sum of the fuelled binary digit populations plus the support cardinality plus
one equals `length * 67`. The concrete-list and model theorems additionally
assume the explicit standard-natural equality `support.card = 985`, and under
that assumption the cast symbolic low mask has population 589083 in every
IΣ₁ model.

This is a single-side exploratory result. Session 35070 exited 1 on broad
simplification and recursion-depth failures; session 52960 exited 1 on an
unsimplified conditional and a natural-cast residue; session 68025 exited 0
with no warnings or sorryAx after restricting simplification. Both failed
sources and all three logs are retained. No paired replay or independent review
has been performed.

The cardinality equality is not proved here. Equality of this symbolic mask
with the retained MC bytes or the actual graph port is also unproved, as are
the high-mask population, machine checker and internal PRA derivation.
