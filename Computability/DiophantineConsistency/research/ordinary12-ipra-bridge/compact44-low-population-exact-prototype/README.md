# Exact symbolic low-mask population: exploratory result

The three sources compose the earlier conditional low-population theorem with
an explicit finite-set cardinality proof. The latter proves the support has
985 elements using disjoint interval unions and erasure of position 1. The
resulting theorem says the explicit symbolic 8,807-digit low mask has
population 589083 in every IΣ₁ model, with no support-cardinality premise.

This is currently **single-side exploratory evidence**: wrapper session 71506
actually exited 0 for all three compilers without warnings or sorryAx. The
first support-cardinality attempt, session 44710, exited 1 on the final
conjunction order; the corrected session 25984 exited 0. The failed source and
logs and successful logs are retained. A same-provider matched replay and
independent audit are required before promoting the result.

The theorem concerns the explicitly defined symbolic finite-list mask. It does
not establish equality with retained MC bytes or the actual graph port, the
high-mask population, machine/checker correctness, or a PRA proof.
