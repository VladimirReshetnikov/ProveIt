# Actual diagonal W coefficient: explicit-lemma retry

Outer session 48691 exited 1: only `(if True then -2 else 0) = -2` remained
unsolved, so no object or postflight exists. The [independent failure audit](../../reviews/current14-carrier65-diagonal-w-retry-failure-independent/)
passed. This retry changes only the two earlier failed proof bodies: it uses
explicit polynomial coefficient lemmas and the direct constant `natDegree_C`
lemma. The no-Lean preflight and [independent prelaunch review](../../reviews/current14-carrier65-diagonal-w-retry-prelaunch-independent/)
passed. The
audited failed attempt, absent object and direct providers remain pinned.
The intended W coefficient −2 and degree 2 are one factor ingredient, not
the whole diagonal leading coefficient or exact total degree.
