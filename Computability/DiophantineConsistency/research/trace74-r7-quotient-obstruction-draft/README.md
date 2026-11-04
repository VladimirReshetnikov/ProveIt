# R7 bounded-quotient obstruction: Lean-checked conditional lemma

In a discrete ordered commutative ring, `impossible_of_bounded_quotient` assumes h>0, y>0, 0<j<y, 32h<y and

`h*(4y-1)*(516y-1)*(127y-32) = (4y*(x+1)-1)*j`.

It derives `y | j-32h`, obtains j=32h from the strict bounds, and derives `4y | 3y`, a contradiction. No graph or size hypothesis is inferred by this generic theorem.

Attempt 01 failed because the tactic import was missing, and its diagnostics and source/runner snapshots remain under `observations/attempt01/`. Attempt 02 passed in actual outer session 2697, exit 0; terminal SHA-256 `c09960edbc4a4e7df8ce150e70c66f30af313b84adbd05678a1818fe3732d239`. The [independent result audit](../../reviews/trace74-r7-quotient-obstruction-result-independent/README.md) checked all 35 recorded direct pins, reports, logs and object. Full historical project/package/dynamic ancestry and ongoing search-path selection remain outside this evidence.
