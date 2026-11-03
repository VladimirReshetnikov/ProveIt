# Unchecked parametric boundary seed corollary

This source-only draft responds to the retained failed `Trace74BoundarySeedConditional` attempt. It replaces the large model numeral `2^30` with a positive parameter `W`, retains the exponential equality, phase, growth and two Pell equations as explicit assumptions, and attempts to discharge the small truncated-subtraction equalities separately. The proposed conclusion still fixes the returned witness coordinates `w 0=w 1=w 2=1` at arbitrary ports `(1,1,28,0)`.

It has not been elaborated or kernel-checked. In particular, its small-model arithmetic tactics, imports and exact same-witness binding remain to be tested on a reviewed provider after the four-stage witness chain is complete. The finite R=31 seed is not formally specialized here; no concrete 74 zero, fixed BFS port result, or iPRA claim follows.

Independent source-level review passed at `reviews/trace74-boundary-seed-parametric-draft-independent/`. Same returned-coordinate equalities and explicit assumptions were checked at source level; no Lean elaboration or numerical specialization was performed.
