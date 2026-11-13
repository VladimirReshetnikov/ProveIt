# Independent review: partial scale swap and fixed-norm rigidity

**PASS as standard-integer reasoning with the stated hypotheses.** For
`J=2`, put `q=2beta+1`, `q'=beta+1`, `w=q'u`, `s=q'³t`,
`w'=qu`, and `s'=q³t`, with positive u,t. Then `wq=w'q'` and
`q³s=q'³s'`. For nonnegative K, if `beta∤(K+u)`, division of
`K+w'` by beta gives remainder `1≤F'<beta`, positive quotient z'
(because `w'>2beta`), and positive `alpha'=beta−F'`. With `C'=1`,
`F'+alpha'+C'=q'` and `(K+w')C'=F'+z'(q'−1)`. Conversely, if
`beta|(K+u)`, any positive F',alpha',C' with sum `q'=beta+1` has
`0<F'<beta`, while transport would force `beta|F'`. The resulting
contradiction applies to this target q', not all possible q changes.

At fixed X,Y, retaining k, eta, first-root witness and h keeps the 72
first and main residuals; also retaining f and i keeps the strong residual.
The auxiliary expression and old carrier still depend on the new rank.
The construction therefore does not by itself give a 76Y graph zero.

For the separate rigidity deduction, assume actual positive source 72 and
target 76Y zeros at the same fixed ports, with the same `X,Y,c,k` and source
`3|q`. The checked forward update makes the target into a positive 72 zero
and yields its exact old-carrier equation. The checked fixed-compact
ranked-main theorem gives `ycoord R (XY+Y)=c` for both 72 zeros; strict
monotonicity identifies their ranks. Each checked main-index extraction has
the same ordinate and so its index is that rank; the carrier roots therefore
are the same x-coordinate. Since their `U,X,a,c,H` agree and `H>0`,
the two carrier equations force equal h. The source then satisfies the
forwarded target's old-carrier equation with the same k and rank,
contradicting the checked fixed-port source no-gamma theorem under `3|q`.
The reviewed component scope is captured-provider Lean checking; this
composition is an external standard-integer deduction, not a newly checked
Lean theorem.

The author's finite checker reproduced its retained output byte-for-byte.
A separate [checker](check.py) enumerated exact scale and transport cases,
including the blocked residue, and independently evaluated the actual 72
graph's first, main and strong residuals after each swap; its observed exit
was 0 and output is [result.json](result.json). Some controls have both
source and target transport zero, but none is claimed to be a full graph
zero. Neither argument establishes existence of either zero, universal
failure of the existential reverse implication, or impossibility of changing
X,Y,c or k.

Reviewed construction README SHA-256
`cc33e3b4a8f7052a817d851ce7ba8a42a421526d897ac8a75c10889b27bb529c`,
checker `3f9f70440bbd666ddaee9c439ca4132e1b0991b977b6215be08874733aae82c7`,
result `2eb386b0f36d8f5b13fa3927db8b2cdee081c9ac0466428692f21dc903b06daf`.
Independent checker SHA-256
`ed747d790c45c4a2184576922490393118c952905eb4edadf53048bba36a16aa`,
result `69ddd3899af97f32ed65fa863e01dd012da040511b13ae82c835fa1c4a8bf68e`.
