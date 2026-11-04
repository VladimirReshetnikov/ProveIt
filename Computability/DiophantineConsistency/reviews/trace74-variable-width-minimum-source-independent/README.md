# Independent source review: unbounded-index minimum separation

The reviewed source has SHA-256
`df79949ff57353353e020247ffb806a423bdb61f2badd8b8621bb19c4ced5906`.
Its threshold argument is sound: `w≥1` and `4w≤n` imply
`3w+1≤n`, `10w≤3n`, and, writing `D=3n−10w`, `n≤2D`. For
`L=2w(n+w)+5w`, nonnegativity of `w(2n−2w−5)` yields `L≤4wn`; the
additional premise `8w≤B` then gives `4wn≤8wD≤BD`. The proof justifies
the model's truncated subtraction before moving it to the difference ring.

For the fixed first port, `B=67·8807=590069`. The chosen width
`w=min(n/4,73758)` is positive for `n≥4`, satisfies `4w≤n`, and satisfies
`8w≤590069` because `8·73758=590064`. Model division uses the division
algorithm and remainder bound, not standard-natural induction. The client
therefore proves `n+min(n/4,73758)<r` for supplied same-zero ordinates
without an upper bound on `n`. Its existential form preserves the earlier
linked pair, ordinate identities, residue, `n≥7`, odd `r≥11`,
`n+3<r`, and `r<2n`.

The positive graph-zero, fixed symbolic first-port and same-ordinate
conditions remain essential. The result does not rule out all zeros,
prove a reverse guard, bind the symbolic port to the external payload,
or establish an iPRA endpoint. This is a source-level mathematical review
and interface check, not an independent Lean replay or an authentication
of transitive provider/package ancestry.
