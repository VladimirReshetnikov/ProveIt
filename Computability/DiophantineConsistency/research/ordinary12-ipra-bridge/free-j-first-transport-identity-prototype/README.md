# Additive first transport to the exact free-J graph

`graph_z_of_additive_transport` proves in any `IΣ₁` model that the actual
free-J graph expression `Z` satisfies `Z=M·τ` whenever, in the model difference
ring at the same graph valuation, the following additive equation holds:

```
M·(ell+k+r) + Y·(q−1) = M·τ + W·q³·Bt,
M = q³(q−1),  W = 1+(q−1)k.
```

Here `q−1`, `M`, `ell`, `k`, `r`, `Y`, and `Bt` are the literal's actual
expressions and coordinates: `ell=X·Y²·k`, `k=η+ζ`, and
`Bt=(q−F−α)(X+Kq)−qF`. The source exposes `M`, `ell` and `Bt` as expressions,
checks the literal's folded `Z` shape by reflexivity, and uses ring algebra
to derive the claimed equation. It does not assume `Bt=qz(q−1)` or `X=qw`;
those can be used separately to establish the additive equation.

This theorem assumes the additive transport identity. It does not construct
its witness `τ`, prove the existence or positivity of graph coordinate `r`,
build a graph valuation or provide an iPRA proof.

The bounded author attempt 02 exited 0 in 4.886 seconds with no warnings or
`sorryAx`. Source SHA-256 was
`8769a763f860d02f5b7ca76d8dd9775c197647f5c5902e50d2b80d42babf58e7`;
object `/tmp/free-j-first-transport-identity-author-80qhmdvy/FreeJFirstTransportIdentity.olean`
had SHA-256
`176f0f01689a0c422b2d5680e4c79bd79fb78a4778cf7fee0548862a763ced90`.
The three selected provider overlaps were compared byte-for-byte and all 1,181
live provider files plus direct and named transitive bridge companions were
unchanged. This is a single-author run, not an independent replay or an audit
of inherited package-transitive and dynamic dependencies. Lean reports
`propext`, `Classical.choice` and `Quot.sound` as metatheoretic dependencies.

Attempt 01 failed because the first algebraic step had not exposed the graph's
`M=q³(q−1)` expression. Its source and log are retained. Attempt 02 added that
identity and did not weaken the theorem.
