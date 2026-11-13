# Exact adaptive lift for the free-J main carrier

`main_lift_identity` proves in any `IΣ₁` model, using its difference ring,
that the actual free-J graph expression `Dstar` satisfies

```
Dstar = U · (X + a·c + γ_old·(4a+3))
```

whenever the following two equations hold at the same graph valuation:

```
X = q·w,
U·γ + U·w = U·γ_old + (k−R−1).
```

Here `q,U,X,a,c,γ,k,R` are the literal's own expressions/coordinates,
`w,γ_old` are specified difference-ring elements, and `rankExpr` and
`shiftExpr` expose the graph's exact `R` and `k−R−1`. The proof checks the
literal's `U` and `Dstar` shapes by reflexivity, then uses the linear lift
and `U=q²Y` to derive the identity. It does not assume a graph zero.

This theorem **assumes** the linear lift equation. It does not establish that
a suitable natural graph coordinate `γ` exists or is positive, nor that the
seed's `γ_old` makes this equation solvable. Those require the relevant
divisibility, size and positivity results. It also does not supply the first
carrier, the ordinary tail, an actual graph valuation or an iPRA proof.

Bounded author attempt 03 exited 0 in 5.215 seconds without warning or
`sorryAx`. Source SHA-256 was
`9200cc59bfbbfa0a224506408d4d8e9cd76dc42d6751d35263f9b8acd8ebedd4`;
object `/tmp/free-j-adaptive-lift-author-eaue0a2c/FreeJAdaptiveLift.olean`
had SHA-256
`08e64dbfb91da17ad2f68b2e342d550cb575dc76e19d0f10d3838554eb5c54ed`.
All three selected provider overlaps were checked byte-for-byte (91, 516 and
97 paths), and 1,181 live provider files and direct/named transitive bridge
object companions remained unchanged. This single-author check does not
independently replay provider ancestry or audit dynamic and package-transitive
dependencies. Lean reports `propext`, `Classical.choice` and `Quot.sound` as
metatheoretic dependencies.

Attempts 01 and 02 failed on local numeral-cast/rewrite issues; their sources,
logs and receipts are retained. Attempt 03 resolved these by a ring
calculation without weakening the statement.
