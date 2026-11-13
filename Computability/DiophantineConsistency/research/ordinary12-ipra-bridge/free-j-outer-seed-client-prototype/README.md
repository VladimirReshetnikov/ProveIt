# Actual outer seed to the free-J carrier factors

`carrier_units_of_outer_seed` applies the existing model-level
`ArithmeticOuterSeed.SeedRelations` directly to the actual 95-operation
free-J literal. For a common valuation it assumes

```
X = 2^R,  Y = s·(2^u)^3,  coordinate 8 = η,  coordinate 9 = ζ,
Z = M·τ,  Dstar = U·χ,
τ = X·Y·n + (η+ζ) − R,  χ = X + a·c + γ·(4a+3).
```

`X,Y` are graph coordinates 5 and 6; `a,c,Z,M,Dstar,U` are the actual graph
expressions. The displayed definition of `τ` is the model-natural
subtraction used by `SeedRelations`; the two carrier equations are checked in
the model's difference ring. The theorem derives both exact carrier factors
as positive units by mapping the seed squares into that ring and invoking the
seed-square bridge.

The theorem assumes the coordinate bindings, `Z=Mτ` and `Dstar=Uχ`; it does
not construct a valuation or derive those equations, prove graph-coordinate
positivity, establish the ordinary third factor, bind fixed coefficient ports,
or produce an iPRA proof. In particular, the seed `n` and graph's free
ordinary-tail coordinate are distinct quantities.

Bounded single-author attempt 03 exited 0 in 6.137 seconds with no warnings or
`sorryAx`. Source SHA-256 was
`d1d7f15683a918d955d01b103ffe0d064b097f90152ee9666edb33d2c0f4d9ff`;
object `/tmp/free-j-outer-seed-client-author-0z0jz4i9/FreeJOuterSeedClient.olean`
had SHA-256
`e8bdd50d230014526e34c88b3777ddae939df88a164e32dcda23327cdc5a2af9`.
All three pairwise provider overlaps were compared byte-for-byte (91, 516 and
97 paths); all 1,181 selected live provider files and the direct/named
transitive bridge object companions were unchanged during this check. This is
not an independent replay or a full audit of inherited package-transitive,
dynamic or earlier provider-build ancestry. Lean reports `propext`,
`Classical.choice`, and `Quot.sound` as metatheoretic dependencies.

Attempt 01 failed before elaboration because the selected provider omitted the
`BusyBeaver` namespace; attempt 02 elaborated successfully but was rejected by
the runner for a style warning. Both sources and logs are retained. Attempt 03
removes the warning without weakening the statement.
