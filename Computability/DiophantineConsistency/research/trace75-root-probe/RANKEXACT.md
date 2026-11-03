# Trace75 rank equals the odd main Pell index

`Trace75RankExact.graph_rank_exact` is Lean checked in every `IΣ₁` model. For
arbitrary natural ports satisfying `31≤beta`, `MC<beta`, `MF<2*beta` in the
model, and ten positive witnesses at which the Lean trace75 ring value is
zero, it proves

```
actual signed rank register = ι(rankNat),
3*q < rankNat,  rankNat % 2 = 1,
c = ycoord rankNat (A-1),
rankNat + q³ + q + 1 ≤ q⁴.
```

Here `A=X*Y+Y`; K0 is arbitrary. The proof combines the signed auxiliary
rank residue with a separately obtained main-ordinate witness on the same
p,v,c. It invokes the freshly rebuilt generic rank reduction and the two
proved half-size inequalities; it does **not** identify the separately chosen
strong I,j tuples. It establishes neither power recovery `X=2^rankNat`,
halting, an iPRA theorem, a trace74 reverse guard, nor formal binding of the
external JSON or coefficient payloads. The port bounds are explicit rather
than fixed-port specialization.

Accepted source `Trace75RankExact.lean` SHA-256
`0e5c5e4e05a934a86d83d619066e943bda3c83fab3156683874d2de0ad0e2c5f`;
`run-rankexact.py` accepted `observations/rankexact-attempt01/`, object
`/tmp/trace75-rankexact-fk1_orgc/Trace75RankExact.olean` SHA-256
`26c9d2ab4e3a06a3f72906eb1a2b2604081324f1488fc1308f594ec3985436ee`.
`#print axioms` reports `[propext, Classical.choice, Quot.sound]`. Selected
direct and nearby providers are pinned; project/package transitive, historical
source/object, prior generic between-stage and dynamic ancestry remain
inherited, without a full closure audit or independent replay.
