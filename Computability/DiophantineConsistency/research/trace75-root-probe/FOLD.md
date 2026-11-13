# Trace75 noncircular odd-ordinate recovery

`Trace75Fold.graph_odd_ordinate` is Lean checked in any `IΣ₁` model. At
arbitrary natural ports satisfying `0<beta`, for ten positive witnesses and a
zero of the Lean trace75 value in the model's difference ring, it returns
natural model witnesses `r,j,I` such that

```
0 < r < j,  r % 2 = 1,  0 < j,  0 < I,
c = ycoord r (A-1),
xcoord j (A-1) = 1 + 2*Delta*U²*E,
ycoord j (A-1) = I,   c² ∣ I.
```

Here `A` is the local natural abbreviation `X*Y+Y` from `Trace75Factors`
(the source paper's Pell base is `A+1`). The result uses the actual same
strong and auxiliary graph witnesses, the trace75 signed residue and the
freshly rebuilt generic `recover_odd_ordinate`; it does not assume the target
main norm, an exact rank/index equality, or an 80 graph zero. The proof
establishes the size conditions needed by the generic theorem. It is a
necessary condition for a trace75 zero, not a converse, machine halt result,
trace74 positivity guard, iPRA theorem, or Lean JSON/payload binding.

Accepted source `Trace75Fold.lean` SHA-256
`93b63d10cb04a904036e900e2cb8ee9af29b60c45768e00f8b1f007d7fdfc3dd`;
`run-fold-v3.py` accepted `observations/fold-attempt03/`, object
`/tmp/trace75-fold-b2hmelpc/Trace75Fold.olean` SHA-256
`60d26b62219b41539aecf950465beee7e90df5a50f78e14ac8670d47c2ef5263`.
`#print axioms` reports `[propext, Classical.choice, Quot.sound]`.
Attempt01 failed to find the historical `Direct80Joined` import, and
attempt02 failed a local let-unfolding goal; both snapshots and logs remain.
The accepted run selects the fresh `pell-generic-fold-rebuild` objects rather
than the historical generic provider with the 80-graph import. Direct
providers and several nearby dependencies are pinned. Project and package
transitive, historical source/object and dynamic ancestry remain inherited;
no complete selected closure audit or independent replay is claimed.
