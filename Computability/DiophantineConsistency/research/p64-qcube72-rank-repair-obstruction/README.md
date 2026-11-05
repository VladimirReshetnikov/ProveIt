# A constrained rank-repair route for the free main coordinate

For the proposed 72-operation free-main graph, recovering the original
coordinate requires `U | h+k−1−R`. A possible repair is to change `F`,
`alpha`, `z` or `T`, leaving all four ports and `q,J,w,s,k,eta` fixed.
The main equation alone prevents adjusting positive `h` independently:
for these fixed coordinates, `U>0`, `H>0` and `b0=X+a*c>0`; the carrier
`U*b0+H*h` is positive, and its square is fixed by the main residual. Hence
any other positive `h` satisfying that residual equals the original `h`.
This is a paper argument, not a checked Lean theorem.

Writing

```
G=(q−1)*(q−F)+alpha,
R=G*(q²−1)+J*(MC+q*MF),
```

the inverse divisibility for any such rank repair requires

```
(q²−1)*G' ≡ h+k−1−J*(MC+q*MF)  (mod U).
```

Positive `F,alpha` and positive transport carrier `q−F−alpha` imply
`2q−1≤G'≤q²−q−1`. Since `U=q⁶s²`, an additional necessary condition is
that `gcd(s²,q²−1)` divide the right-hand side. Even when it does, the
bounded range for `G'` and the transport equation may leave no usable
rank. These statements are algebraic necessary conditions, not a proof
that repair is impossible at the compact44 ports.

The [previous exact partial example](../p64-qcube72-free-main-obstruction/README.md)
has `q=4`, `U=h=4096`, `k=10`, `beta=1`, `J=3`, `K0=1`, `w=1`,
`MC=MF=0`. For *any* positive `F,alpha` with positive transport carrier,
`7≤G'≤11`, so

```
3940 ≤ h+k−1−R' = 4105−15*G' ≤ 4000 < U.
```

Consequently no such rank can give the inverse divisibility, even before
requiring transport. The exact checker enumerates the three possible
`(F,alpha)` pairs; only `(1,1)` also permits positive transport `z`, namely
`z=1`. Changing `T` cannot repair this divisibility while the specified
coordinates and ports remain fixed.

The partial example has `M=W=Lt=0`, but its first-unit norm target is
nonsquare and its complete graph output is nonzero. It is **not a full
zero**, uses ports different from the compact44 tuple, and does not disprove
a different witness normalization or zero-existence equivalence. A genuine
alternative inverse could still change other coordinates (including `q`,
`w`, `s`, or the Pell parameters); this packet does not examine those maps.

[`check.py`](check.py) pins the earlier exact partial result, checks the
q=4 arithmetic and exhausts the possible positive carrier pairs. Its
[result](result.json) and this paper derivation do not constitute a Lean
proof. No Lean was run. Reproduce with:

```sh
nice -n 19 ionice -c 3 python3 -I -S -B Computability/DiophantineConsistency/research/p64-qcube72-rank-repair-obstruction/check.py
```

| Artifact | SHA-256 |
| --- | --- |
| `check.py` | `817d76d1436168d14a039a2b462fe9b0cff9e50df9b24ea234971c1f0151638b` |
| `result.json` | `e5684a452d6a8d9ff446e2845edef99642bfcbec954e9f0dd9c5d2d6d44f12ab` |
