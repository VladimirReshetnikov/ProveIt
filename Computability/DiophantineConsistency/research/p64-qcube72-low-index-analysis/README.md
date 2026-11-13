# Low Pell indices under q-cube divisibility

The following **standard-integer** argument shows that the first and main
Pell data relevant to the 72 graph force main index `m≥4`, under the stated
q-divisibility and positivity hypotheses. It does not reach `m≥6`, the
sufficient large-c threshold in the signed half-index theorem, and it is not
an actual-zero extraction, Lean theorem, reverse implication, or compact44
existence result.

Assume `q≥5`, positive integers `X,Y` with `q|X` and `q|Y`, `Y≥5`,
`0<eta<k`, and

```
P=X Y²,       a=(X+1)Y,       c=kY+eta,
k=2 ycoord n (2(P−1)+1),       c=ycoord m a.
```

Here `ycoord` uses Pell base `b+2` and discriminant `(b+1)(b+3)`, as in the
repo. These assumptions hold at the intended scale only after the separate
first/main-root extraction; this packet does not claim that extraction has
been checked.

## Index comparison

`n≥1` since `k>0`. The [base comparison argument](../../Lean/DiophantineConsistency/Compact44/P72Exact.lean)
for `n<m` uses only `eta>0`, `Y≥2`, the two displayed Pell identities and
`a≤2P−1`, not the early rank congruence. Indeed `c>k`, while `m≤n` would give
`c≤ycoord n a≤ycoord n (2P−1)≤k`.

If `n=1`, then `k=2` and `eta=1`, so `c=2Y+1`. But `m>n` gives
`c≥ycoord 2 a=2(a+2)>2Y+1`, impossible. Hence `n≥2` and `m≥3`.

## Excluding `(n,m)=(2,3)`

The first two Pell powers and the third main power give

```
k = 8 X Y² + 4,
c = 4((X+1)Y+2)² − 1,
eta = c−kY
    = 4Y²((X−2Y)X+2X+1) + Y(16X+12)+15.
```

If `X≥2Y`, direct subtraction gives

```
eta−k = 4Y²((X−2Y)X+1)+Y(16X+12)+11 > 0,
```

contrary to `eta<k`. If `X<2Y`, both are multiples of `q`, so
`X≤2Y−q≤2Y−5`. Therefore

```
eta ≤ −12XY²+4Y²+16XY+12Y+15.
```

Because `X,Y≥5`, the four positive terms are at most respectively
`XY²`, `4XY²`, `XY²`, and `XY²`. Thus `eta≤−5XY²<0`, contrary to
`eta>0`. The pair `(2,3)` is impossible, and `m≥4` follows.

For the 72 q-cube coordinates, `X=wq` and `Y=q³s` give the needed positive
multiples and bounds when `q≥5`. The remaining cases `m=4` and `m=5` have
not been excluded. The finite [checker](check.py) pins the relevant Pell
sources and validates the two algebraic branches on 2,880 small q-cube
instances; these controls do not replace the universal argument above. Run
with `python3 -I -S -B check.py`.
