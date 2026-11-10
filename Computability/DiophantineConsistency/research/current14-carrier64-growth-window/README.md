# A stronger Pell growth condition in the rank window

Under the same existing-theorem application reviewed in
`../current14-carrier64-bad-gap-exclusion/`, every positive candidate zero
with `q>=16`, `R>=26`, and `R+1<E` has odd `R`, `X=2^R`, and satisfies

```
X^N < 2*(Y+1)*6^N,       2Y < (18X)^N,
N=(R-1)/2.
```

This is an external consequence of the cited generic index and power
theorems and the elementary Pell bounds below. It is not a new Lean client,
an independently replayed ancestry closure, a full zero, or a proof of the
64-gate candidate's reverse equivalence.

## Derivation

The reviewed bindings give main Pell index `r=R` and first Pell index
`j=(R+1)/2=N+1`. Put `m=E*Y=X*Y²` and `a=E+Y=Y*(X+1)`. With
`psi_p(0)=0`, `psi_p(1)=1`, `psi_p(t+1)=2p*psi_p(t)-psi_p(t-1)`, we have

```
c=psi_(a+2)(R),          k=2*psi_(2m+1)(N+1),
c < (Y+1)*k.
```

The last inequality follows from `c=Y*k+eta` and positive
`zeta=k-eta`. For every `p>=2`, `t>=1`, monotonicity and induction give

```
p^(t-1) <= psi_p(t) <= (2p)^(t-1).
```

Since `a+2>XY`, `2*(2m+1)<=6XY²`, and `R-1=2N`, it follows that

```
(XY)^(2N) < 2*(Y+1)*(6XY²)^N.
```

Cancel the positive factor `X^N Y^(2N)` to obtain the stated inequality.
For the other direction, `c>Y*k`, `a+2<=3XY`, and `2m+1>=2XY²` give

```
2Y*(2XY²)^N < (6XY)^(2N).
```

Cancelling the same positive factor yields `2Y<(18X)^N`. These are necessary
conditions only; they do not solve the two-Pell-index compatibility or the
reverse scalar normalization.

## Consequence for the reviewed partial family

The fixed-port partial assignment in
`../current14-carrier64-power-window-partial/` has `R` odd, `R>3B`,
`B=94517`, `X=2^R`, and `Y=X*2^(3B)<X²`. It satisfies the first norm,
transport, rank window and the weaker `X<Y` condition. If it were a full
zero, the inequality above would apply. But `N>=13` and `X>36` imply
`(X/6)^N > X^6`, while `2*(Y+1)<4X²<X^6`; this contradicts the inequality.
Thus **that particular partial assignment cannot extend to a full zero**,
subject to the previously reviewed theorem application. Other choices of `s`
and other outside-guard candidate inputs remain open.

The modified partial assignment in
`../current14-carrier64-growth-compatible-partial/` chooses `s=2^(R²)` and
does satisfy the first inequality, but its `Y=2^(R²+3B)` violates the second.
Indeed `18<2^5` and, for `R>=27`,
`R²+3B>(R+5)(R-1)/2=(R+5)N`; hence `Y>(18X)^N`. It too cannot be completed
to a full zero under the same theorem application. Other `s` values, including
those within the two-sided growth window, remain untested.

The checker pins the partial receipt and generic theorem sources, checks the
recurrence bounds for 1,160 small pairs and both growth contradictions on
bounded illustrative exponent choices. Those finite controls do not replace
the proof and do not materialize the actual enormous witnesses.

```sh
python3 -I -S -B research/current14-carrier64-growth-window/check.py > /tmp/carrier64-growth.json
cmp /tmp/carrier64-growth.json research/current14-carrier64-growth-window/result.json
```

No Lean process, native proof replay, or PDF interpretation is performed.
The independent external review is in
`../../reviews/current14-carrier64-growth-window-independent/`.
