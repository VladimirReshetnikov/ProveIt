# Sharper rank-window Pell growth restriction

Under the same reviewed application of existing generic index and power
theorems as `../current14-carrier64-bad-gap-exclusion/`, every positive
64-candidate zero with `q>=16`, `R>=26`, and `R+1<E` satisfies

```
X=2^R,  R odd,  N=(R-1)/2>=13,  X^N/2 < Y < X^N.
```

In particular `Y` cannot be a power of two. Since `q|X` forces `q` to be a
power of two and `Y=s*q³`, **s cannot be a power of two**. This is an
external theorem consequence, not a new Lean client or a proof of the
candidate's reverse zero-existence equivalence.

## Sharper elementary Pell bounds

For `p>=2` and `t>=1`, the recurrence for `psi_p` is monotone and gives

```
(2p-1)^(t-1) <= psi_p(t) <= (2p)^(t-1).
```

The reviewed index theorem gives `r=R=2N+1`, `j=N+1`, and

```
c=psi_A(2N+1),  k=2*psi_P(N+1),  Y*k<c<(Y+1)*k,
A=Y*(X+1)+2,    P=2*X*Y²+1.
```

For the lower bound, `c<(Y+1)k` and the Pell estimates give

```
((2A-1)²/(2P))^N < 2*(Y+1).
```

The base is greater than `X+1`: its numerator minus `(X+1)*(2P)` is
`(X+1)*(4Y²+12Y-2)+9>0`. The checker verifies this as an exact
polynomial identity. Thus `(X+1)^N<2(Y+1)`. Since `N>=13` and `X>=2`,
`(X+1)^N>=X^N+2`, giving `Y>X^N/2`.

For the upper bound, `c>Y*k`, `A<=Y*(X+2)` (as `Y>=2`), and
`2P-1>=4XY²` give

```
2Y < X^N*(1+2/X)^(2N).
```

Because `X=2^R` and `2N=R-1` with `R>=27`, `X>8N`. The binomial
coefficients are at most `(2N)^j`, so the finite binomial sum is bounded
by the geometric series `1/(1-4N/X)<2`. Hence `Y<X^N`.

If `q=2^t`, then `t<=R` and `Y=s*2^(3t)`. The strict interval becomes

```
2^(R*N-3t-1) < s < 2^(R*N-3t).
```

The exponents are nonnegative because `N>=13` and `t<=R`. The interval
contains no power of two, although it contains many other integers; this
condition alone does not resolve the reverse map.

## Effect on the symbolic partial assignment

The independently reviewed assignment in
`../current14-carrier64-two-sided-window-partial/` sets `Y=X^N`, so the
new strict upper bound excludes its extension to a full candidate zero under
the cited theorem application. That assignment remains a valid partial
witness for transport, the first norm and the earlier coarse bounds. Other
scales `s` and outside-guard scalar inputs remain open.

`check.py` pins the two prior result receipts, checks the key base identity
exactly, and runs bounded controls on the sharper Pell estimates and the
exponential inequality. Those controls do not replace the displayed proof.
No Lean run, native proof replay or PDF interpretation is performed; the
existing generic theorems retain their source/object/model ancestry limits.
The independent external review is in
`../../reviews/current14-carrier64-sharp-growth-independent/`.

```sh
python3 -I -S -B research/current14-carrier64-sharp-growth/check.py > /tmp/carrier64-sharp-growth.json
cmp /tmp/carrier64-sharp-growth.json research/current14-carrier64-sharp-growth/result.json
```
