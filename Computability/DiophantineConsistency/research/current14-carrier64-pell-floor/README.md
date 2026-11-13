# Pell floor and a rank lower bound

Subject to the already reviewed application of `P72Exact.indices_ordinary`
and `P72Power.power_of_mod`, every positive 64-candidate zero with
`q>=16`, `R>=26`, and `R+1<E` satisfies the exact formula

```
X=2^R, R=2N+1, N>=13,
Y = (1/2) * sum_{i=0}^N binom(2N,i)*X^(N-i).
```

The right side is an integer. This is an external argument from the existing
theorem statements and the elementary estimates below, **not** a new Lean
client or an independent replay of those theorems' source/object ancestry.
It does not prove the 64-gate reverse equivalence.

## Bounding the Pell ratio

As in `../current14-carrier64-sharp-growth/`, put

```
A=Y*(X+1)+2,  P=2*X*Y²+1,
c=psi_A(2N+1),  k=2*psi_P(N+1),  Y<c/k<Y+1.
```

The last strict inequalities use positive `eta,zeta` and `c=Y*k+eta`.
The recurrence bounds `(2p-1)^(t-1)<=psi_p(t)<=(2p)^(t-1)` give

```
L^N/2 <= c/k <= U^N/2,
L=(2A-1)²/(2P),  U=(2A)²/(2P-1).
```

Set `B0=(X+1)²/X` and `H=B0^N/2`. An exact polynomial identity gives

```
X*(2A-1)²-(X+1)²*(2P)
  = 12XY(X+1)+9X-2(X+1)² > 0.
```

Thus `L>B0`. Also, for `X>=2,Y>=1`,

```
U < B0 + 4(X+1)/(XY) + 4/(XY²) < B0 + 9/Y.
```

The previously reviewed sharp window gives `Y>X^N/2`. Since
`X=2^(2N+1)>144N` for `N>=13`, the binomial/geometric estimate gives

```
U^N/2 - H < 9N*B0^(N-1)/Y < 36N/X < 1/4.
```

For the middle bound use `B0^(N-1)<2X^(N-1)` and `Y>X^N/2`. Hence
`H<c/k<H+1/4`.

Let

```
T = (1/2) * sum_{i=0}^N binom(2N,i)*X^(N-i).
```

It is integral: `X` is even and the central binomial coefficient is even.
The remaining terms in the expansion of `H` are positive and total less
than `2^(2N)/(2X)=1/4`, because `X=2^(2N+1)`. Therefore
`T<H<c/k<H+1/4<T+1/2`. Since `Y<c/k<Y+1`, necessarily `Y=T`.

## Binary consequence and gap bounds

Every noncentral term of `T` is divisible by `X/2=2^(2N)`, while the central
term is a positive integer below `2^(2N-1)`. Thus it alone determines
`v2(Y)`. Legendre's factorial formula gives

```
v2(binom(2N,N)) = popcount(N),
v2(Y)=popcount(N)-1,
popcount(R)=v2(Y)+2.
```

As `q|X`, write `q=2^t`. Since `q³|Y`,
`popcount(N)>=3t+1`; the least integer with that many set bits is
`2^(3t+1)-1`. Consequently

```
N>=2q³-1,   R>=4q³-1.
```

For the candidate's scalar gap `G=q(q-F)-C`, positivity of `F,C` alone
also gives `G<=q²-q-1`, with **no** assumption `q-F-C>0`. For ports in the
current scalar box `0<MC<beta<MF<2beta`, `beta*J=q-1` implies

```
MC*J+q*MF*J < (2q+1)*(q-1).
```

Substituting these bounds in the rank formula yields the unconditional
scalar upper bound `R<q⁴-q³`. In particular, for a positive zero with
`R>=26`, `R+1<E` is automatic because `E=w*s*q⁴>=q⁴`, so the window
assumption in the first paragraph may be replaced by `R>=26`.

Conversely `R>=4q³-1` and the same mask bound force `G>=4q-1`: if
`G<=4q-2`, then

```
R < (4q-2)*(q²-1)+(2q+1)*(q-1) < 4q³-1.
```

These bounds rule out the previous `G=1` partial families as full zeros in
the rank window. They still do not force the old residue condition or its
transport congruence, and do not rule out a candidate zero with `R<26`.

## Checks

`check.py` pins the reviewed sharp-window receipt and current graph. It checks
the displayed base identity in an exact sparse polynomial ring, tests the
floor/error inequalities at 32 exact Pell instances, verifies the central
binomial valuation for 2,000 finite integers, and checks the rank polynomial
algebra for 998 small `q`. These controls do not replace the proofs above and
do not materialize the actual huge Pell values.

```sh
python3 -I -S -B research/current14-carrier64-pell-floor/check.py > /tmp/carrier64-pell-floor.json
cmp /tmp/carrier64-pell-floor.json research/current14-carrier64-pell-floor/result.json
```

No new Lean run, native proof replay, or PDF interpretation is performed.
The independent external review is in
`../../reviews/current14-carrier64-pell-floor-independent/`.
