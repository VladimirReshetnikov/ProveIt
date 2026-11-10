# Growth-compatible partial assignment outside the old scalar domain

The stronger Pell growth inequality in `../current14-carrier64-growth-window/`
does not by itself force the missing positive-coordinate guard. At the actual
fixed ports, the following symbolic assignment satisfies transport, the first
Pell norm, the rank window, `X=2^R`, `X<Y`, and that growth inequality,
while its gap cannot come from old positive scalars with the same `q,R`.
It does **not** solve the main, strong or auxiliary norms and is not a full
candidate zero or a disproof of a more general reverse map.

As in `../current14-carrier64-power-window-partial/`, let

```
B=94517, q=beta+1=2^B, J=1, F=C=q-1,
G=1, R=(q²-1)+MC+q*MF,
w=2^(R-B), z=K+w.
```

The actual port checks give `R>=27`, `R` odd, `R>B`, and `K>0`. The exact
identities from that independently reviewed packet give `Nt=1` and `G=1`;
all displayed coordinates are positive. Instead of its scale, choose

```
s=2^(R²),  N=(R-1)/2,
X=wq=2^R,  Y=sq³=2^(R²+3B),
E=XY=2^(R²+R+3B),  m=EY=2^(2R²+R+6B).
```

These are finite symbolic integers, not materialized. They obey `R+1<E` and
`X<Y`. Also `R²+3B>R*N`, hence `Y>X^N` and consequently

```
X^N < 2*(Y+1)*6^N.
```

Thus this assignment passes the reviewed necessary growth inequality.

Let `j=(R+1)/2`, and let `(x,k)` be the symbolic Pell coefficients of
`(2m+1+2sqrt(m(m+1)))^j`. As in the reviewed partial packet,
`x=1 (mod E)`, `k=2j=R+1 (mod E)`, and `x>k>=2`. Therefore
`n=(x-k+R)/E>0`, `eta=1`, and `zeta=k-1` give `tau=x` and first norm 1.

The candidate's direct recovered `alpha=q-F-C=2-q` is negative. Every old
positive scalar assignment with the same `q` has gap at least `2q-1`, so
none can have this `G=1` and the same `R`. This says nothing about a reverse
construction changing `q` or `R`, or about whether the remaining norms are
compatible with these symbolic coordinates.

The read-only checker verifies both hashes for all four actual port payloads,
the finite rank facts and the ordinary integer exponent identities; it never
constructs `w`, `s`, or a Pell power. The gap, transport and Pell identities
are those independently reviewed in the earlier packet. No Lean run, native
proof replay or PDF interpretation is performed.

```sh
python3 -I -S -B research/current14-carrier64-growth-compatible-partial/check.py > /tmp/carrier64-growth-compatible.json
cmp /tmp/carrier64-growth-compatible.json research/current14-carrier64-growth-compatible-partial/result.json
```

The independent review of this partial assignment and its exclusion by the
second growth inequality is in
`../../reviews/current14-carrier64-growth-window-independent/`.
