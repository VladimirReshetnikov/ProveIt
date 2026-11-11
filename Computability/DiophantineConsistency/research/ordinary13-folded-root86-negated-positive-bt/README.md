# Positive Bt suffices to repair a sign-reversed folded zero

This is an elementary integer argument submitted for independent review. For
any fixed integer ports with **beta>0**, every positive zero of the
sign-reversed 86-gate candidate in `../ordinary13-folded-root86-negated/` with
`Bt>0` admits a positive zero of the 88/30 parent while keeping the other
twelve coordinates fixed. The proof may switch the first Pell root, so it does
not require the given sigma to satisfy `k*Bt>sigma`.

The remaining reverse-existence question is whether the candidate can have
positive zeros with `Bt<=0`, and if so whether such zeros can be replaced by
ones with `Bt>0`. This packet does not establish either answer, an iPRA or
Lean theorem, or a global existence equivalence.

## Root and divisibility consequences

Write `b=J*beta`, `q=b+1`, `M=q³*b`, `U=Y*q²`, `m=X*Y²`,
`k=eta+zeta`, `ell=m*k`, `a=XY+Y`, `c=kY+eta` and
`Delta=(a+1)(a+3)=(a+2)²−1`. All named factors except potentially the
integer expressions Bt and Dstar are positive; k>=2. Let the signed-candidate
first-root input be sigma and its first expression be

```
Z=M*(ell+k−sigma)+Y*b−q³*Bt.
```

A zero of the four-square output has both `A0=A1=0`, giving

```
Z²=M²*(1+m*(m+1)*k²),
Dstar²=U²*(1+Delta*c²).
```

For integers, `M²|Z²` and `U²|Dstar²` imply `M|Z` and `U|Dstar` by prime
valuations. Set `tau=|Z|/M`, `d=|Dstar|/U`. Reducing the first expression
modulo `q³` and `b`, using `gcd(q,b)=1`, yields

```
Y=q³*s,   Bt=b*t,   tau²=1+m*(m+1)*k²,
d²=1+((a+2)²−1)*c²
```

for integers s>=1 and t. Under Bt>0 we have t>=1 and Bt>=1.

## The main root excludes k=2

If k=2 then positive eta and zeta both equal 1, so `c=2Y+1`. Since
`a=XY+Y>=2Y`, we have `1<c<2(a+2)`. Consequently

```
((a+2)*c−1)² < 1+((a+2)²−1)*c² < ((a+2)*c)²,
```

contradicting integral d. Thus k>2.

## Elementary first-Pell descent

Given `tau²−m(m+1)k²=1`, m>=1 and k>2, set

```
tau' = (2m+1)*tau − 2m(m+1)*k,
k'   = (2m+1)*k − 2*tau.
```

Both are positive integers: `tau'>0` follows by comparing the positive
squares; `k'>0` follows from
`((2m+1)k)²−(2tau)²=k²−4>0`. Also `k'<k` because tau>m*k, and the
same Pell equation holds for tau',k'. There is no solution with k'=1,
because `m² < m(m+1)+1 < (m+1)²`. Hence `k'>=2` and
`tau'>m*k'`, so tau'>=2m+1. Inverting the linear transformation gives

```
k=(2m+1)*k'+2*tau' >= 8m+4.                     (1)
```

Moreover

```
tau²−(m*k+k/4)² = (m/2−1/16)*k²+1 > 0,
```

so `tau−ell>k/4>2m>=2Y>=2s`.

## Choose the positive root

Define

```
r_old = k*Bt − ell − k − s + t + tau.
```

This is an integer and

```
r_old = k*(Bt−1)+t−s+(tau−ell) > 0.
```

The parent first expression then equals `M*tau`, and its first residual is
zero. All other parent residuals agree with the signed candidate and are
independent of the first coordinate, so all vanish. The resulting thirteen
parent inputs are strictly positive. No assumption about the present sigma's
root branch or the sign of its direct reverse image was needed.

The checker pins both graphs and their exact coordinate relation and runs
finite Pell/descent and consecutive-square controls. These do not replace the
unbounded proof. No Lean run, PDF interpretation or source ancestry replay is
performed.

Independent external review is recorded in
`../../reviews/ordinary13-folded-root86-negated-positive-bt-independent/`.
