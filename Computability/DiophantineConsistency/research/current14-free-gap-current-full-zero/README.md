# Proposed actual-port zero of the free-Pell-gap candidate

This is an **independently critically reviewed symbolic construction**. It
specifies a positive symbolic zero of the 64-gate free-Pell-gap candidate at
the actual four maintained ports, without assuming a zero of the maintained
65-gate equation. The enormous powers, Pell units and CRT progression are
not expanded. Even if verified, this would not prove unrestricted
zero-existence nonequivalence, a Lean/iPRA theorem, a PDF binding, or ZFC
inconsistency.

The candidate replaces y by positive t and the auxiliary factor by
`Na'=V²−(S²−1)t`. Its 64-gate graph and forward map were checked in
`../current14-carrier64-free-pell-gap-toy-zero/`. The independently reviewed
ordinary results `../free-pell-gap-generic-completion/` and
`../free-pell-gap-seed-characterization/` reduce construction of a candidate
zero to positive scalar/first/main/transport seed coordinates. The same
completion can choose `V²+t` nonsquare.

## Actual-port scalar fixed point

The checker authenticates the complete four pinned compressed and raw port
payloads. Let

```
beta=2^B−1, B=94517, q=beta+1, J=1,
e=28633, C=1,
F=(K+2^e) mod beta, alpha=q−F−C,
gap=beta*(q−F)+alpha,
R=gap*(q²−1)+MC+q*MF,
d=(R+1)/3,  r=2d,  h=3d/2,  lambda=d−1.
```

The actual finite calculation gives positive F and alpha, `R=3 mod 4`,
`d=0 mod 4`, and `r=e mod B`. In particular d, h, r and lambda are
positive integers, `r>=2B` and `lambda>=3B`. F has 47272 bits and
SHA-256 `411970036963b7b05d9055fb1917f3f0f636892cdf4e85b9930272e4acf56cca`;
R has 378068 bits and SHA-256
`3dd9c6439028ac65f4ec83ba0589e74a74221764c6d2ba342a7bd5902e9d7d3e`.

Define only symbolically

```
X=2^r,  w=2^(r−B),
Y=2^lambda,  s=2^(lambda−3B),  E=X*Y=2^R,
z=1+((K+w)*C−F)/beta.
```

Since `r=e mod B`, `w=2^e mod beta`; F was chosen so the displayed z is an
integer. It is positive because `w>=q>F`. All scalar coordinates are
positive, the literal rank equals R, and the transport factor is 1.

## Strict first/main Pell ratio

Use Pell notation
`(u+sqrt(u²−1))^j=chi_u(j)+psi_u(j)*sqrt(u²−1)`, and set

```
m=E*Y,  P=2m+1,  a=E+Y,  A=a+2,
Delta=A²−1, H=4a+3,
k=2*psi_P(h),  tau=chi_P(h),
c=psi_A(r),  D=chi_A(r).
```

The checker verifies the exact exponent identity

```
(2*Y*X)^(r−1) / [2*(4*X*Y²)^(h−1)] = Y.       (1)
```

This is checked by equality of integer exponents, not by expanding powers.
The standard bounds `(2u−1)^(n−1)<=psi_u(n)<=(2u)^(n−1)` imply

```
Y < c/k < Y+1.                                   (2)
```

For the lower bound write `r0=r−1`, `h0=h−1`,
`u=(2Y+3)/(2YX)` and `v=1/(2XY²)`. Relative to (1), the lower ratio is
`(1+u)^r0/(1+v)^h0`. Here `h0*v<1/2` and `r0*u>2*h0*v`:
`r0>=h0`, Y>=1, and X is enormous. Thus
`(1+u)^r0>=1+r0*u>1+2*h0*v>(1+v)^h0`.
For the upper bound, `2A/(2YX)<1+2/X` and `2P−1>4XY²`;
`(1+2/X)^r0<1+4r0/X`. Since `2d−1<2^(d−1)`, the last correction satisfies
`4Y*r0/X<1`. The checker verifies this inequality by comparing bit lengths,
without forming X or Y. This proves (2).

Consequently

```
eta=c−Y*k,  zeta=k−eta
```

are positive integers and the literal `k=eta+zeta`, `c=kY+eta` hold. The
first Pell factor is 1 because `ell=(E*Y)*k=m*k`; the main factor is 1 by
its Pell definition. Set

```
n=(tau−k+R)/E,
gamma=(D−X−a*c)/H.
```

Both are positive integers: `tau>k`, `tau=1 mod E`, and
`k=2h=R+1 mod E`; and the trace recurrence with `X=2^r` gives

```
D−X−a*c = H * sum_{j=1}^{r−1} 2^(r−1−j)*psi_A(j) > 0.
```

Thus all ten seed inputs in the three-factor characterization are positive,
and `N0=N1=Nt=1` at the actual ports.

## Complete the relaxed auxiliary factor

Apply the independently reviewed generic completion to the positive main
unit `(D,c)` and rank R. It chooses an even positive main-unit power
`f+L*sqrt(Delta)` with `c²|L`, sets `i=L/c²` and `S=Delta*L`, and uses CRT
to choose positive V, T and free-gap t such that

```
f²−Delta*(i*c²)²=1,
V=f²*(c*T−R)−c,
V²−(S²−1)*t=1,
V²+t is not a square.
```

This completes all five normalized factors at 1 and makes the free-gap
candidate zero, without an original-zero assumption. The nonsquare blocks
an original positive y with all other coordinates fixed. CRT and Pell
sparsity specify a witness existentially rather than enumerating it.

## Separate same-q,R old obstruction

The finite actual rank has `popcount(R)=283517`. The previously reviewed
rank-window application of the historical `P72Exact.indices_ordinary` and
`P72Power.power_of_mod` states that a maintained positive zero with this
same q,R would have canonical binomial Y of valuation
`popcount((R−1)/2)−1=283515`, below `v2(q³)=283551`. It therefore cannot
have a positive integer `s=Y/q³`. This is a **separate** conditional use of
those historical point-audited providers, not a new Lean client, fresh
transitive/dynamic-load audit, or claim that the maintained equation has no
zero at some other q,R. It is stronger than only blocking the displayed
same-coordinate repair, but still does not prove unrestricted existential
nonequivalence.

The local checker verifies all finite port, scalar, exponent and valuation
facts only. The complete construction, strict ratio, inherited Pell/CRT
lemmas and old-obstruction hypotheses have passed independent review.

```
python3 -I -S -B research/current14-free-gap-current-full-zero/check.py > /tmp/free-gap-current-full.json
cmp /tmp/free-gap-current-full.json research/current14-free-gap-current-full-zero/result.json
```

Independent external review is recorded in
`../../reviews/current14-free-gap-current-full-zero-independent/`.
