# A symbolic positive zero outside the double-gap image

The conditional 85/84-operation double-gap rewrite in
[`../adaptive-double-gap-conditional-85-84/`](../adaptive-double-gap-conditional-85-84/README.md)
cannot have a positive-witness reverse transport that works uniformly for all
integer ports, even if `beta >= 0`. The construction below gives positive
values for **all 13 rewritten witnesses** and integer auxiliary ports at which
both rewritten polynomials vanish, but `q=1 < h=2`; the inverse has `F=-1`.

**This does not address the actual fixed ports.** Here `beta=0`, `K0=-2`,
`MF=0`, and `MC` is a specifically defined negative integer. The project's
actual first port is positive and its other fixed ports have different values.
Thus this is not a counterexample to fixed-port equivalence, and it does not
establish or refute `Con(ZFC)`. The witness below is a finite exact symbolic
integer construction; its enormous Pell power is **not expanded** by the
checker or printed in decimal. A separate [independent mathematical review](../../reviews/double-gap-uniform-counterexample-independent-audit/README.md)
passed; no Lean formalization is claimed.

## The witness

Put

```text
s + c sqrt(15) = (4 + sqrt(15))^15
c = 3572846569215,  s = 13837575261124,
k = c - 1,  R0 = (-s - (1+2c))/11 + k - 2 = 1665276714707.
```

All divisions displayed here are exact. Define positive integers `f,B` by

```text
f + B sqrt(15) = (s + c sqrt(15))^c.
```

The coefficient `B` is divisible by `c²`: the coefficient of `sqrt(15)` in
the binomial expansion has first term `c*c*s^(c-1)` and every remaining odd
term contains at least `c³`. Thus `i=15B/c²` is a positive integer. Since
`s²-15c²=1`, also `f²-15B²=1`. Set `I=15B`, so

```text
I = c² i,       I² = 15(f²-1).
```

Define integer polynomials `v_j(t), w_j(t)` by

```text
v_0 = w_0 = 1,   v_1 = 4t-3,   w_1 = 4t-1,
v_(j+1) = (4t-2)v_j - v_(j-1),
w_(j+1) = (4t-2)w_j - w_(j-1).
```

Let `t=I²`, `V=v_7(t)`, `y=w_7(t)`, and `P=(V+c)/f²`. The checker verifies
exactly in `Z[t]` that

```text
t v_7(t)² - (t-1) w_7(t)² = 1,    v_7(-15) = -c.
```

Consequently `V+c` is divisible by `t+15=15f²`, and `P` is an integer.
Also `f>=s>4`, `t>=225`, and induction on the recurrence gives
`v_7(t)>=t^7`. Since `f²<=t` and `225^6>c`, one has `P>c`.

Set the rewritten witnesses and auxiliary ports to

```text
J=X=Y=T=r=eta=1,    zeta=c-2,
h=2,  C=1,          f=f,  i=15B/c²,  y=w_7(I²),
gamma=P-c+R0,
beta=0,  K0=-2,  MC=c-P,  MF=0.
```

All witnesses are positive: in particular `y>0` by its recurrence and
`gamma>R0>0` since `P>c`. Here `q=1+J beta=1`, so `q<h` and the inverse
coordinate `F=q-h=-1` is not positive. The other inverse coordinate is
`alpha=h-C=1`.

## Why the residuals vanish

The old integer graph, evaluated at these inverse coordinates, has
`a=2`, `Delta=15`, `H=11`, `U=1`, `M=0`, `c=eta+Y(eta+zeta)`,
`B_t=C(X+K0 q)-Fq=0`, and `R=MC=c-P`. Its first Pell residual is zero:
`Z=-B_t=0=M`. Its main signed root satisfies

```text
Dstar = (1+2c) + 11(gamma + R + 2 - k) = -s,
s² = 1 + 15c²,
```

so the main residual is zero. The strong residual is zero by
`I²=15(f²-1)`. Finally, `T c-R=P` gives the graph's ordinate
`V=f²P-c=v_7(I²)`. The verified polynomial identity gives
`y²-I²(y²-V²)=1`, so the auxiliary residual is zero. Therefore the
sum of four squares vanishes; each of the product graph's four factors is 1,
so its product-minus-one also vanishes. The previously checked ring identity
for the double-gap rewrite transfers this integer evaluation to the new
positive coordinates.

Run `python3 check.py` from this directory or
`python3 Computability/DiophantineConsistency/research/double-gap-uniform-counterexample/check.py`
from the repository root. The script pins the two graph bytes, checks the
relevant graph wiring and exact small Pell constants, expands the polynomial
Pell identity, and checks the divisibility and positivity certificates. It
rejects optimized Python. The exponentiation `(s+c sqrt(15))^c` is justified
by the binomial and norm identities above, not computed by the program.
