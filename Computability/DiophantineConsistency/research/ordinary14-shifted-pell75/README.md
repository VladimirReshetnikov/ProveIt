# Positive shifted Pell witness: 14 inputs, 75 operations, degree 97

This candidate trades one operation for a lower degree than the reviewed
[14/74/107 positive-guard graph](../ordinary14-positive-guard74/). The
positive-zero existence equivalence below is an external mathematical
argument, not a Lean or iPRA theorem, a new PDF/JSON binding, a replay of the
provider, or a global minimum claim. The parent endpoint and all of its
qualifications are inherited. An [independent review](../../reviews/ordinary14-shifted-pell75-independent/README.md)
checks the zero map, algebraic identities, and specialized degree.

Write `ell = E*kY` and `k = eta+zeta`, as in the parent. For positive inputs
and `beta>0` both `ell` and `k` are positive. The parent's first factor is

```
F0_old = r_old^2 - ell*(ell+k).
```

Replace its positive input `r_old` with a new positive input `t` and put

```
F0_new = t^2 + ell*(2*t-k).
```

The identity `F0_new = F0_old` under `r_old=ell+t` holds for arbitrary
integer inputs and ports. The other four factors contain neither `r_old`
nor `t`. The new graph therefore maps every positive zero to a positive
parent zero with all other inputs unchanged.

Conversely, at any positive parent zero, the parent's reviewed five-unit
argument forces `F0_old=1`. In particular,

```
r_old^2 = ell^2 + ell*k + 1 > ell^2.
```

Since `r_old` and `ell` are positive integers, `r_old>ell`. Thus
`t=r_old-ell` is a strictly positive integer and the exact identity maps
that parent zero to a new zero. This argument uses the parent's unit-factor
result and does not prove it anew. In particular, no conclusion follows for
arbitrary port values outside the parent's hypotheses (`beta>0`, `K0>=0`).

## Operation count and degree

Delete the four parent gates for `ell+k`, `r_old^2`, their product, and their
subtraction. Add the five gates for `t^2`, `2*t`, `2*t-k`,
`ell*(2*t-k)`, and their sum. The result has 75 live binary operations,
14 positive witness inputs, and the same four fixed numeral ports as its
parent.

The specialized total degree is exactly 97. For the upper bound, ordinary
gate degrees give `deg(F0_new)<=12`, `deg(Fa)<=30`, `deg(Fs)<=22`, and
`deg(guard)<=3`. Although a gatewise bound on `F1=1+A1` is 34, cancellation
gives `deg(F1)<=30`: using the parent's definitions `Dstar=U*b0+H*shift`,
`b0=X+a*c`, and `Delta=a^2+H`, expand

```
A1 = U^2 * (X^2 + 2*X*a*c - H*c^2 - 1)
   + 2*U*b0*H*shift + H^2*shift^2.
```

The terms on the right have degree at most 28, 30, and 26, respectively.
The complete final product therefore has degree at most
`12+30+30+22+3=97`. For the matching lower bound, the checker authenticates
the compact44 port bytes against both existing bindings and evaluates the
univariate ray in which `t=2*x` and all other positive witnesses equal `x`.
Modulo 1,000,000,007, the ray has degree 97 with leading coefficient
979034495. Thus the integer polynomial has a nonzero degree-97 term. The
factor ray degrees are 12, 30, 30, 22, and 3. The different coefficient
for `t` is necessary: the all-witnesses-equal ray makes `2*t-k` vanish.

The checker also verifies the exact graph delta, topology and liveness, and
200 finite signed transport identities. Those finite tests do not replace
the positive-domain proof above or establish the inherited source endpoint.

```
python3 -I -S -B research/ordinary14-shifted-pell75/check.py | cmp - research/ordinary14-shifted-pell75/result.json
```
