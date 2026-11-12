# Forced w: 14 natural inputs, 79 operations, degree 107

This proposed graph deletes `w=n_w+1` from the proposed
[14/80/107 natural forced-gamma graph](../ordinary14-natural-forced-gamma80/)
and uses `n_w` directly. It has 14 nonnegative inputs, 79 live binary
operations and exact degree 107 at the authenticated compact44 ports. The
local zero maps require only integer `beta>0` and `K0>=0`, with arbitrary
integer MC and MF. The 80 parent's stronger rank-window, fixed-port, and
endpoint qualifications remain inherited. The elementary divisibility
argument has an [independent review](../../reviews/ordinary14-natural-forced-w79-independent/README.md); it is external mathematics, not a
Lean/iPRA theorem, PDF or byte binding, provider replay, or minimum claim.

## Graph and zero maps

Deleting the w increment and retargeting its consumer gives the new graph.
For arbitrary signed integer inputs and ports, its output at `w=g` equals
the 80 output at `n_w=g−1`, with all other coordinates unchanged. An 80
natural zero therefore maps to a 79 zero by incrementing `n_w`. Conversely,
the argument below forces `w>0` at every natural 79 zero; subtracting one
then gives an 80 natural zero. The maps are inverse on zeros.

## Units and the J=0 branch

Suppose the new graph vanishes with `w=0`. Then `X=q*w=0`, so
`m=X*Y²=0`, `ell=0`, and the first product factor is simply `F0=r²`. The
other three restricted factors `F1`, `Fa`, and `Fs` cannot be −1 modulo 4
for arbitrary integer inputs. As the five factors multiply to one, `F0`
is a nonnegative integer unit and those three restricted factors must also
be +1; consequently the guard factor is +1.

If `J=0`, then `b=0`, `q=1`, `qF=−n_F<=0`, and
`C=qF−alpha<=−1`, because the alpha increment remains. With `X=0` and
`K0>=0`, the guard is

```
C*(X+K0)+qF−b*n_h <= 0,
```

contradicting the guard unit +1. Thus `J>0`. Since `beta>0`,
`q=1+J*beta>=2`. The retained s increment gives `s>=1`, so

```
Y=q³*s>=q³>0,  a=XY+Y=Y,
H=4*Y+3,  U=Y*q²>0,  Delta=a²+H.
```

## Main-norm divisibility contradiction

The main factor is +1, so its residual equation is

```
Dstar²=U²*(1+(a²+H)*c²).
```

For integers, `U² | Dstar²` implies `U | Dstar`; write the possibly signed
quotient as `d=Dstar/U`. Since `X=0`, the literal main expression has the
form `Dstar=U*a*c+H*shift`. Thus `H | U*(d−a*c)`, while the norm gives

```
(d−a*c)*(d+a*c)=1+H*c².
```

Multiplying this identity by U and using the preceding divisibility shows
`H | U`. But `4*U=(H−3)*q²`, so `H | 3*q²`. This is impossible because
`3*q²>0` and

```
H=4*Y+3 >= 4*q³+3 > 3*q².
```

No sign assumption on Dstar, gamma, f, r, or y is used. This contradiction
proves `w>0` and completes the stated zero maps.

## Count and degree

All 79 binary gates, 14 inputs and four ports are live. The affine edit
preserves the parent's degree-107 upper bound. The all-inputs-equal ray at
authenticated P72/P115 ports has degree 107 modulo 1,000,000,007 with
leading coefficient 419359493, proving exact specialized integer degree
107. The checker pins both graphs and port bytes, verifies the gate edit and
liveness, checks 300 signed modular identities and actual port bounds,
samples the divisibility inequalities, and computes the ray. Its finite
controls do not replace the unbounded proof or inherited endpoint.

```
python3 -I -S -B research/ordinary14-natural-forced-w79/check.py > /tmp/natural14-w79.json
cmp /tmp/natural14-w79.json research/ordinary14-natural-forced-w79/result.json
```
