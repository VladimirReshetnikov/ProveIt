# Forced w: 13 natural inputs, 86 operations, degree 99

This proposed graph deletes `w=n_w+1` from the proposed
[13/87/99 forced-gamma graph](../ordinary13-natural-forced-gamma87/) and
uses the input directly. It has 13 nonnegative inputs, 86 live binary
operations, and exact degree 99 at the authenticated compact44 ports. The
local zero maps require only integer `beta>0` and `K0>=0`, with arbitrary
integer MC and MF; the parent's rank/port and endpoint qualifications remain
inherited. An [independent review](../../reviews/ordinary13-forced-w-x-independent-aggregate/README.md)
checks this graph and the related C-fold variants. This is external mathematics,
not a Lean/iPRA theorem, PDF or byte binding, fresh provider replay, or
minimum claim.

## Coordinate maps and the zero-w branch

The candidate at `w=g` equals the parent at `n_w=g−1` for arbitrary signed
integer inputs and ports. A parent zero maps to a candidate zero by
incrementing `n_w`; a candidate zero maps back by decrementing it after
proving `w>0`. The maps are inverse on zeros.

At a candidate zero, all four unit-product factors equal +1 by the existing
all-integer modulo-four exclusions. Suppose `w=0`; then `X=q*w=0`, and the
first norm says `Z²=b²` with

```
b=J*beta, q=b+1, C=q−F−alpha,
B=C*(X+K0)−F, Z=b*(ell+k+r−k*B)−B.
```

If `J=0`, then `b=0`, `q=1`, `C=1−F−alpha<0` and
`B=C*K0−F<0` because the F and alpha increments remain and `K0>=0`.
Hence `Z=−B>0`, contradicting `Z²=0`. Thus `J>0` and `q>=2`. The retained
s increment gives `Y=q³*s>=q³>0`; at `X=0`, `a=Y`, `H=4Y+3`,
`U=Y*q²>0`, and `Delta=a²+H`.

The main unit implies `Dstar²=U²*(1+Delta*c²)`, so `U|Dstar`. Write the
possibly signed quotient `d=Dstar/U`. The literal main expression at
`X=0` has the form `Dstar=U*a*c+H*shift`, yielding

```
H | U*(d−a*c),   (d−a*c)*(d+a*c)=1+H*c².
```

Multiplying the second equation by U shows `H|U`. Since
`4U=(H−3)q²`, it follows that `H|3q²`, impossible because
`0<3q²<H=4Y+3` and `Y>=q³`. Thus `w>0`. No sign or positivity of gamma,
the signed main root, or MC/MF is used in this local argument.

## Count and degree

All 86 binary operations, 13 inputs, and four ports are live. The affine
edit preserves the parent's degree-99 upper bound. The all-inputs-equal ray
at the authenticated P72/P115 ports has degree 99 modulo 1,000,000,007 and
leading coefficient 663418019, proving exact specialized integer degree
99. The checker pins both graphs and port bytes, verifies the gate edit and
liveness, checks 300 signed modular identities and actual port bounds,
samples divisibility inequalities, and computes the ray. Finite checks do
not replace the unbounded proof or inherited endpoint.

```
python3 -I -S -B research/ordinary13-natural-forced-w86/check.py > /tmp/natural13-w86.json
cmp /tmp/natural13-w86.json research/ordinary13-natural-forced-w86/result.json
```
