# Forced X in the C-fold graph: 13 natural inputs, 95 operations, degree 28

This proposed graph deletes `X=n_X+1` from the proposed
[13/96/28 forced-gamma C-fold square graph](../ordinary13-natural-cfold-forced-gamma96-degree28/)
and uses the input directly. It has 13 nonnegative inputs, 95 live binary
operations, and exact degree 28 at authenticated compact44 ports. The
local zero maps require only integer `beta>0` and `K0>=0`, with arbitrary
integer MC and MF; the parent's stronger calibration, rank, fixed-port,
and endpoint qualifications remain inherited. An [independent review](../../reviews/ordinary13-forced-w-x-independent-aggregate/README.md)
checks the forced-input maps. This is external mathematics, not a Lean/iPRA theorem, PDF or
byte binding, fresh provider replay, or minimum claim.

## Zero maps and the X=0 branch

The candidate at `X=g` equals the parent at `n_X=g−1` for arbitrary signed
integer inputs and ports. Incrementing the parent's `n_X` maps a parent
zero to a candidate zero; after proving `X>0`, decrementing it maps back.
These maps are inverse on zeros.

At a candidate zero all four square residuals vanish. Suppose `X=0`. Write

```
b=J*beta, q=b+1, M=q³*b, C=q−F−alpha,
Bt=C*(X+K0*q)−F*q,
Z=M*(ell+k+r−k*C)+Y*b−q³*Bt.
```

If `J=0`, then `b=M=0`, `q=1`, `C=1−F−alpha<0`, and
`Bt=C*K0−F<0` because F and alpha are positive and `K0>=0`. Thus
`Z=−Bt>0`, contradicting the first norm `Z²=M²*(1+ell*(ell+k))=0`.
Therefore `J>0`, so `q>=2` and `M>0`. The first norm gives `M|Z`. Reducing
the displayed Z modulo `q³` then gives `q³|Y*b`; as `gcd(q,b)=1`,
`q³|Y`. Since the Y input remains positive, `Y>=q³`.

At `X=0`, the main quantities are `a=Y`, `H=4Y+3`, `U=Y*q²>0`, and
`Delta=a²+H`. Its norm gives `U|Dstar`; let the signed quotient be
`d=Dstar/U`. The literal main expression is `Dstar=U*a*c+H*shift`, so

```
H | U*(d−a*c),  (d−a*c)*(d+a*c)=1+H*c².
```

Consequently `H|U`. The identity `4U=(H−3)q²` then gives `H|3q²`, which
contradicts `0<3q²<H=4Y+3` and `Y>=q³`. Thus `X>0`, completing the
maps. This local proof does not use the sign of the main root, gamma, or
MC/MF.

## Count and degree

All 95 binary operations, 13 inputs and four ports are live. The affine
edit preserves the parent's degree-28 upper bound. The all-inputs-equal ray
at authenticated P72/P115 ports has degree 28 modulo 1,000,000,007 and
leading coefficient 59132194, proving exact specialized integer degree 28.
The checker pins both graphs and port bytes, verifies the gate edit and
liveness, checks 300 signed modular identities and actual port bounds,
samples divisibility inequalities, and computes the ray. Finite controls
do not replace the unbounded proof, calibration, or inherited endpoint.

```
python3 -I -S -B research/ordinary13-natural-cfold-forced-x95-degree28/check.py > /tmp/natural13-cfold-x95.json
cmp /tmp/natural13-cfold-x95.json research/ordinary13-natural-cfold-forced-x95-degree28/result.json
```
