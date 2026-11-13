# Forced J: 14 natural inputs, 81 operations, degree 107

This proposed graph deletes one gate from the reviewed
[14/82/107 natural graph](../ordinary14-root74-natural-forced82/). It has 14
nonnegative inputs, 81 live binary operations and exact degree 107 at the
authenticated compact44 ports. Its natural-zero existence agrees with the
82 parent when the integer ports satisfy `beta > 0` and `K0 > 0`, with
arbitrary `MC` and `MF`. These local hypotheses strengthen the parent's
`K0 >= 0` condition. The checker authenticates the actual port bytes and
verifies that both `beta` and `K0` are strictly positive. An [independent
review](../../reviews/ordinary14-natural-forcedj81-independent/README.md)
checks the unit argument and degree certificate. This is external mathematics, not a Lean/iPRA theorem, PDF or
physical-byte binding theorem, fresh provider replay, or minimum claim.

## Exact graph edit and zero maps

The 82 graph begins with `J=n_J+1`. Delete that gate and replace `J` at its
consumers with the natural input `n_J`. Over arbitrary signed integers the
81 output at `n_J=J` equals the 82 output at `n_J=J−1`, with all other
inputs unchanged. A natural 82 zero therefore maps to a natural 81 zero by
incrementing `n_J`.

Conversely, suppose a natural 81 valuation makes its output vanish. The
output is a product of five integer factors minus one, so **every factor is
an integer unit**, either +1 or −1. In the case `J=0`, we have

```
b=J*beta=0, q=b+1=1, X=q*w=w>=1,
qF=b−n_F=−n_F<=0, C=qF−alpha<=−1,
guard=C*(X+K0)+qF−b*n_h <= −2.
```

Here `w=n_w+1` and `alpha=n_alpha+1` remain positive, and `K0>=1` by the
port hypothesis. The guard cannot be an integer unit, contradiction.
Therefore `J>=1`, and subtracting one from it gives a natural 82 zero by
the exact identity. This proof requires no negative-Pell exclusion at
`J=0`; it only uses the unit property of an integer product equal to one.
The two coordinate maps are inverse on zeros.

## Count and exact degree

All 81 binary gates, 14 inputs and four fixed ports are live. The affine
coordinate change preserves the parent's degree-107 upper bound. The
candidate's all-inputs-equal ray at the authenticated P72/P115 ports has
degree 107 modulo 1,000,000,007 with leading coefficient 419359493, so its
specialized integer degree is exactly 107. The checker pins both graphs and
the port bytes, verifies the gate edit and liveness, checks 300 signed
modular affine identities, and computes the degree ray. Its finite controls
do not replace the unbounded unit argument or prove the inherited endpoint.

```
python3 -I -S -B research/ordinary14-natural-forcedj81/check.py > /tmp/natural14-forcedj81.json
cmp /tmp/natural14-forcedj81.json research/ordinary14-natural-forcedj81/result.json
```
