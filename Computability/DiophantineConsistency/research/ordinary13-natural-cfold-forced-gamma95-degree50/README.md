# Forced gamma and C-fold unit product: 13 natural inputs, 95 operations, degree 50

This proposed graph deletes `gamma=n_gamma+1` from the proposed
[13/96/50 natural C-fold unit-product graph](../ordinary13-natural-cfold-product96/).
It has 13 nonnegative inputs, 95 live binary operations and exact degree 50
at the authenticated compact44 ports. Its natural-zero existence agrees
with that parent when `beta>=46`, `K0>=0`, `0<MC<beta`, and `0<MF<2*beta`,
using the rank-window theorem and elementary Pell descent. The actual
authenticated ports satisfy these bounds. Both packets have independent
reviews; see the [95-operation review](../../reviews/ordinary13-natural-cfold-forced-gamma95-degree50-independent/README.md).
This is external mathematics, not a Lean/iPRA theorem, PDF or byte
binding, fresh provider replay, or minimality claim.

## Zero maps and forced gamma

Delete the gamma increment and use the input directly. The candidate output
at `gamma=g` equals the parent output at `n_gamma=g−1` for all signed
integer valuations and ports. A parent zero maps to the candidate by
incrementing `n_gamma`; a candidate zero maps back by subtracting one after
the proof that `gamma>0`. The maps are inverse on zeros.

At a candidate zero, its four integer factors multiply to one. Their
exclusions of −1 modulo 4, established pointwise for arbitrary integer
inputs and ports in the linked 96/50 parent packet, force all four factors
to be +1. Thus the same four residual equations hold as in the
[13/96/28 forced-gamma square graph](../ordinary13-natural-cfold-forced-gamma96-degree28/).
That packet's unbounded argument applies: positive J and f and `C>0`
follow without gamma positivity; the first norm gives `q³|Y`; rank bounds
and the Pell descent give `k> E*q+R+1`; and the main norm and direct
orientation make `gamma=0` impossible. Therefore `gamma>0`.

## Count and degree

All 95 binary gates, 13 inputs and four ports are live. The affine edit
preserves the parent's degree-50 upper bound. The all-inputs-equal ray at
authenticated P72/P115 ports has degree 50 modulo 1,000,000,007 with
leading coefficient 604845992, proving exact specialized integer degree
50. The checker pins both graphs and port bytes, verifies the gate edit and
liveness, checks actual port bounds and 300 signed modular controls,
samples the orientation inequalities and computes the ray. These controls
do not replace the unbounded proof or inherited endpoint. Compared with
the proposed 96/28 square graph, this uses one fewer gate and has higher
degree; neither dominates the other in those two measures.

```
python3 -I -S -B research/ordinary13-natural-cfold-forced-gamma95-degree50/check.py > /tmp/natural13-cfold-gamma95.json
cmp /tmp/natural13-cfold-gamma95.json research/ordinary13-natural-cfold-forced-gamma95-degree50/result.json
```
