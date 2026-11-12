# Forced X and C-fold unit product: 13 natural inputs, 94 operations, degree 50

This proposed graph deletes `X=n_X+1` from the proposed
[13/95/50 forced-gamma C-fold unit graph](../ordinary13-natural-cfold-forced-gamma95-degree50/)
and uses the input directly. It has 13 nonnegative inputs, 94 live binary
operations and exact degree 50 at the authenticated compact44 ports. Its
local zero maps require only integer `beta>0` and `K0>=0`, with arbitrary
integer MC and MF; the parent's stronger calibration, rank, fixed-port,
and endpoint qualifications remain inherited. An [independent review](../../reviews/ordinary13-forced-w-x-independent-aggregate/README.md)
checks the forced-input maps. This is external mathematics, not a Lean/iPRA theorem, PDF or
byte binding, fresh provider replay, or minimum claim.

## Coordinate maps and forced X

The candidate at `X=g` equals the parent at `n_X=g−1` for all signed
integer inputs and ports. Incrementing the parent's natural `n_X` maps a
parent zero to a candidate zero; once `X>0` is shown, decrementing it maps
back. The maps are inverse on zeros.

At any candidate zero, the four factors multiply to one and each excludes
−1 modulo 4 by the all-integer argument in the
[C-fold unit-finalizer packet](../ordinary13-natural-cfold-product96/).
Thus each factor is +1, and exactly the four residual equations used in the
[95/28 forced-X proof](../ordinary13-natural-cfold-forced-x95-degree28/)
hold. That proof applies without change: at `X=0` the first residual
excludes `J=0` and then gives `q³|Y`; the main norm forces `H|U`, hence
`H|3q²`, contradicting `H=4Y+3>3q²`. Therefore `X>0`.

## Count and degree

All 94 binary operations, 13 inputs and four ports are live. The affine
edit preserves the parent's degree-50 upper bound. The all-inputs-equal ray
at authenticated P72/P115 ports has degree 50 modulo 1,000,000,007 and
leading coefficient 604845992, proving exact specialized integer degree 50.
The checker pins the graphs and port bytes, verifies the gate edit and
liveness, tests 300 signed modular identities and actual port bounds,
samples divisibility inequalities, and computes the ray. Finite controls
do not replace the unbounded proof or inherited endpoint. Compared with the
proposed 95/28 square graph this uses one fewer gate but has higher degree;
neither dominates the other in those measures.

```
python3 -I -S -B research/ordinary13-natural-cfold-forced-x94-degree50/check.py > /tmp/natural13-cfold-x94.json
cmp /tmp/natural13-cfold-x94.json research/ordinary13-natural-cfold-forced-x94-degree50/result.json
```
