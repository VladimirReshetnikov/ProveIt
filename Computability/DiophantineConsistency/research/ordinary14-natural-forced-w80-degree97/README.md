# Forced w and shifted Pell root: 14 natural inputs, 80 operations, degree 97

This proposed graph deletes `w=n_w+1` from the proposed
[14/81/97 forced-gamma shifted-Pell graph](../ordinary14-natural-forced-gamma81-degree97/)
and uses the input directly. It has 14 nonnegative inputs, 80 live binary
operations and exact degree 97 at the authenticated compact44 ports. The
local zero maps require only integer `beta>0` and `K0>=0`, with arbitrary
integer MC and MF; the parent's stronger fixed-port/rank assumptions and
endpoint qualifications remain inherited. An [independent review](../../reviews/ordinary14-natural-forced-w80-degree97-independent/README.md)
checks the argument and degree certificate.
This is external mathematics, not a Lean/iPRA theorem, PDF or byte binding,
fresh provider replay, or minimum claim.

## Zero maps and forced w

The candidate at `w=g` equals the parent at `n_w=g−1` for arbitrary signed
integer inputs and ports. Incrementing the parent's natural `n_w` maps any
parent zero to a candidate zero. Conversely, at a candidate zero with
`w=0`, we have `X=m=ell=0`, and its shifted first factor becomes
`F0=t²+ell*(2*t−k)=t²`. This nonnegative unit is +1; the other three
restricted factors exclude −1 modulo 4, so the guard is also +1.

If J were zero, the unchanged guard would be at most zero because
`qF=−n_F<=0`, `C=qF−alpha<=−1`, and `K0>=0`, contradicting that unit.
Thus `J>0` and `q>=2`. The main factor and all other quantities entering the
[79/107 forced-w divisibility proof](../ordinary14-natural-forced-w79/)
are identical here. With `Y=q³*s>0`, `a=Y`, `H=4Y+3`, `U=Yq²`, that proof
uses the main norm to obtain `H | U`, then `H | 3q²`, contradicting
`H>=4q³+3>3q²`. Hence `w>0`; subtracting one from it gives a parent zero.
The two maps are inverse on zeros and require no sign assumption on the
main root or gamma.

## Count and degree

All 80 binary gates, 14 inputs and four ports are live. The affine edit
preserves the parent's degree-97 upper bound. At the authenticated P72/P115
ports the ray with `n_t=2*x` and all other inputs equal to `x` has degree
97 modulo 1,000,000,007 with leading coefficient 979034495, proving exact
specialized integer degree 97. The checker pins the graphs and port bytes,
verifies the gate edit/liveness, tests signed modular identities and finite
divisibility controls, and computes the ray. These tests do not replace the
unbounded proof or inherited endpoint. Compared with the proposed 79/107
graph, this uses one additional gate and has degree ten lower; neither
dominates the other in those measures.

```
python3 -I -S -B research/ordinary14-natural-forced-w80-degree97/check.py > /tmp/natural14-w80-97.json
cmp /tmp/natural14-w80-97.json research/ordinary14-natural-forced-w80-degree97/result.json
```
