# Forced J: 13 natural inputs, 88 operations, degree 99

This proposed graph deletes one gate from the proposed
[13/89/99 natural graph](../ordinary13-natural-unit-product89/). It has 13
nonnegative inputs, 88 live binary operations, and exact degree 99 at the
authenticated compact44 ports. It has the same natural-zero existence as
that parent for arbitrary integer ports with `beta > 0` and `K0 >= 0`;
the other two ports are unrestricted for this local map. Both packets have
received independent review; see the [88-graph review](../../reviews/ordinary13-natural-unit-product88-independent/README.md).
Endpoint, calibration, and provider qualifications of
the earlier positive graph are inherited. No Lean/iPRA theorem, PDF or
physical-byte binding, fresh provider replay, or minimum claim is made.

## Coordinate maps and forced positivity

The 89 graph begins by setting `J=n_J+1`. Delete that gate and use `n_J`
directly at every consumer. As an identity over arbitrary signed integers,
the 88 output at `n_J=J` is the 89 output at `n_J=J−1`, with all other
coordinates unchanged. Thus a natural 89 zero maps to a natural 88 zero by
incrementing its `n_J` coordinate.

Conversely, let the 88 graph vanish. The parent unit-product factorization
and modulo-four exclusions apply to all integer inputs, so its first
factor is +1. Write

```
b=J*beta, q=b+1, X=q*w, C=q−F−alpha,
B=C*(X+K0)−F,
Z=b*(ell+k+r−k*B)−B.
```

If `J=0`, then `b=0`, `q=1`, and `X=w>=1`. The retained input shifts give
`F>=1` and `alpha>=1`, so `C=1−F−alpha<0`. The hypothesis `K0>=0` yields
`B=C*(X+K0)−F<0`, hence `Z=−B>0`. But the first factor being +1 gives

```
Z² = b²*(1+ell*(ell+k)) = 0,
```

a contradiction. Therefore `J>=1`. Subtract one from this coordinate and
leave all others unchanged to obtain a natural 89 zero by the exact
polynomial identity. Composing with the 89 packet's explicit positive-zero
maps supplies the inherited positive-parent equivalence; that packet's
`r=0` root switch is still needed.

## Count and degree

The one input-gate deletion leaves 88 live binary operations, 13 inputs,
and four fixed ports. The affine substitution preserves the 89 parent's
degree-99 upper bound. At the authenticated P72/P115 ports the all-equal
input ray modulo 1,000,000,007 has degree 99 and leading coefficient
663418019, proving exact specialized integer degree 99. The checker pins
the complete graphs and port bytes, verifies the exact gate edit and
liveness, tests 300 signed modular identities, and computes the ray. Those
finite tests do not prove the unbounded positivity or inherited endpoint.

```
python3 -I -S -B research/ordinary13-natural-unit-product88/check.py > /tmp/natural13-product88.json
cmp /tmp/natural13-product88.json research/ordinary13-natural-unit-product88/result.json
```
