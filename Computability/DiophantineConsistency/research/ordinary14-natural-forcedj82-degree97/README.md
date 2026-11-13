# Forced J and shifted Pell root: 14 natural inputs, 82 operations, degree 97

This proposed graph deletes the `J=n_J+1` gate from the proposed
[14/83/97 natural shifted-Pell graph](../ordinary14-natural-shifted-pell83/).
It has 14 nonnegative inputs, 82 live binary operations and exact degree 97
at the authenticated compact44 ports. Its natural-zero existence agrees
with that parent when `beta > 0` and `K0 > 0`, with arbitrary integer `MC`
and `MF`. The positive `K0` hypothesis is stronger than the 83 parent's
`K0 >= 0`; the authenticated actual `K0` is strictly positive. Both packets
have independent reviews; see the [forced-J review](../../reviews/ordinary14-natural-forcedj82-degree97-independent/README.md).
This is external mathematics, not a Lean/iPRA
theorem, PDF or physical-byte binding theorem, fresh provider replay, or
minimum claim.

## Zero maps

Delete `J=n_J+1` and replace `J` at every consumer with `n_J`. For any
signed integer inputs and ports, the 82 output at `n_J=J` equals the 83
output at `n_J=J−1`, with the other inputs unchanged. Any natural 83 zero
therefore maps to an 82 zero by incrementing its `n_J` coordinate.

Conversely, an 82 zero has a product of five integer factors equal to one,
so each factor is ±1. If `J=0`, then `b=0`, `q=1`, `X=w>=1`,
`qF=−n_F<=0`, and `C=qF−alpha<=−1`. Since `K0>=1`, its unchanged guard
factor satisfies

```
guard=C*(X+K0)+qF−b*n_h <= −2,
```

contradicting the unit property. Thus `J>=1`, and subtracting one from it
gives a natural 83 zero. These maps are mutually inverse on zeros. The
argument is unchanged by the shifted first Pell root because it uses only
the guard and the final product.

## Non-dominated local tradeoff and degree

All 82 binary gates, 14 inputs and four fixed ports are live. The affine
substitution preserves the parent's degree-97 upper bound. At the
authenticated ports, the ray with `n_t=2*x` and the other inputs equal to
`x` has degree 97 modulo 1,000,000,007, with leading coefficient
979034495, proving exact specialized integer degree 97. The all-equal ray
hides the top term because the leading part of `2*t−k` cancels there.

Compared with the separately proposed [14/81/107 natural graph](../ordinary14-natural-forcedj81/),
this graph uses one additional operation and has ten lower degree. Neither
dominates the other by operation count and degree; no global Pareto or
optimality claim is made. The checker pins both graphs and port bytes,
verifies the gate edit and liveness, checks 300 signed modular affine
identities and computes the degree ray. Finite tests do not replace the
unbounded guard argument or establish the inherited endpoint.

```
python3 -I -S -B research/ordinary14-natural-forcedj82-degree97/check.py > /tmp/natural14-forcedj82-degree97.json
cmp /tmp/natural14-forcedj82-degree97.json research/ordinary14-natural-forcedj82-degree97/result.json
```
