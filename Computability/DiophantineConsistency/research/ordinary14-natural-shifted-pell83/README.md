# Natural shifted Pell witness: 14 inputs, 83 operations, degree 97

This proposed natural-domain graph combines the separate
[82-operation natural graph](../ordinary14-root74-natural-forced82/) and
[75-operation positive-domain shifted-Pell graph](../ordinary14-shifted-pell75/).
It trades one operation for a lower degree than the 82 graph. Its natural
zero existence agrees with that graph for arbitrary integer ports with
`beta > 0` and `K0 >= 0`; `MC` and `MF` are unrestricted. The source and
this construction have received independent review; see the
[natural-83 review](../../reviews/ordinary14-natural-shifted-pell83-independent/README.md).
This is not a Lean/iPRA theorem, PDF binding, new provider replay, or minimum claim.

## Explicit zero maps

Write `ell = E*kY` and `k = eta+zeta`; the 82 graph has first factor

```
F0_old = r² − ell*(ell+k).
```

Replace its natural coordinate `r` by natural `t` and set

```
F0_new = t² + ell*(2*t−k).
```

For every integer input and port assignment, `F0_new` equals `F0_old`
under `r=ell+t`; the remaining factors do not use `r` or `t`. Under the
stated port assumptions and the other natural inputs, `ell > 0`, so any
new zero maps to an 82 zero with natural `r=ell+t`, keeping all other
coordinates fixed.

Conversely, at an 82 zero, the unit-factor argument in the 82 packet yields
`F0_old=1` and `r>0`. Since `k,ell>0`, it follows that
`r²=ell²+ell*k+1>ell²`, hence `r>ell`. Set `t=r−ell>0` and keep the other
coordinates fixed. The polynomial identity then gives a new zero. The two
maps are inverse on zeros; they are explicit coordinate transformations,
while the unbounded unit-factor argument remains external mathematics.

## Gate count and degree

The exact edit deletes the four gates computing `ell+k`, `r²`, their
product, and their difference, and adds the five gates computing `t²`,
`2*t`, `2*t−k`, `ell*(2*t−k)`, and their sum. The resulting 83 binary
operations, all 14 inputs, and all four fixed ports are live.

The graph is the positive 75-operation shifted-Pell polynomial after
affine substitutions by increments of 0 or 1 in the inputs. Its total
degree is therefore at most the 75 graph's 97; see that packet for its
`F1` cancellation argument. The checker independently authenticates the
P72/P115 ports and calculates the ray with `t=2*x` and all other natural
inputs equal to `x`: its degree is 97 modulo 1,000,000,007, with leading
coefficient 979034495. Therefore the specialized integer polynomial has
exact degree 97. The all-equal ray would hide the top term because the
leading part of `2*t−k` cancels there.

The checker also pins both graphs, verifies their exact DAG delta and
liveness, and checks 200 signed full-graph substitution controls. These
finite controls do not replace the unbounded argument or establish the
inherited source endpoint.

```
python3 -I -S -B research/ordinary14-natural-shifted-pell83/check.py > /tmp/natural-shifted-pell83.json
cmp /tmp/natural-shifted-pell83.json research/ordinary14-natural-shifted-pell83/result.json
```
