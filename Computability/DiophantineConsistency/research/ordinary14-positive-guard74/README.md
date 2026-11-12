# Positive shifted guard: 14 inputs, 74 operations, degree 107

This **proposed all-positive** graph has 14 strictly positive inputs, 74 live
operations and exact degree 107 at the authenticated compact44 ports. Its
positive-zero existence agrees with the reviewed
[`14/75` five-unit parent](../ordinary14-negative-pell75/) for arbitrary
integer ports satisfying `beta>0` and `K0>=0`. The explicit quotient maps
below and finite graph/degree checks require independent review. This is not
a new Lean/iPRA theorem, PDF/JSON binding, fresh provider replay or global
minimum claim; the parent's compact44 endpoint and source qualifications are
inherited.

This is a different graph from the separate
[`14/74` mixed-domain F shift](../ordinary14-mixed-guard74/): **all fourteen
inputs here are strictly positive**.

## Shift the guard quotient

Write `b=J*beta`, `q=b+1`, `X=q*w`, `qF=q−F`,
`C=q−F−alpha=qF−alpha`, and `Bprime=C*(X+K0)−F`. The 75-parent's
guard factor is

```
Fg_old = 1 + C*(X+K0)−F−b*h_old.
```

Let the new positive input h represent `h_old+1`. Since `qF=b+1−F`,
compute the factor directly as

```
Fg_new = C*(X+K0)+qF−b*h = 1+Bprime−b*(h−1).
```

With `h_old=h−1`, `Fg_new=Fg_old` identically, and all four other unit
factors are unchanged. This signed integer identity holds for arbitrary
ports; the positive-domain maps require the stated port bounds. The new
graph retargets one guard-base addition and one product consumer and deletes
the old `Fg=1+guard_old` gate, reducing 75 gates to 74.

## Why the shifted quotient is strictly greater than one

For any positive inputs and `beta>0`, `K0>=0`, b is positive, q>=2 and
`X=q*w>=q`. The expression Bprime is **never zero**:

* If `C<=0`, then `Bprime=C*(X+K0)−F<0`.
* If `C>0`, positivity of alpha gives `F<=q−2`, so
  `Bprime>=X−F>=q−(q−2)=2`.

From a positive 75-parent zero, set `h=h_old+1>=2`; the exact identity
gives a positive new zero.

Conversely, let the new product output vanish. The four factors F0, F1, Fa
and Fs are independent of h. As established in the reviewed 75-parent
packet, positive beta and inputs imply that F0 cannot be −1 by the elementary
negative-Pell descent, while F1, Fa and Fs cannot be −1 modulo 4. All five
integer factors multiply to one, so those four equal +1 and the fifth factor
`Fg_new` also equals +1. Its displayed equation gives

```
Bprime=b*(h−1)>=0.
```

Since Bprime cannot be zero, `h−1>0`. Thus `h_old=h−1` is a strictly
positive integer; the exact identity supplies a positive 75-parent zero.
No machine calibration, Mersenne property, or assumption about MC and MF is
used in this local map. The elementary beta/K0 bounds are explicit; no claim
is made for negative K0.

## Count and exact degree

The checker pins both complete graphs and both port bindings, verifies the
single-gate deletion, exact source delta, topology/liveness of all 74 gates,
14 inputs and four fixed leaves, and tests 160 signed quotient-shift
identities. It also checks finite instances of the displayed Bprime sign
argument. These controls do not replace the unbounded argument above.

The quotient change is an affine coordinate shift and does not increase the
parent's degree bound of 107. The whole all-inputs-equal ray at the
authenticated P72/P115 ports modulo 1,000,000,007 has degree 107 and leading
coefficient 419359493, proving exact specialized integer degree 107.

```
python3 -I -S -B research/ordinary14-positive-guard74/check.py > /tmp/positive-guard74.json
cmp /tmp/positive-guard74.json research/ordinary14-positive-guard74/result.json
```

Independent external review is recorded in
`../../reviews/ordinary14-positive-guard74-independent/`.
