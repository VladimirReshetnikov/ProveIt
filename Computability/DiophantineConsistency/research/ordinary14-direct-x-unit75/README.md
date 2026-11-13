# Direct-X five-unit graph: 14 inputs, 75 operations, degree 100

This **proposed all-positive** graph has 14 strictly positive inputs, 75 live
operations and exact degree 100 at the authenticated compact44 ports. It
combines the negative-Pell unit finalizer and shifted guard with the reviewed
[`14/79` direct-root, direct-auxiliary parent](../ordinary14-direct-roots79-56/),
which keeps X as a free positive input and retains the `E*q` main-carrier
term. Its positive-zero comparison requires the source replay below and is
submitted for independent review. It adds no Lean/iPRA theorem, PDF/JSON
binding, fresh provider replay or global minimum; the parent's endpoint
qualifications remain inherited.

## Source delta and unit signs

Put `b=J*beta`, `q=b+1`, `Y=q³*s`, `m=X*Y²`, `k=eta+zeta`,
`ell=m*k`, `qF=q−F`, `C=qF−alpha` and
`Bprime=C*(X+K0)−F`. The parent has five-square output

```
A0² + A1² + (Fa−1)² + g72² + (Bprime−b*h_old)²,
A0=r²−(1+ell*(ell+k)).
```

Replace the finalizer by

```
F0=r²−ell*(ell+k),  F1=1+A1,  Fs=1+g72,
Fg=C*(X+K0)+qF−b*h,
out=F0*F1*Fa*Fs*Fg−1.
```

At signed assignments with `h_old=h−1`, `Fg=1+Bprime−b*h_old` and
F0=1+A0; the other factors are unchanged. The graph deletes the ten
five-square finalizer gates and the first residual's two `+1`/subtraction
gates, then adds the eight displayed unit-product gates: `79−10−2+8=75`.

For positive inputs with `beta>0`, q>=2, `Y=q³*s>=8` and X>=1, so
`m>=64`. The elementary negative-Pell descent in the reviewed
[`14/75` five-unit packet](../ordinary14-negative-pell75/) proves that
`F0=r²−m*(m+1)*k²` is never −1 for m>=2. The usual modulo-four
arguments exclude −1 for F1, Fa and Fs. Therefore a zero of the product
forces those four factors to +1 and then forces Fg=+1, without any sign
restriction on Fg. Conversely the parent's five-square zero makes all five
factors +1 after `h=h_old+1`.

## Reverse map and the h=1 boundary

Assume the fixed integer ports satisfy

```
beta>=46,  K0>=0,  0<MC<beta,  0<MF<2*beta.
```

The authenticated compact44 ports meet these bounds. Take a positive new
zero. Its unit factors give the same first, main, strong and direct-y
auxiliary norms as the parent, and

```
Fg=1  ==>  Bprime=b*(h−1)>=0.
```

If h>1, set `h_old=h−1>0`; the displayed factor equalities immediately give
a positive parent zero. If h=1 then `Bprime=0`. Since
`Bprime=C*(X+K0)−F`, F>0 and X+K0>0, this already forces `C>0` and
`F+alpha<q`. This is the nontrivial boundary: **C>0 alone does not make
Bprime positive when X is free**. For instance q=5, F=3, alpha=1, X=1,
K0=2 gives C=1 and Bprime=0; that scalar control is not a graph zero.

From the new graph's own norms, `Y=q³*s`, positive C and the stated scalar
port bounds, the reviewed fact-level replay in
[`ordinary14-shifted-guard87-calibration`](../ordinary14-shifted-guard87-calibration/)
applies without an old parent zero. Its direct-y coordinate is converted to
the positive auxiliary difference by the reviewed
[`13/87` auxiliary-root proof](../ordinary13-aux-root87-36/). In particular:

* the scalar rank window gives `R+1<q⁴`, `R>=q³>=26`;
* positive first/main Pell roots and the main orientation yield
  `q⁴|(R+1−k)`; `P72Exact.indices_ordinary` applies with `mu=q⁴` and
  `i_prime=i`;
* because this **old-style main carrier retains `E*q`**, its projection
  yields `q|3X`. Since q>=47 and X>0, this implies X>=16. The cited
  `power_bound` and three-multiplier trace replay then give `X=2^R`.

Since `R>=q³`, elementary growth gives `X>=q²`. Positive C and alpha imply
`F<=q−2`, and K0>=0, so

```
Bprime=C*(X+K0)−F >= q²−(q−2) > 0,
```

contradicting the h=1 assumption. Thus h>=2 and the reverse map
`h_old=h−1` is strictly positive. The zero-existence comparison is an
external fact-level replay from the **new** graph; it does not invoke an old
literal-zero wrapper whose first-coordinate assumptions are unavailable.

## Degree and checks

With fixed ports, the reviewed parent bounds give `deg F0<=20`,
`deg F1<=28`, `deg Fa<=28`, `deg Fs<=22`, and `deg Fg<=2`. Hence the
product has degree at most 100. A full all-inputs-equal ray at authenticated
P72/P115 ports modulo 1,000,000,007 has degree 100 with leading coefficient
380600189, proving exact specialized degree 100.

The checker pins both complete graphs and port bindings, verifies the source
delta/topology/liveness, finite modulo-four and negative-Pell controls, 160
signed factor-shift identities, and the displayed partial boundary control.
The controls do not replace the unbounded negative-Pell proof or h=1 source
replay. No Lean run is performed.

```
python3 -I -S -B research/ordinary14-direct-x-unit75/check.py > /tmp/direct-x-unit75.json
cmp /tmp/direct-x-unit75.json research/ordinary14-direct-x-unit75/result.json
```

Independent external review is recorded in
`../../reviews/ordinary14-direct-x-unit75-independent/`.
