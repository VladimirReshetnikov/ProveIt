# A nonnegative boundary zero at fixed compact ports

The [separate all-moduli packet](../p64-qcube72-fixed-mask-all-moduli-controls/README.md) records the positive modular construction. This packet adds the exact nonnegative boundary zero and preserves its own independent controls.

For **every positive integer N**, there are positive assignments at the
actual fixed compact44 beta and masks, for each of two specific natural K
ports, for which the 72-graph output is positive but divisible by `N⁴`. One
family has `3|q`; the other has `3∤q`. The assignments vary with N. Thus,
at these two K values, any finite collection of tests requiring the output
to vanish modulo specified integers can be met in either q class by choosing
N to be their product.

This does **not** produce a strictly positive integer zero or an actual
positive 72 zero with either q class. It does not rule out stronger modular or 3-adic arguments involving
additional hypotheses, unbounded precision, or a proof using the full integer
norm equations. In particular,
it does not disprove existential reverse implication.

## Fixed ports and positive assignments

Use exactly the fixed compact beta and mask ports

```
beta = 2^590069−1,
MC = CompactSymbolicPorts.lowNat,
MF = beta + CompactSymbolicPorts.highNat.
```

Choose `J=2` for the `3|q` family or `J=1` for the `3∤q` family, and put

```
q=beta*J+1, K=q−1,
F=z=w=t=f=i=T=y=1, alpha=q−2,
s=eta=h=N, zeta=1.
```

`K` is fixed within each family and does not depend on N: it is `2*beta`
for `J=2` and `beta` for `J=1`. Since `beta≡1 (mod 3)`, the first
family has `q≡0 (mod 3)` and the second has `q≡2 (mod 3)`. All graph
coordinates and K are positive; `q≥3` and `alpha>0` follow from the fixed
beta.

## An exact nonnegative boundary zero

The construction is a perturbation of an exact zero over nonnegative
integers: keep the same fixed ports, `J`, `q`, `K`, `F=z=w=t=f=i=T=y=1`,
`alpha=q−2`, and `zeta=1`, but set `s=eta=h=0`. Then `Y=U=P=c=0`,
`a=0`, `H=Delta=3`, `k=1`, `A0=Na=1`, and `M=W=Lt=0`. The graph
output is exactly zero, independent of the rank and mask values. This is
not an admissible positive zero: `s`, `eta`, and `h` are zero.

For a fixed prime p, choosing `N=p^r` in the positive assignments gives a
compatible p-adic sequence converging to this boundary vector. The limiting
p-adic zero likewise does not provide the strictly positive integer witnesses
required by the Diophantine equation; no general conclusion about other
p-adic arguments follows.

## Exact residual calculation

Write `Y=q³s`, `X=wq`, `U=Y²`, `k=eta+zeta=N+1`,
`P=XY²`, `ell=P*k`, `c=kY+eta`, and `a=XY+Y`. The graph residuals
satisfy:

- `N|Y`, hence `N²|U` and `N²|P`; also `N|c`.
- `A0=1−ell(ell+k)`, so `N²|(A0−1)`.
- The main expression `Dstar=U(X+ac)+Hh` is divisible by N, while
  `N⁴|U²`; therefore the main residual `M=Dstar²−U²(1+Delta*c²)`
  is divisible by `N²`.
- Since `f=i=1`, the strong residual is `W=c⁴`, hence `N⁴|W`.
- Since `f=y=1`, the auxiliary residual is **exactly** `Na=1`.
- `C=q−F−alpha=1` and `(K+w)C=q=F+z(q−1)`, so the transport
  residual `Lt` is exactly zero.

Consequently every term of

```
output=(A0*Na−1)²+M²+W²+Lt²
```

is divisible by `N⁴`. At the same time `P>0` and `k=N+1>0`, so
`A0−1=−ell(ell+k)≠0`; with `Na=1` the output is strictly positive.
These are therefore explicit nonzero outputs, not integer zeros.

[`check.py`](check.py) independently evaluates the pinned full 72-row graph
modulo `N⁴` for `2≤N≤64` and both fixed-port families. It computes the
actual beta, low-mask and high-mask residues from their pinned digit sources
without expanding the enormous constants. Its 126 evaluations and 40 exact small-beta boundary-zero evaluations are
finite controls for the symbolic proof above, not the proof of the universal
claim.
Run `python3 -I -S -B check.py`; retained output and source pins are in
[result.json](result.json). No Lean theorem is claimed.
