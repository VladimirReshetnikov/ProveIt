# Six forced inputs: 13 naturals, 88 operations, degree 60

This external mixed shift of the independently reviewed
[13/81/60 positive residue graph](../ordinary13-residue-first81/) leaves
`J`, `w`, `f`, `y`, `gamma` and the first-root input `r` natural and unshifted;
the other seven coordinates are shifted. Its graph has 13 natural inputs,
88 live binary operations and exact degree 60 at the authenticated compact44
ports. It saves one operation compared with the separate 13/89/56 graph while
raising degree by four. No global minimum or new Lean/iPRA endpoint is claimed.

## Boundary arguments

The graph defines `X=q*w`, `Y=q³*s`, `b=J*beta` and `q=1+b`. Under a
positive represented beta and nonnegative represented K0, the model-level
[J, X, f, y forcing arguments](../ordinary13-natural-residue-forced91-degree56/)
apply to this graph's identical first/main/strong/direct-auxiliary norms.
They require only that `X>=0`, not that it be an independent input. In
particular X=0 is impossible by the main-norm divisibility contradiction;
since q>0, `X=q*w>0` forces w>0. The shifted variables include F, alpha, i,
T, s, eta and zeta, while r and gamma may be zero during these arguments.

The [13/89 root-coordinate argument](../ordinary13-natural-residue-forced89-degree56/)
then forces r>0 provided the represented compact bound `K0+1<=q²` is supplied.
It uses the actual residue carrier `P=C*(X+K0)-F`, its own first norm and
`Y>=q³`; these are unchanged here. The proof's corrected minus-branch bound is
`k*(P-1)+t < 2*ell < ell+tau`, not the false stronger inequality
`k*(P-1)+t<=k*P`. The checker authenticates the compact P72/P115 bytes and
verifies `K0+1<=(beta+1)²`; a Lean proof that the represented model ports
satisfy the corresponding inequality is still required.

For gamma, the [13/90 standard-integer argument](../ordinary13-natural-residue-forced90-degree56/)
applies after X>0, with one graph-specific change: this 81-row parent's
modified main shift is `U*gamma-(k-R-1)`, **without** the `X*Y*q` term.
At gamma=0 its signed main expression is

```
Dstar = U*(X+a*c) + H*(R+1-k).
```

The same carrier-specific first norm rules out `C<=0` using only r>=0; its
Pell equation and the main norm give the cited standard-integer bound
`k>=8XY²+4`. The compact rank window gives `R+1<q⁴`; together with
`Y>=q³` this yields `R+1<k`, and the same positive-main-root comparison
contradicts gamma=0. Unlike the 82-parent case, there is no extra `X*Y*q`
to absorb. This gamma proof is **standard-integer only**, as is the parent
calibration; the source-only IΣ₁ facts and graph-specific client remain
unelaborated.

These arguments give standard zero-existence equivalence between the mixed
natural graph and its positive parent under the authenticated compact bounds.
The mixed graph's polynomial is exactly the positive-parent polynomial at the
displayed mixed substitution; it is not generally identical to the fully
shifted polynomial at the same natural tuple. The separate
[13/89 s=0 full-zero probe](../ordinary13-residue89-unshift-s-full-zero/)
shows why unshifting s is unsafe for that other graph; it is not itself a
full-zero proof for this graph.

## Evidence and scope

The checker verifies the parent hash, all 88 graph rows, liveness, first and
main norm wiring including the absent `X*Y*q` term, authenticated P72/P115
port bytes, the extra compact kernel bound, and the exact cancellation used
in the degree bound. The residual degree bounds are 24, 30, 30 and 22; the
complete graph's compact-port all-inputs-equal ray has degree 60 with nonzero
coefficient 619528110 modulo 1,000,000,007. The result is exact for that tuple.
The check also retains finite controls for the corrected root inequality;
those controls do not prove its general model form.

The positive parent's [independent standard-integer review](../../reviews/ordinary13-residue-first81-math-independent/)
uses fact-level compact calibration, not an elaborated modified-graph model
client. Neither this candidate nor its earlier chain has a new checked Lean
model transfer, provider replay, iPRA endpoint or current-2011 PDF binding.
The exact [13/87/60 zeta/rank-offset fold](../ordinary13-natural-residue-eta-fold87-degree60/)
saves one operation from this graph. The separate [13/88/56 natural graph](../ordinary13-natural-residue-eta-fold88-degree56/)
has the same number of variables and operations at lower degree, although its
source proof path differs. The 13/86/99 natural candidate trades fewer
operations for higher degree; 13/94/50 and 13/95/28 trade more operations for
lower degree. These selected comparisons do not establish a global frontier.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-natural-residue-forced88-degree60/build.py
python3 -I -S -B research/ordinary13-natural-residue-forced88-degree60/check.py
```

The deterministic source/byte/ray output is [receipt.json](receipt.json). No
Lean process is run.
