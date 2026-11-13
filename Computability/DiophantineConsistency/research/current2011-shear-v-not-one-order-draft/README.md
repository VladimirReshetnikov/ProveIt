# Forward shear: avoiding the strong-root residue

This source-only draft simplifies one component of the existing 72/46
positive-coordinate shear plan. It does **not** prove that candidate
equivalent to the checked current2011 71/60 equation, and no Lean declaration
in this packet has been elaborated. The exact 71/60 parent and 72/46 child
graphs, `Carrier65` core, and model-index source are pinned by the read-only
checker. Their port and provider qualifications remain unchanged.

## Fact-level ordered-ring argument

Let `c,f,T,rank` lie in a linearly ordered commutative ring and assume

```
1 <= c,  2 <= f,  1 <= T,  2*rank < c,
V = f²*(c*T−rank)−c.
```

Then `V != 1`. Indeed `c*T>=c`, hence `c*T−rank>c/2>0` in the
inequality sense `2*(c*T−rank)>c`. Also `f²>=4`; therefore
`f²*(c*T−rank)>2*c>=c+1`, contradicting `V=1`. This multiplication
argument uses only order and the stated inequalities; it does not use
division, a Pell index, or `f²=1 (mod c)`.

Suppose further that `1<=A`, `1<=y_parent`, and the unit auxiliary norm is

```
A*(V²−y_parent²)+y_parent² = 1.
```

Then `y_parent>V`. Otherwise `V>=y_parent>=1`, and both
`A*(V²−y_parent²)` and `y_parent²−1` are nonnegative. Their sum is zero,
so `y_parent=1` and `V=1`, contradicting the previous conclusion. Thus the
forward positive child coordinate `y_child=y_parent−V` exists in the
intended natural model once these facts have been transferred there.

## Parent binding and remaining obligations

The literal 71/60 graph computes `V=f²*(c*T−R)−c`, where R is the signed
rank at the same valuation. On a parent zero, its checked generic norm
extraction supplies the auxiliary unit equation and `H=I²−A=0`, with
`I=i*c²` and `A=Delta*(f²−1)`. Positive i and c imply `I>0`, hence A>0;
discreteness gives `A>=1`. Positive natural f has `f>=1`, and `f=1` would
make A=0, so f>=2. The positive inputs give `T>=1` and
`c=(eta+zeta)*Y+eta>=3`.

The [index source](../../Lean/DiophantineConsistency/ArithmeticCarrier94Indices.lean)
`ordinary_first_indices` concludes `2*R<c` for its *natural* named rank and
the full displayed hypotheses there: positive inputs, beta/MC/MF bounds,
transport, first/main/ordinary strong, and auxiliary norms. The source
uses natural truncated subtraction in its definitions. A client still must
extract these hypotheses from the **same actual parent zero**, identify the
natural rank and carriers with the signed difference-ring fields, and
transport `2*R<c` through the cast. This note does not assume those bindings.

The earlier [shear draft](../current2011-sheared72-46-proof-draft/README.md)
instead proposed extracting a proof-local `f² mod c` lemma to rule out
`V=1`. The present elementary argument replaces only that step; it does not
remove the rank-window/index extraction. The child-to-parent direction
still needs the nonzero and absolute-value argument for `V+y_child`, with
the corresponding model-natural witness and literal graph evaluation.
Both zero maps, new literal syntax binding, full iPRA bridge and endpoint
remain open.

[`ShearOrder.lean.src`](ShearOrder.lean.src) records proposed generic ordered
ring proofs and a same-coordinate `Carrier65.core.V` fact with the above
assumptions explicit. Its tactics and theorem applications have **not**
been checked. The read-only checker validates pinned source statements,
literal graph rows, bounded arithmetic controls and the source-only draft;
the controls are diagnostics, not the unbounded proof or model extraction.

```
python3 -I -S -B research/current2011-shear-v-not-one-order-draft/check.py > /tmp/shear-order.json
cmp /tmp/shear-order.json research/current2011-shear-v-not-one-order-draft/result.json
```

No Lean/build or staging operation is performed by this packet.
