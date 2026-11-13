# Reverse shear: the parent ordinate is nonzero

At a zero of the proposed current2011 72/46 sheared graph, the expression
`V+y_child` is nonzero under elementary ordered-ring bounds. This is one
fact-level step toward the reverse witness map, **not** a checked Lean lemma,
literal model bridge, positive natural-witness construction, or iPRA
endpoint. The new source is unelaborated. The complete reverse direction
still needs the sign/absolute-value model witness and graph-evaluation proof.

## A simple inequality

Work in a linearly ordered commutative ring. Assume `A>=0`, `I>=2`,
`y>=1`, `rest>=0`, and

```
rest + U² + (I²−A)² = 2,
U = A*(V²−(V+y)²)+(V+y)².
```

Then `V+y != 0`. Otherwise `V=−y`, so `U=A*y²`. Since `I²>=4` and
`y²>=1`, if `A>=2` then `U>=2`; if `A<=2` then `I²−A>=2`. In either
case one of the displayed squares is at least 4, contradicting their total
2 with `rest>=0`. This argument needs neither a Pell-index theorem, a sign
exclusion, a nonzero first norm, nor a case split on f.

## Exact graph context

The pinned 72-row child uses the same current2011 fixed ports as the 71/60
parent. Its rows define

```
I=i*c², A=Delta*(f²−1), y_old=V+y_child,
U=y_old² − A*y_child*(y_old+V), H=I²−A,
output=P²+U²+(Q*W−1)²+H²−2.
```

The exact ring identity `U=A*(V²−y_old²)+y_old²` is the existing
`auxiliary_shear` statement in the earlier source-only shear draft.
Strictly positive natural inputs give `y_child>=1`, `i>=1`, `f>=1`, and
`c=(eta+zeta)*Y+eta>=3`; hence `I>=2`. The checked positive-beta/current
port facts give `Delta>0`, and `f>=1` gives `A>=0` in the model difference
ring. The nonnegative `rest` is `P²+(Q*W−1)²`.

For a full model proof, the candidate graph and its exact shear identity
must still be evaluated in the same difference-ring valuation. Having shown
`y_old != 0`, an explicit model-natural absolute-value witness must
represent `|y_old|`; the parent uses y only through its square, but this
must be tied to its actual literal evaluator. The separate forward map,
its `2*R<c` binding, the resulting two-way zero bridge and internal
iPRA/Gödel–Gentzen transfer remain open.

[`ShearNonzero.lean.src`](ShearNonzero.lean.src) proposes the generic
ordered-ring proof with all bounds explicit. Its tactics are **uncompiled**.
The finite checker pins the source and literal child rows and runs bounded
arithmetic diagnostics; neither the source inspection nor finite samples
prove the universal theorem or model bindings.

```
python3 -I -S -B research/current2011-shear-ordinate-nonzero-order-draft/check.py > /tmp/shear-nonzero.json
cmp /tmp/shear-nonzero.json research/current2011-shear-ordinate-nonzero-order-draft/result.json
```

No Lean/build or staging operation is performed.
