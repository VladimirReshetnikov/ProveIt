# Eta-natural prototype: conditional model proof that J>0

This is an **unelaborated source draft**, not a checked model theorem or an
iPRA endpoint. It applies only to the exact generated eta-natural prototype
and imports the separately unelaborated prototype factor-unit/signed-norm
bridge. The source assumes the graph's ports are the integer images of a
natural tuple `p : Fin 4 → ℕ`; in particular this supplies model-natural
`K0=p 1≥0`. It does not require a fixed beta value, beta positivity, or
positive eta, X, zeta, f, y or gamma.

If `J=v 0=0`, then the actual prototype's `b=J*beta=0`, `q=1`, and
`X=q*v 6=v 6`. With `F=v 1+1≥1` and `alpha=v 2+1≥1`, its signed graph
carrier satisfies

```
C = 1−F−alpha ≤ 0
Bt = C*(X+K0)−F < 0
Z = −Bt > 0.
```

The graph's first squared factor, extracted conditionally by the imported
unit bridge, gives `Z²=b²*(1+ell*(ell+k))=0`, contradicting `Z>0` in the
model difference ring. Thus the proposed graph-level source concludes
`0<J`, including eta=0 and X=0, with no unrelated graph wrapper.

The K0 sign matters for this particular first-factor contradiction. As a
small scalar control, `J=0, F=alpha=1, X=0, K0=−1` gives `Bt=0` and
`Z=0`, so the first factor alone does not exclude J=0 if negative K0 is
allowed. This is **not** claimed to be a full graph zero or a counterexample
to some other proof.

The port-to-model casts, exact factor-unit bridge and its modulo-four proof,
all source/provider compatibility, `#print axioms` results, eta-zero
contradiction, zero maps and internal iPRA endpoint remain open. The checker
pins the generated graph and bridge, checks the exact dependency rows, and
runs finite scalar controls. It does not run Lean. Reproduce from
`Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-eta-natural-J-positive-model-draft/check.py | cmp - research/ordinary13-eta-natural-J-positive-model-draft/receipt.json
```
