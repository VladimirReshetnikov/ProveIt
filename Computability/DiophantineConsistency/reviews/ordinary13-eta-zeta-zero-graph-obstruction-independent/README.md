# Independent review: eta=zeta=0 graph obstruction

For a natural port tuple and J=0, the actual probe rows give `q=1`, `X=w`, `b=0`, and `Z=F-(1-F-alpha)*(X+K0)`. The shifted inputs satisfy F,alpha≥1 and the natural K0 and w are nonnegative, so Z>0. The separately proposed unit/norm bridge makes the first norm `Z²=0` at a graph zero, yielding the proposed contradiction. This step needs natural K0 but no beta, eta or zeta positivity.

With represented `beta>0`, J>0 yields `q≥2`; the shifted `s≥1` gives `Y=q³*s≥q³`. At eta=zeta=0 the pinned graph has `k=c=0`, `X=q*w`, and exact main root `U*X+H*(U*gamma+R+1)`, where `U=Y*q²` and `H=3+4Y(X+1)`. The proposed signed norm reduces to `z²=U²`, matching every explicit argument of the separately reviewed modulus obstruction. The rank and shift stay signed; no natural-rank representation is assumed.

The statement requires natural ports and strictly positive represented beta. It does not claim the signed-port controls are compact examples. It excludes the double-zero branch only, conditional on the unelaborated unit, natural-port casts, model arithmetic and source interfaces. It says nothing by itself about eta>0,zeta=0, witness replacement, a reduction or an endpoint.

The source-level checker pins the graph and proof inputs, inspects the relevant rows and hypotheses, and reproduces the author's receipt. From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B reviews/ordinary13-eta-zeta-zero-graph-obstruction-independent/check.py | cmp - reviews/ordinary13-eta-zeta-zero-graph-obstruction-independent/receipt.json
```

No Lean elaboration, compiled provider check or axiom audit was performed.
