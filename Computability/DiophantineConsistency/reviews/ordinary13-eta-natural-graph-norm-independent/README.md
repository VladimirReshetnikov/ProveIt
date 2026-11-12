# Independent review: eta-natural graph-to-norm draft

The draft uses the exact generated prototype fields and supplies the
positivity hypotheses required by its signed-root quotient interfaces. No
field, root-witness, or eta-zero mismatch was found at the source-statement
level. It remains an unelaborated source proposal: neither graph evaluation
and casts nor imported model theorems have been checked by Lean here.

The independent checker parses every operation row of the generated literal
and compares it with the pinned structural prototype, including the field
selection for the actual first root `Z`, actual main root `Dstar`, b, k,
ell, U, c and Delta. The six proposed model-natural field statements use
`b=J*beta`, `q=1+b`, `X=q*v6`, `Y=q³*(v7+1)`,
`k=v9+v10+1`, `ell=(X*Y²)*k`, `U=Y*q²`,
`c=v9+Y*k`, and `Delta=3+4*(X*Y+Y)+(X*Y+Y)²`. The nontrivial first-norm
identity is `ell*(ell+k)=m*(m+1)*k²` for `m=X*Y²`.
The actual evaluation and rewriting of the integer port casts use the pinned
`P72Root.cast_port` interface and still require Lean elaboration.

`first_natural_norm` applies the bridge's signed first norm to the actual
`(graph (pp p)).z` field, after the proposed b/k/ell field casts, and
requires the explicit positive first scale `b>0`. The cited fact-level
`first_natural_norm` then returns a natural tau with that norm. It does not
silently substitute the original free-J root.

`main_natural_norm` similarly takes the actual `(graph (pp p)).d` field,
uses the proposed U/Delta/c casts, and requires `U>0`. The cited
`signed_norm_quotient` source returns a natural magnitude and quotient of
that signed root, from which the stated natural g satisfies the main norm.
The public graph theorem only returns g's norm; it does **not** assert that
g is the oriented signed quotient or a specified Pell abscissa. That
identification must be made separately before sharing witnesses with an
oriented balance or exact-index theorem.

The combined theorem assumes the prototype zero and a positive beta cast,
then calls the separate prototype J-positive draft for `b>0`. Independently,
q and shifted `v7+1` yield `Y>0` and `U>0`. Its statements do not require X
positive, a positive-C gap, a natural rank representation, or positive eta;
`v9=0` remains allowed. The J theorem's dependence on the unit bridge, the
actual compact-port/byte binding, source/object/axiom provenance, main-root
orientation, zero maps and iPRA translation remain open.

From this directory run

```
python3 -I -S -B check.py > /tmp/eta-graph-norm-independent.json
cmp result.json /tmp/eta-graph-norm-independent.json
```

The checker pins the relevant sources, compares the complete generated row
sequence and field selection, and checks 240 bounded prototype valuations,
including eta-zero cases. This is not an all-model evaluation or Lean proof.
No reviewed source was modified.
