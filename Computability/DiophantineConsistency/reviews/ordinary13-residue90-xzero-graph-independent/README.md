# Independent source review: 13/90 graph to X forcing

The proposed graph client uses the correct residual-1 norm and signed main shift at arbitrary gamma. The pinned literal wiring gives `R=(alpha+(q-F)*(J*beta))*(q²-1)+J*(MC+q*MF)`, `shift=U*gamma+X*Y*q+R+1-k`, and `Dstar=U*(X+a*c)+H*shift`. Its main residual is exactly `Dstar²-U²*(1+(H+a²)c²)`. The signed R avoids assuming a rank window or C>0 during this extraction; the `X*Y*q` term is required for this 82-parent graph and is present in the draft.

At X=0, `a=X*Y+Y=Y`, so the fact-level X=0 client's root shape and norm apply to the signed shift, regardless of gamma or root sign. J>0 and represented positive beta supply `q>=2` and `Y>=q³`. The compact-symbolic client combines the earlier proposed J branch and compact beta facts to supply X positivity, then composes the gap/rank/gamma source. Its K remains an arbitrary standard natural: identifying it with the physical compact kernel, exact graph zero maps and the endpoint still require separate work.

The checker pins the independently reviewed arithmetic and J packets, checks every relevant literal graph row, source interfaces and finite specialization controls; the author's receipt also reproduces. The `simp`, `ring`, `linear_combination`, casts, imports, axiom reports and providers have not been checked by Lean. The finite checks do not establish arbitrary-model or iPRA theorems.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-residue90-xzero-graph-independent/check.py | cmp - reviews/ordinary13-residue90-xzero-graph-independent/result.json
python3 -I -S -B research/ordinary13-residue90-xzero-graph-draft/check.py | cmp - research/ordinary13-residue90-xzero-graph-draft/receipt.json
```
