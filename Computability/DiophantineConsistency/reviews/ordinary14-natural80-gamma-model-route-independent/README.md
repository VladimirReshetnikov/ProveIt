# Independent review: natural-80 gamma model-proof route

The [source audit and proposed route](../../research/ordinary14-natural80-gamma-model-route/README.md) accurately identifies a plausible path through the inspected signatures, with the stated caveat that several 74/81 clients are unelaborated drafts. Both source receipts reproduce. This is not a Lean model theorem, an axiom audit, or an iPRA derivation.

The checker independently compares the complete external 80 and positive-74 graphs under the proposed partial shift. The 74 coordinates `J,f,r,y,gamma` correspond to the 80 coordinates directly; `F,alpha,i,T,w,s,eta,zeta,h` are incremented. The exact `qF`, `k`, `r0`, and guard cuts are verified as sparse ring-polynomial identities, and all other graph rows agree after renaming. This supports the mathematical changed-valuation identity, but a Lean ring-evaluation and model-embedding theorem remains to be written and checked.

`OwnZeroProduct74Draft.factor_units_of_zero` explicitly requires represented positive beta, positivity at slots `J,w,s`, an own zero and three residue premises; it does not require all slots positive. The corresponding residue source proposes those premises. The guard-cut source has explicit beta and K0 representations, but its `strict_of_zero` client requires `∀ j, 0<v j`; it cannot be applied directly with gamma zero. A new fact-level use of the guard unit and cut to derive `F+alpha<q` is therefore necessary. The rank-window source separately requires represented positive beta and J, positive F and alpha, `MC<beta`, `MF<2*beta`, `q=beta*J+1`, and that gap. The route correctly leaves the model representations and bounds to be supplied.

`DirectMainNorm.direct_main_orientation` takes `U,X,Y,k,eta,G,R`, `U>0`, `Y>=8`, `k>0`, and the explicit signed-magnitude main-norm equality. Neither it nor its `direct_parts_positive` helper has a separate `G>0` premise, so `G=0` is compatible with their displayed hypotheses. The graph's main unit must still be converted to that exact magnitude equality. The conclusion is a positive quotient and a natural additive balance; using that balance avoids treating natural subtraction as ring subtraction.

For the `k=2` exclusion, `ArithmeticPellClassification.solution_index` proposes an ordinate `c=ycoord p a` after the norm is bound with `delta a=(a+1)(a+3)`. `Direct80IndexOne.impossible` accepts parameters `Y,S,X,eta,zeta,p`; taking its `S=a+1` and its **own** `X=0` gives recurrence base `(a+1)*(0+1)−1=a`, with the required `Y<=a+1` following from `a=X_graph*Y+Y`. It additionally requires `1<=Y`, `eta,zeta>0`, `eta+zeta=2`, and the graph-to-ordinate equality. Those obligations and the natural subtraction rewrite are not formalized by this review. The first-norm classification source and recurrence pattern support a fact-level derivation of `8*m+4<=k` once first indices zero and one are excluded, but the inspected `TraceNormKpos` graph clients themselves require all their slots positive and cannot simply be applied to the target gamma-zero valuation.

The remaining predecessor proof, source rewrites, model instances, symbolic-port bounds, transitive providers, axiom closure and endpoint conversion all require Lean checking. The `IΣ₁` model interface alone does not establish the requested iPRA proof-existence result; physical coefficient and PDF bindings remain separate.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural80-gamma-model-route-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural80-gamma-model-route-independent/result.json
```
