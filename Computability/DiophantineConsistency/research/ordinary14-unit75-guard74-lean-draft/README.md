# Literal 75/74 product-graph sources — unelaborated draft

`P75NegativePell.lean` and `P74PositiveGuard.lean` are literal source-only
`Expr (Fin 14)` renderings of the independently reviewed
[75-operation negative-Pell product](../ordinary14-negative-pell75/) and
[all-positive 74-operation shifted-guard product](../ordinary14-positive-guard74/).
The generator pins the exact candidate JSON bytes, preserves all 75/74 rows
in their original order, checks each operand is previously available, and
maps witnesses `J,F,alpha,f,i,T,w,s,r,eta,zeta,y,gamma,h` to slots 0–13 and
fixed ports `beta,K0,MC,MF` to slots 0–3. It does not add computation gates.

`first`, `main`, `aux`, and `strong` expose the four **product factors**
`F0`, `F1`, `Fa`, and `Fs`; they are not the 78-parent residuals.
`guardFactor` is `Fg` for 75 and `guard` for 74. `output_shape` proposes the
literal five-factor product minus one. The remaining Graph fields expose
existing intermediate rows for prospective model clients; these projections
are not operation-count additions. F and alpha remain valuation slots.

The independently reviewed standard-integer statements assert the 75 graph
has the same positive zeros as 78 when beta>0, and the 74 and 75 graphs have
the same positive-zero existence when beta>0 and K0≥0. These source files do
not establish either comparison in an arbitrary IΣ₁ model. The forthcoming
model proof must bind the literal factors to signed pairs and the reviewed
[internal five-unit fact](../ordinary14-five-unit-model-facts-draft/), derive
`m≥2` and the three residue exclusions from the same graph zero, prove the
exact guard-coordinate change, derive its positivity using the separately
reviewed [guard fact](../ordinary14-positive-guard74-model-fact-draft/), and
connect the actual model and port casts. It must also bridge the 78 parent,
authenticate coherent transitive providers and Init, and separately check the
iPRA endpoint. No module here proves graph equivalence, graph operation count,
degree, elaboration, provider compatibility, byte/PDF binding or an endpoint.
The 74 graph here is **all-positive**; it is not the distinct mixed-F-domain
74 graph.

From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B research/ordinary14-unit75-guard74-lean-draft/make_graph.py --check | cmp - research/ordinary14-unit75-guard74-lean-draft/observation.json
```

No Lean run was performed. The printed axiom commands are source text only.

Independent source review: [75/74 literal graphs](../../reviews/ordinary14-unit75-guard74-lean-independent/README.md).
