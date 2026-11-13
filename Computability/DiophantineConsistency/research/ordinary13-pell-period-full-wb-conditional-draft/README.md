# Conditional six-witness `WB` client for the Pell period formula

The six top-level existential witnesses in the proposed period formula admit concrete candidate replacement bounds. This new inert client organizes them into six applications of `PRAWitnessPR.wb_exs_bt'`, starting from the proposed coordinate-graph `WB` clients. **Every hierarchy proof and every replacement implication remains an explicit hypothesis**, and the source has not been elaborated or compiled. It does not prove a uniform primitive-recursive bound for the complete formula or an iPRA theorem.

Let `c=ycoord m a`, `h=2mc`, and x/y be the Pell coordinates at h. Define `F(j,a)=2^(2*(a+2)*j)`. The intended witness-replacement bounds and environments **before** adding each witness are:

| Witness | Environment before binding | Candidate bound |
| --- | --- | --- |
| c | `[m,a]` | `F(m,a)` |
| h | `[c,m,a]` | `2*m*c` |
| x | `[h,c,m,a]` | `F(h,a)` |
| y | `[x,h,c,m,a]` | `F(h,a)` |
| r | `[y,x,h,c,m,a]` | `x` |
| t | `[r,y,x,h,c,m,a]` | `y` |

The two final bounds are both `#1` in their **different** contexts. Coordinate graph equations plus the existing model-level Pell growth estimate suggest reusing the same c, h, x and y. If c>0, the final equations `x=1+c²r` and `y=t*c²` give `r≤x` and `t≤y`.

The c=0 case requires actual replacement. Then the equations only give x=1 and y=0, while r and t may be arbitrarily large; bounding the *original* r or t by x/y is false. Replacing either one by zero preserves all other displayed conjuncts. The source's `Replacement` hypotheses explicitly allow a new witness with the same remaining body, so this case can be handled without assuming positivity. The checker includes a direct c=0 counterexample to any same-witness bound.

The literal inner body has intended context `[t,r,y,x,h,c,m,a]`. The draft builds five nested existential bodies, assumes their six `Σ₁` hierarchy facts and six exact all-`IΣ₁` replacement implications, then proposes to assemble `WB M periodDef.val` in each candidate-PRA model. The inner body `WB` proof uses the separate proposed `xDef_wb`/`yDef_wb` facts. Quotation-generated definitional matching to `periodDef.val`, the hierarchy instances, `BoundTerm.vval` normalization, actual model coordinate/equality extraction, positivity case split, `wb_auto`, imported source resolution and all tactics are untested. The bound terms and source shapes are pinned, but this does not discharge those claims.

Even a successful proof of this `WB` statement would give an existential monotone **model function** bounding all witnesses; it would not itself exhibit a single uniform primitive-recursive bound/code across models. Nor would it establish the period formula's explicit evaluation bridge, the required classical-PRA and intuitionistic witness transfer, the unproved parent-lift hypotheses, or an iPRA consistency equivalence.

The checker verifies the source interfaces and expected variable positions, checks nine small positive-c examples, and checks the c=0 same-witness obstruction. These are finite controls, not quantified model proofs or Lean AST validation. The imports name prospective source providers; no overlay or compiled objects are produced. From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary13-pell-period-full-wb-conditional-draft/check.py | cmp - research/ordinary13-pell-period-full-wb-conditional-draft/receipt.json
```

No Lean, build, staging, provider authentication or axiom report was performed.
