# Proposed full-period c witness bound

This source-only client keeps the original c and the existing h, x, y, r, t witnesses. The body interpretation says that `yDef` holds of `[c,m,a]`; its represented-function interface proposes `c = ycoord m a`. The existing IΣ₁-model coordinate bound and the separately drafted variable-base-to-binary estimate then give

```
c ≤ power (2*(a+2)) m ≤ Exp.exp (2*(a+2)*m).
```

This is the specified `boundC` at the two-place environment `[m,a]`. It also covers m=0, without a positivity assumption on c or a. The five existential witnesses and full original body are preserved; there is no replacement of the final body's formula. The `cReplacement` theorem explicitly assumes `BodyEvaluationBridge`. The proposed `cReplacement_closed` uses a separately drafted evaluation bridge, which is itself unelaborated.

All local `.lean.src` imports are prospective logical providers: no source was materialized or Lean checked. In particular, the `y_defined.defined` graph equivalence, existential reduction, quotation and `BoundTerm.vval` simplification, tactics, instances, axioms, and coherent source/object provider selection remain to be checked. The comments and `#print axioms` commands are not axiom reports. This bounded witness result alone neither supplies a uniform primitive-recursive witness code nor proves a syntactic iPRA statement. Its only dependencies and elementary finite controls are recorded by the checker; they do not validate Lean elaboration or arbitrary-model theorems.

From `Computability/DiophantineConsistency`, reproduce with `python3 -I -S -B research/ordinary13-pell-period-c-replacement-draft/check.py` and compare the output to `receipt.json`.
