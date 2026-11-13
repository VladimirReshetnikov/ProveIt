# Proposed evaluation bridge for the Pell final body

This inert source proposes a proof of the `BodyEvaluationBridge` premise left by the [final r/t replacement client](../ordinary13-pell-period-final-replacements-draft/README.md). Its conclusion identifies the actual quoted eight-variable `finalBody` with the six named graph/arithmetic conjuncts used by those clients. It also proposes passing that bridge to the two conditional replacement theorems. **No Lean elaboration or compilation has occurred.**

The intended vector is `[t,r,y,x,h,c,m,a]`. The bridge compares the quoted body with exactly:

```text
yDef(c,m,a) ∧ h=2*m*c ∧ xDef(x,h,a) ∧ yDef(y,h,a)
∧ x=1+c*c*r ∧ y=t*c*c.
```

The existing coordinate source uses `(out,time,parameter)` for both graph definitions. Thus the three graph vectors are `[e5,e6,e7]`, `[e3,e4,e7]`, and `[e2,e4,e7]`; the remaining equations use the same eight slots. The proposed proof is the focused simplification `simp [BodyData, finalBody, Semiformula.eval_substs]`, following patterns in existing represented-arithmetic clients. Whether the quotation macro, graph evaluations, numeral casts and simplifier actually elaborate and close the goal in a coherent provider environment remains untested.

If the proposed bridge and the separately drafted arithmetic replacements check, the two final `Replacement` obligations would be supplied without an extra evaluation hypothesis. The first four replacement obligations, hierarchy facts and full-period `WB` composition remain separate. The `WB` statement would still quantify over a monotone model function; it does not itself produce a uniform primitive-recursive bound/code for all nested witnesses or an iPRA proof. The parent-lift hypotheses and original consistency-equation endpoint are unaffected.

The checker pins the source quotations and draft, compares all named source positions, and runs 144 standard-natural controls of the intended formula and `BodyData` on true and false cases. It does not inspect the Lean-generated quotation AST, prove an evaluation lemma, resolve prospective imports, execute `#print axioms`, or validate a provider chain. The import names an inert source proposal, not a built module. From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary13-pell-period-final-body-eval-draft/check.py | cmp - research/ordinary13-pell-period-final-body-eval-draft/receipt.json
```

No Lean, build, staging, model transfer or new iPRA theorem was produced.
