# Independent source review of the period x/y replacements

The proposed x and y clients select the intended nested witnesses, graph arguments and bound-term slots. Their coordinate-growth chains have the correct direction. No concrete source-level mismatch was found; the body bridge, quotation matching, simplification, typeclass inference and prospective providers remain **unelaborated**.

Before x, the environment is `[h,c,m,a]`; its three inner existentials introduce y, r and t, giving `[t,r,y,x,h,c,m,a]`. The x graph is the third `BodyData` conjunct, selected by `data.2.2.1`, with source argument vector `[x,e 0,e 3]=[x,h,a]`. `boundX` uses `#0=h` and `#3=a`. Before y, the environment is `[x,h,c,m,a]`; its two inner existentials introduce r and t, giving the same final-body vector. The y graph is the fourth conjunct, selected by `data.2.2.2.1`, with vector `[y,e 1,e 4]=[y,h,a]`; `boundY` uses `#1=h` and `#4=a`.

The inspected represented graphs use `(output,time,parameter)`, and the existing coordinate bounds followed by the separately drafted variable-base comparison give `xcoord h a, ycoord h a ≤ Exp.exp (2*(a+2)*h)`. The two proposed terms use `exp2(...,0)`, whose source valuation is that same exponential. Both clients return the original coordinate and original body evidence, so no positivity assumption or modification of an inner witness is needed. The exact `change`, repeated `eval_ex`, graph equivalence and `BoundTerm.vval` simplification still require a coherent Lean check.

Each main replacement explicitly assumes `BodyEvaluationBridge`; its `_closed` version merely applies a separately unelaborated proposed bridge. Neither naming convention constitutes a checked proof. The other clients, hierarchy claims, provider/axiom audit, uniform full-period witness code and iPRA transfer remain separate obligations.

The independent checker pins the two clients and source interfaces, reconstructs both contexts and conjunction projections, checks the bound-term expressions and growth-chain declarations, and runs finite coordinate controls including index zero. It does not inspect Lean's quotation AST or execute tactics. From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-pell-period-xy-replacements-independent/check.py | cmp - reviews/ordinary13-pell-period-xy-replacements-independent/receipt.json
```

No Lean, build, staging, provider audit or axiom report was run.
