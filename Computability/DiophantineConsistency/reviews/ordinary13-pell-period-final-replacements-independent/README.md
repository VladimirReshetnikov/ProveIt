# Independent source review of the final Pell replacements

The proposed r and t replacements preserve the six displayed body conjuncts and use the intended context slots. Their positive- and zero-c arithmetic is correct at the source level; no concrete index or algebra error was found. The exact quoted-body interpretation is still the explicit **unproved** `BodyEvaluationBridge`, and neither this file nor its upstream providers has been elaborated.

When `c>0`, the intended natural-model order gives `1≤c²`; therefore `r≤c²r≤1+c²r=x` and `t≤t*c²=y`. The proposed clients retain the original witness in that case. When `c=0`, the equations reduce to `x=1` and `y=0`, so the original r and t can be arbitrarily large and cannot be bounded by x or y. Replacing the relevant witness by zero preserves its equation. The four graph/h conjuncts and the other arithmetic equality do not depend on the replaced witness, so they remain unchanged. This is an arithmetic argument for the stated natural models, not a checked Lean proof of the proposed tactics or typeclass resolution.

For t, the environment before binding is `[r,y,x,h,c,m,a]`, so `e 1=y`, `e 4=c`, and `boundT` selects y. For r, it is `[y,x,h,c,m,a]`, so `e 1=x`, `e 3=c`, and `boundR` selects x. The r client opens the inner existential t and restores the **same** t after changing r; the t client leaves r fixed. The source's reconstructed `BodyData` includes all six conjuncts in the same order as the intended prior quote. The proposed `change`, `eval_ex`, `simp`, bound-term valuation and cons-vector reductions remain elaboration questions.

The later client is conditional on the explicit bridge from the quoted `finalBody` to `BodyData`; the source does not establish that bridge. The other four replacement obligations, hierarchy facts, provider chain, full witness-code bound and iPRA transfer remain open even if the local arithmetic is eventually checked.

The independent checker pins both drafts and relevant interfaces, compares the complete six-conjunct text and contexts, verifies that the replacement interface permits new witnesses, and checks finite positive- and zero-c arithmetic controls. It does not inspect Lean's generated quotation AST or execute any proof. From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-pell-period-final-replacements-independent/check.py | cmp - reviews/ordinary13-pell-period-final-replacements-independent/receipt.json
```

No Lean, build, staging, axiom report or provider audit was run.
