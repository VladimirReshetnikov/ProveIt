# Independent source review of the Pell h replacement

The proposed h client has the intended four-existential order, eight-slot vector, `BodyData` conjunction projection, and bound-term context. The same-witness argument is correct at source level, including when `c=0`. No concrete interface mismatch was found; the quotation reductions, simplification and prospective providers remain **unelaborated**.

Before h, the outer environment is `[c,m,a]`. The nested bodies expand to `∃x ∃y ∃r ∃t finalBody`, so the proposed extraction order `x,y,r,t` yields the final vector `[t,r,y,x,h,c,m,a]`. The explicit `BodyEvaluationBridge` maps this vector to `BodyData`; its second conjunct is exactly `h=2*m*c`, so `data.2.1` selects the intended equality. The candidate `boundH` is `2*#1*#0`, hence `2*(e 1)*(e 0)` in that outer environment. Returning h unchanged therefore satisfies the inequality and preserves the original entire body, without assuming c or m positive.

The inspected `Semiformula.eval_ex` has the expected cons-vector evaluation direction. The `BoundTerm.poly` valuation uses the term's valuation at e, and the source text matches that intended bound. These observations do not establish that the four-quantifier `change`, repeated simplification, finite-vector reductions, quoted polynomial valuation, or the final `simpa` actually elaborate. The non-conditional-looking client still imports a **separate unelaborated** proposed body bridge; it is not a checked theorem or a provider audit.

This handles only h. The other replacements, hierarchy proofs, complete bounded-witness assembly, uniform code and iPRA transfer remain separate. The independent checker pins the source drafts and interfaces, reconstructs all eight slots and tests the equality on finite controls; it does not inspect Lean's generated AST or run any proof.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-pell-period-h-replacement-independent/check.py | cmp - reviews/ordinary13-pell-period-h-replacement-independent/receipt.json
```

No Lean, build, staging or axiom report was run.
