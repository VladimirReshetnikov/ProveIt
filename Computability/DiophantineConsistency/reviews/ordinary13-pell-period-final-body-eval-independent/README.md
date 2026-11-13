# Independent source review of the Pell final-body evaluation draft

The intended quotation and `BodyData` agree on all eight named slots and all six conjuncts. The three embedded Pell graphs use the inspected `(output,time,parameter)` order. No concrete source-level mismatch or simplifier hazard was found, but the proposed single `simp` proof, quotation-generated syntax, instance resolution and imported providers remain **unelaborated**.

The vector is `[t,r,y,x,h,c,m,a]`. Consequently the graph argument vectors are `yDef [e5,e6,e7]`, `xDef [e3,e4,e7]`, and `yDef [e2,e4,e7]`; the equalities use `h=e4`, `m=e6`, `c=e5`, `x=e3`, `r=e1`, `y=e2` and `t=e0`. The pinned `BodyData` has exactly the same three graph and three arithmetic conjuncts in the same order. The later source applies the proposed bridge to the separately drafted r and t replacement clients; those clients' arithmetic and provider limitations are unchanged.

Foundation's inspected `Semiformula.eval_substs` is a simp lemma for evaluation after substitution, and the represented-graph infrastructure exposes a simp evaluation equivalence; existing arithmetic clients use the same `simp [..., Semiformula.eval_substs]` pattern. That is source-level support for the proposal, not a demonstration that this particular quotation elaborates or that simplification closes the exact goal. The statement concerns one internal Lean quotation, not the semantics of an external TeX or PDF page.

The independent checker pins the quote, named body, coordinate graph definitions and substitution interfaces. It compares each of the six intended conjuncts against its slotted interpretation on finite natural controls; all eight one-slot mutations of a selected true instance are detected. Those controls do not prove an arbitrary-model equivalence or validate Lean's quotation AST. The four earlier witness replacements, hierarchy facts, full uniform bound, provider/axiom checks and iPRA transfer remain separate.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-pell-period-final-body-eval-independent/check.py | cmp - reviews/ordinary13-pell-period-final-body-eval-independent/receipt.json
```

No Lean, build, staging, provider audit or axiom report was run.
