# Independent source review of the Pell c replacement

The proposed c replacement matches the inspected coordinate-graph argument order, five nested witness contexts and candidate bound. No concrete source-level algebra or interface error was found. The body-evaluation bridge, source drafts and all Lean tactics remain **unelaborated**, so this is not a checked replacement theorem or an iPRA result.

The outer context is `[m,a]`; `bodyC` successively introduces `[h,x,y,r,t]`, yielding final-body context `[t,r,y,x,h,c,m,a]`. Its first intended `BodyData` conjunct is `yDef(c,m,a)`. The inspected represented-function definition says the graph's zeroth argument equals the function applied to the remaining arguments, so the proposed `y_defined.defined ![c,e 0,e 1]` has the intended direction `c=ycoord m a`. Applying the supplied body bridge is essential: the draft does not silently establish the quotation's evaluation.

The inspected coordinate bound and separately drafted binary-power comparison have the required order:

```text
c = ycoord m a ≤ power (2*(a+2)) m ≤ Exp.exp (2*(a+2)*m).
```

`boundC` is `exp2 (2*(#1+2)*#0) 0` in context `[m,a]`; the inspected `exp2` valuation makes this the displayed exponential. The proof proposes to keep the same c and the entire original five-witness body evidence. It does not need a positivity assumption, and the case `m=0,c=0` is included. The exact graph equivalence, repeated existential simplification, `BoundTerm.vval` normalization, numeral coercions, instance resolution and the final `simpa` still need a coherent Lean check.

The `_closed` client merely invokes a separately proposed, likewise unelaborated body bridge. The x/y replacement obligations, hierarchy facts, source/object provenance, full uniform witness-code bound and iPRA proof transfer remain separate.

The independent checker pins the source draft and interfaces, checks the exact graph signature and witness order, follows the bound-chain source declarations, and runs finite recurrence controls including index zero. Such controls do not validate Lean's generated quotation AST, typeclass inference or any quantified model theorem. From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-pell-period-c-replacement-independent/check.py | cmp - reviews/ordinary13-pell-period-c-replacement-independent/receipt.json
```

No Lean, build, staging, provider audit or axiom report was run.
