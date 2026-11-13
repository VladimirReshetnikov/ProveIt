# Proposed final r/t witness replacements for the Pell period

This inert source proposes model-level proofs of the final two replacement obligations from the [six-witness conditional `WB` client](../ordinary13-pell-period-full-wb-conditional-draft/README.md). The elementary arithmetic splits on `c=0`; the clients preserve all other graph and arithmetic conjuncts. **The quoted final-body evaluation is an explicit, unproved premise**, and none of this source has been elaborated or compiled.

## Arithmetic split

Given natural-model values with `x=1+c*c*r`, the proposed `replaceR` returns an r′ with `r′≤x` and `x=1+c*c*r′`. If c>0, c²≥1 and the original r is bounded; if c=0, the equation is independent of r and r′=0 works. Similarly, from `y=t*c*c`, `replaceT` returns t′≤y preserving that equality: retain t when c>0 and choose zero when c=0. In the zero case the original r or t can be arbitrarily large, so replacing it is essential. The proof source uses the project's `eq_zero_or_pos`, `one_le_mul`, and ordered multiplication interfaces; its tactics and typeclass resolution remain untested.

## Exact body and remaining premise

`BodyData` retains **all six** conjuncts of the prior final formula: the y-coordinate graph at m, the equation h=2mc, both coordinate graphs at h, and the r/t equations. `BodyEvaluationBridge` explicitly requires that evaluation of the prior quoted `finalBody` at `[t,r,y,x,h,c,m,a]` is equivalent to those conjuncts. No proof of that quotation/evaluation bridge is supplied here.

Conditional on that bridge, the proposed `tReplacement` changes only t. Its outer environment is `[r,y,x,h,c,m,a]`, so its bound `#1` is y and c is `#4`. The proposed `rReplacement` first extracts an existential t from `bodyR`, changes only r, then restores the **same** t and every unchanged conjunct. Its outer environment is `[y,x,h,c,m,a]`, so `#1` is x and c is `#3`. These are exactly the `Replacement finalBody boundT` and `Replacement bodyR boundR` inputs of the earlier conditional client, if all source drafts elaborate together.

The other four witness replacements, all hierarchy claims, exact quotation and finite-vector simplification, the `BoundTerm.vval` rewrites, provider/instance compatibility, `wb_auto`, full-period witness-bound composition and its axiom report remain unverified. Even a checked model-level `WB` result would not automatically be a uniform primitive-recursive code for all witnesses or an iPRA derivation. The conditional parent lift and original consistency equation remain separate.

The checker pins the prior source, verifies the stated named context positions and proposed interfaces, and checks 1,440 finite natural replacements including c=0. It does not execute Lean's quotation elaborator, prove the model lemmas, or authenticate imported objects. The prospective import is an inert draft, not a materialized source provider. Reproduce from `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary13-pell-period-final-replacements-draft/check.py | cmp - research/ordinary13-pell-period-final-replacements-draft/receipt.json
```

No Lean, build, staging, provider authentication or axiom report was performed.
