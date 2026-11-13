# Proposed extraction of the Pell successor projection bounds

This separate inert client proposes proofs of the two explicit successor-bound premises in the [Pell blueprint WB draft](../ordinary13-pell-blueprint-wb-draft/README.md). It interprets the quoted six-variable successor body, extracts the embedded first and second projection equalities, and applies Foundation's `pi₁_le_self` and `pi₂_le_self`. It then proposes to call the earlier conditional successor client. **Neither draft has been elaborated or compiled**, so these are source proposals, not discharged Lean obligations.

The earlier inner formula has the intended environment `[y,x,out,previous,index,b]`. The central `succInner_eval` proposal states its interpretation as

```text
x = pi1(previous) ∧ y = pi2(previous)
∧ out = pair((b+2)*x+(b+1)*(b+3)*y, x+(b+2)*y).
```

The graph's index parameter is present but unused by its actual successor equation. The proposed proof uses `simp [succInner, Semiformula.eval_substs]`, relying on the imported graph representations for both projections and pairing. Whether those simplification lemmas fire in the selected provider environment is untested.

For `SecondBound`, the outer environment is `[x,out,previous,index,b]`; after adjoining y, the previous value is inner index 3, hence `e 2` before adjoining. The second graph equality and `pi₂_le_self` give `y≤e 2`. For `FirstBound`, the outer environment is `[out,previous,index,b]`; after adjoining x and extracting an existential y, the same value is inner index 3 and `e 1` in the original vector. The first graph equality and `pi₁_le_self` give `x≤e 1`. The final client proposes `succ_wb_of_bounds first_bound second_bound`.

Remaining source-level risks include the exact Lean quotation AST and binder order, `Semiformula.eval_ex` and graph-simplification rewrites, finite-vector simplification, local `IOpen`/`PA⁻` instances, and the earlier draft's `change` and `wb_auto` steps. The import `DiophantineConsistency.PellBlueprintWB` names an inert draft as a prospective provider; no source overlay, compatible compiled object, resource guard or axiom report is supplied. The zero and successor results remain unverified until the whole dependency chain is elaborated and audited.

Even a successful `WB` proof for the Pell recursion graph would be model-level and existential in a monotone bounding function. It would not automatically supply one uniform primitive-recursive bound for every nested witness of the period formula, prove its `PeriodEvaluationBridge`, or construct an iPRA derivation. Those obligations remain separate.

`check.py` pins the two drafts and their graph/calculus sources, checks the intended context and transition shapes, and runs 750 standard-natural projection/transition controls. The checker does not inspect Lean's generated syntax or prove its tactics. From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary13-pell-blueprint-projection-bounds-draft/check.py | cmp - research/ordinary13-pell-blueprint-projection-bounds-draft/receipt.json
```

No Lean, build, staging or new iPRA result was produced.
