# Source-only literal evaluator and all-ring shear for 72/46

`Shear72Literal.lean.src` defines the exact proposed 72-row expression with 14 variable indices and the four existing integer port leaves. Its proposed `eval_expression` evaluates it over an arbitrary commutative ring using the same style as the checked 71/60 literal evaluator. The proposed `value72_eq_sheared71` updates only index 12 to `V+y` and relates `value72` to the existing `OrdinarySphere7160Literal.value71`; `eval_eq_sheared71` composes both evaluator statements. It asserts only ring-value equality under a signed coordinate update. It does not claim that this update preserves positivity or gives a two-way zero map.

The independent external `check.py` parses the actual source rows, variables and port aliases, compares all 72 rows to the pinned JSON, checks the exact edit against the 71-row parent and the common fixed-port binding, and verifies the cut identity in a sparse polynomial ring. It also compares 200 whole-graph evaluations with signed small integer parameters. Those diagnostics and row equality are not Lean proofs of JSON or file semantics, and do not prove the asserted all-ring Lean theorems.

`OrdinarySphere7160Literal` is the checked historical source interface imported by the proposed new module; its existing successful run and evaluator theorem have their own direct-provider and inherited ancestry qualifications. The `.lean.src` file is inert and has not been elaborated. In particular `simp` over `Function.update`/finite indices and the final `ring` normalization, the evaluator simplification, imports and all `#print axioms` commands remain untested. No live provider selection, coherent rebuild, Lean object or axiom report is claimed. Positive witness conversion in both directions and the iPRA transfer remain separate obligations.

From `Computability/DiophantineConsistency`, run:

```
python3 -I -S -B research/current2011-sheared72-literal-evaluator-draft/check.py | cmp - research/current2011-sheared72-literal-evaluator-draft/receipt.json
```

No Lean/build/staging was performed.
