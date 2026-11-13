# Proposed `WB` clients for the represented Pell coordinates

Existing `PRAWitnessPR.wb_exs_bt'` fits the extra state existential in the Pell `xDef` and `yDef` graphs. This inert source proposes both clients, using the separately drafted `WB` result for `runDef` and the existing projection-graph `WB` facts. **None of the proposed source or prospective upstream providers has been elaborated.** This is not a checked witness-bound theorem, a uniform primitive-recursive bound for the period formula, or an iPRA derivation.

Both coordinate graphs have the literal structure

```text
∃ state, runDef(state,time,a) ∧ pi₁Def(out,state)
∃ state, runDef(state,time,a) ∧ pi₂Def(out,state), respectively.
```

The proposed state-body contexts are `[state,out,time,a]`; after the state is bound, the outer environment is `e=[out,time,a]`. The source proposes to evaluate the run graph as `state=run (e 1) (e 2)`. At an `IΣ₁` model instance, the existing source-only paired-state estimate at `i=u=e 1` bounds **that same state** by `pairValueBound.vval e`, after the separately proposed `BoundTerm.vval` identification. The replacement clauses keep the state and its projection relation unchanged.

On the candidate-PRA-model side, the proposed body `WB` proofs combine `run_wb_selected` with the existing `wb_pi₁Def` or `wb_pi₂Def`; `wb_exs_bt'` then uses the all-`IΣ₁` replacement, the explicit `pairValueBound`, and body `WB` to handle the state existential. The model arithmetic operations and the `IOpen`/`PA⁻` setup follow the existing witness-calculus pattern. The result would be `WB M xDef.val` and `WB M yDef.val` in the specified candidate-PRA models.

The direct `change` steps matching the two independent quotations, the evaluation `simp` proofs, hierarchy checks, `wb_auto`, `BoundTerm` rewrites and typeclass/provider resolution are untested. The import `DiophantineConsistency.PellRunWBComposition` and its upstream draft imports are prospective logical providers; this packet creates no source overlay or compiled object. A successful compatible elaboration and axiom audit of the full chain is still required.

`WB M` existentially supplies a monotone **model function** bounding witnesses. Even if checked, these coordinate clients would not by themselves construct a single primitive-recursive bound code for every nested witness of the complete period formula, establish its formula-evaluation bridge, or yield an iPRA proof. The conditional parent lift and original consistency equation remain separate.

The checker pins the relevant source signatures and tests 35 small standard-natural state/projection instances with the intended context and bound. It does not inspect Lean's generated AST or validate the proposed proof tactics. From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary13-pell-coordinate-wb-draft/check.py | cmp - research/ordinary13-pell-coordinate-wb-draft/receipt.json
```

No Lean, build, staging, provider authentication or axiom report was performed.
