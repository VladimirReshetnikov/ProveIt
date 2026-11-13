# Proposed `WB` composition for the represented Pell run

This inert client attempts to connect the separately drafted Pell recursion estimates to the existing `PRAWitnessPR.wb_resultDef` interface. Its prospective imports and its own proof are **unelaborated**. It is not a verified Lean result, a uniform primitive-recursive bound for the entire period formula, or an iPRA derivation.

`run_wb_of_inputs` exposes the exact three premises for the one-parameter Pell blueprint:

1. `WB M blueprint.zero.val`;
2. `WB M blueprint.succ.val`;
3. `PellValueMajorant`, the all-`IΣ₁`-model bound on paired recursion values with context `[result,time,parameter]`.

Under the source's classical candidate-PRA model assumptions for M, it proposes to identify `runDef` with `blueprint.resultDef` and invoke the existing `wb_resultDef` using `pairValueBound`. Its result is `WB M runDef.val`. The majorant is quantified over separate `IΣ₁` models as required by that existing theorem; it does not assume that the candidate-PRA model M itself satisfies `IΣ₁`.

`run_wb_selected` proposes to supply these three premises from the separate zero-clause, successor-projection and majorant clients. It obtains the arithmetic-reduct `IOpen` instance through the existing `PRAModelIOpenPairing.standardModelIOpen` source interface. The local arithmetic operations and model assumptions are copied from the `PRAWitnessPR` section. In particular, this proposed no-extra-argument assembly **depends** on all of the imported source-only lemmas: the previous successor body interpretation and its `change`/`wb_auto` proof, the paired-state growth proof, and the `BoundTerm.vval`/Fin-1 mapping. None has been compiled as part of this packet.

`WB M` existentially supplies a monotone bounding **model function** for witnesses of one formula. It does not itself exhibit one primitive-recursive code uniform across models. Moreover, `runDef` is only the encoded recursion result: proving `WB` for the coordinate graphs and for every existential in the full bounded period formula, proving a uniform candidate-PRA bound/code when needed, establishing the formula evaluation bridge, and the subsequent syntactic/iPRA and parent-lift steps all remain separate. The `#print axioms` declarations are requests in inert source and have not been executed.

The checker pins the participating drafts and existing source signatures, verifies the blueprint arity and expected argument positions, and checks the explicit generic and selected source calls. It does not elaborate Lean, resolve imported objects, validate axioms, or execute the witness-bound proof. The proposed module names refer to future source providers; no overlay or object is created. From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary13-pell-run-wb-composition-draft/check.py | cmp - research/ordinary13-pell-run-wb-composition-draft/receipt.json
```

No Lean, build, staging, provider authentication or iPRA claim was made.
