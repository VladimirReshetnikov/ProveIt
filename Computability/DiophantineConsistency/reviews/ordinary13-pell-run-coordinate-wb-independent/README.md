# Independent source review of the Pell run and coordinate WB clients

The proposed composition follows the inspected generic source interfaces: its blueprint arity, separate all-`IΣ₁` majorant, candidate-PRA model assumptions, coordinate contexts and `wb_exs_bt'` premises align. No concrete source-level interface mismatch was found. Both clients and their prospective upstream providers remain **unelaborated**, so this is not a checked `WB` theorem or an iPRA result.

For the run, `runDef` is defined as the one-parameter blueprint's `resultDef`. The generic `wb_resultDef` requires zero- and successor-clause `WB` facts and an all-`IΣ₁` majorant with context `[result,time,parameter]`; `run_wb_of_inputs` exposes exactly those three premises and supplies the proposed construction and `pairValueBound`. The selected assembly calls separately drafted clause and majorant clients. Its candidate-PRA-model arithmetic operations mirror the existing generic source section, and the inspected `standardModelIOpen` has the indicated candidate-PRA-model conclusion. Actual inference and definitional equality of the local instances still require elaboration; the client does not assume that its candidate-PRA model itself is an `IΣ₁` model.

For each coordinate, the literal graph is an existential state satisfying the run graph and the relevant projection graph. In the outer context `[out,time,a]`, adjoining state yields `[state,out,time,a]`; the proposed evaluations identify that same state with `run (e 1) (e 2)` and the output with its first or second projection. The replacement chooses the **same** state, so it preserves the full body if its quoted evaluation theorem is accepted. Applying the proposed horizon inequality with `i=u=e 1` and `a=e 2`, together with the separately proposed bound-term valuation, gives the inequality required by `wb_exs_bt'`.

The inspected `wb_exs_bt'` additionally requires the body's `Σ₁` hierarchy and `WB M` facts. The coordinate draft explicitly proposes those through `by simp`, `run_wb_selected`, the projection-graph facts and `wb_auto`; none has been checked here. In particular, the independent quotation `change` steps, graph-evaluation simplification, local model instances, imported draft namespaces and transitive compiled providers are unresolved elaboration questions.

Even if all those steps succeed, `WB M` supplies a monotone model function witnessing bounds for each named formula. It does not by itself construct a single uniform primitive-recursive bound for every nested witness in the full bounded period formula, prove that formula's evaluation bridge, or establish classical-to-intuitionistic proof transfer.

The independent checker pins both drafts and their generic interfaces, checks the source calls and explicit premises, and evaluates small natural state/projection examples with asymmetric time and parameter slots. These tests do not inspect Lean's generated syntax or validate any proof object. From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-pell-run-coordinate-wb-independent/check.py | cmp - reviews/ordinary13-pell-run-coordinate-wb-independent/receipt.json
```

No Lean, build, staging, provider audit, axiom report or iPRA derivation was run.
