# Proposed `BoundTerm` and one-parameter bridge for the Pell run

This inert client proposes the exact connection from the source-only [paired-state estimate](../ordinary13-pell-run-exponential-bound-draft/README.md) to the [Pell value-majorant predicate](../ordinary13-pell-period-history-majorant-draft/README.md). Its two upstream imports name prospective source providers; neither those providers nor this file have been elaborated together. No new Lean theorem, witness-bound theorem or iPRA derivation is established.

For a model valuation `e : Fin 3 → V`, the intended context is `[result,time,parameter]`. The proposed `pairValueBound_vval` unfolds the existing `BoundTerm` semantics to

```text
pairValueBound.vval e
  = (2 * 2^(2*(e 2+2)*e 1) + 1)^2.
```

The `exp2` constructor denotes `2^(A*2^B)`; here B is zero, so the internal exponent is `2*(e 2+2)*e 1`. The result slot `e 0` is unused. Simplification of quoted arithmetic terms, model numerals, `exp_zero`, and the syntactic form of `2*F` is proposed in the source; it is not checked by the Python controls.

`PellValueMajorant` instead presents the recursion parameter as `fun j : Fin 1 => e j.succ.succ`. The draft copies the exact `Fin.cases` proof pattern already present in `PRAWitnessPR` to identify it with `![e 2]`. Unfolding the existing `ArithmeticPellRecurrence.run` then turns the desired inequality into the upstream `run_le_exponential_horizon` statement with `u=e 1` and `a=e 2`. The proposed `pellValueMajorant` gives precisely the `hH` premise for `PRAWitnessPR.wb_resultDef` **if** the source is accepted in a coherent provider environment.

That generic theorem still needs witness-bound premises for the recursion's zero and successor clauses. It yields a model-level `WB` assertion, not automatically a single uniform primitive-recursive code for every nested existential in the complete bounded period formula. The exact period formula's evaluation bridge, candidate-PRA transfer premises, positive witness recovery and the conditional parent lift remain open. No conclusion about iPRA or the displayed consistency equation follows here.

`check.py` pins the source drafts and relevant project interfaces, compares their expected signature and context text, and evaluates small exact paired-state controls; it includes an asymmetric check to detect swapping time and parameter, and changes the unused result slot. These finite tests do not execute Lean's quotation elaborator, evaluate `BoundTerm.vval` in Lean, authenticate providers, or establish the quantified majorant. From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary13-pell-run-majorant-client-draft/check.py | cmp - research/ordinary13-pell-run-majorant-client-draft/receipt.json
```

No Lean, build, staging, axiom report or iPRA proof was performed.
