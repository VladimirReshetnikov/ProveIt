# Proposed all-model bound for a Pell paired state

This inert source proposes the first concrete model-level lemma needed by the [Pell history-majorant plan](../ordinary13-pell-period-history-majorant-draft/README.md). For every `IΣ₁` model, indices `i≤u` and parameter a, it attempts to show

```text
run i a ≤ (2 * 2^(2*(a+2)*u) + 1)^2.
```

The file has **not** been elaborated or compiled. Its source checker and 605 finite paired-state controls pass; those are not a proof of the quantified theorem or a Lean tactic check.

## Proposed proof from existing interfaces

Write `B=2*(a+2)`. The existing `ArithmeticConstructionBoundPell.x_le` and `.y_le` give each Pell coordinate at i at most `power B i`. Since B≥1 and i≤u, `ArithmeticPow.power_mono_exponent` bounds these by `power B u`. The existing `lt_exp B`, `power_mono_base`, `power_two` and `power_iterate` then propose the algebraic comparison

```text
power B u ≤ power (2^B) u = 2^(B*u).
```

The actual recursion state is the encoded pair of `xcoord i a` and `ycoord i a`; `pair_unpair` relates this pair to `run i a`, and `pair_polybound` bounds it by `(xcoord+ycoord+1)^2`. Combining the two coordinate bounds gives the displayed expression. The first proposed theorem isolates this pair step under explicit coordinate-bound hypotheses; the next two attempt the power and horizon arguments.

This would provide the mathematical inequality underlying `PellValueMajorant`, but it is **not yet that exact theorem**. A further client must verify `pairValueBound.vval e` unfolds to the displayed expression with `e 1=u`, `e 2=a`, identify `(construction.result (fun j => e j.succ.succ) i)` with `run i (e 2)`, and handle the `Fin 1` parameter vector. It must also establish the separate zero/successor witness bounds before applying `PRAWitnessPR.wb_resultDef`. The latter yields a model-level `WB` assertion; obtaining one uniform primitive-recursive bound for every nested witness in `bnd periodDef` still requires additional work.

The proof imports Foundation's pairing definitions explicitly. Its namespace resolution, simplification of `pair_unpair`, ordered-semiring coercions, exponent rewrites, tactics, compatible provider selection, resource behavior and axiom report all remain untested. The source names are pinned against the current Foundation checkout and project files; pinning does not authenticate a compiled object or the full transitive provider chain. No conclusion about the conditional parent lift, a standalone iPRA derivation or the displayed consistency equation follows from the draft alone.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary13-pell-run-exponential-bound-draft/check.py | cmp - research/ordinary13-pell-run-exponential-bound-draft/receipt.json
```

No Lean, build, staging or axiom report was performed.
