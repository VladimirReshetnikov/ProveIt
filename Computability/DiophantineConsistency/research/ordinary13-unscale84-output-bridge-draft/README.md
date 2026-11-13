# Proposed equality between the two generated 84 outputs

`Unscale84OutputBridge.lean.src` is **unelaborated source**, not a checked
Lean theorem or an end-to-end iPRA proof. It proposes the missing explicit
interface between `PositiveUnscale84GraphDraft` (used by the 84↔87 endpoint)
and `PositiveUnscaled84GraphDraft` (used by the 83↔84 bridge).

`output_eq` proposes that their `.output` expressions are definitionally
equal for the **same arbitrary integer tuple p**, with proof `rfl`. The
checker independently verifies that both generated sources have the exact
same 84 JSON operation lines, witness and port mappings, and select `out` as
the output field. The enclosing graph structures expose different extra
fields; matching source text is good evidence for the proposed projection
equality but is **not** a successful Lean elaboration of `rfl`.

Given the exact same-K positive-model bridge for the 87 graph,
`bridge84` proposes to use the existing 84 positive-model endpoint and
`IPRAOrdinary12.bridge_of_positive`, then rewrite with `output_eq` to supply
the *other* 84 graph namespace expected by `Positive83To84BridgeDraft`.
`bridge83` retains the 83 gamma and 84 divisibility cuts. `native85` also
retains the 81↔83 cross-root cut; no cut is silently discharged. The
`fixed_native85` variant supplies its 87 bridge from the separately
unelaborated fixed compact 87/88 chain, while retaining all three graph cuts.
All tuples use the same compact natural K and the same natural-to-integer
port casts.

Every result in this packet, including `rfl`, the two bridge adapters, the
fixed compact chain, graph/cast equalities, graph-cut source proofs,
source/object/provider closure and axiom reports, remains unchecked. The
final theorem is conditional source, not a verified proof in iPRA and not a
physical PDF, coefficient-byte or independently identified ZFC encoding
binding. The declared `#print axioms` commands have not run.

From `Computability/DiophantineConsistency` reproduce the receipt:

```
python3 -I -S -B research/ordinary13-unscale84-output-bridge-draft/check.py
```
