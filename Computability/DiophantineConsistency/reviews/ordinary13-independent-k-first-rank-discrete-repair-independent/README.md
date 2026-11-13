# Independent review: discrete-order source repair

The isolated [source alternative](../../research/ordinary13-independent-k-first-rank-discrete-repair/README.md) addresses the specific missing unit gap identified in the [original review](../ordinary13-independent-k-first-rank-source-independent/README.md). I found no source-level direction or assumption mismatch in the repair. It remains unelaborated; this review does not certify Lean tactics, typeclass instances, imports, the other proof steps or provider compatibility.

The exact difference from the frozen first-rank source is the replacement of the single positive-C `halpha` proof by the four-step model-natural argument, plus the separate namespace and axiom-query names. From `0<Q−F'−A`, the new source obtains `ι(F+alpha)<ι q`, applies `ι_lt_ι.mp` to reflect it into `F+alpha<q`, uses the natural successor step `add_one_le_iff.mpr`, and re-embeds `F+alpha+1≤q` with `ι_le_ι.mpr`. The final ordered-ring inequality is then a direct linear consequence. The pinned source definitions state `ι_lt_ι : ι a < ι b ↔ a < b` and the analogous ≤ equivalence, so both indicated directions match the desired conversion. The earlier rational countermodel violates the newly introduced successor premise, as expected; it was never a countermodel for the model-natural statement.

The alternate keeps the first norm, rank equation, port and main-helper assumptions unchanged. The code's `#print axioms` commands have not run and provide no observed axiom result. Separate graph-to-unit, child J positivity, model cast, rank representation, source selection, and end-to-end iPRA obligations remain.

The receipt reproduces the author checker, reconstructs the exact source delta independently, pins the relevant difference-ring source signatures, and tests the successor step on bounded naturals. These checks do not replace Lean elaboration. From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B reviews/ordinary13-independent-k-first-rank-discrete-repair-independent/check.py | cmp - reviews/ordinary13-independent-k-first-rank-discrete-repair-independent/receipt.json
```
