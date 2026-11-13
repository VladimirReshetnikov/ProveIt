# Independent coherent concrete-increment review

This reviews paired packet `dab52dbfea`. In each IΣ₁ model, `mask` is the cast
of the explicit standard finite-list value constructed by
`CompactConcreteMask`; `mask_eq_bit_recipe` identifies it with the cast of
that list's unexpanded natural-number bit-exponent recipe. `recipe_digits`
requires **all three explicit premises** `0<N`, `1≤C`, and

```
NoCarry (C−1) (mask * rep (67*8807) N + 1).
```

It concludes `dig 67 C 0 = 1` and `dig 67 C k ≤ 3` for every model index
`k<8807*N`. The theorem does not derive the NoCarry premise or equate this
symbolic list value with the retained MC payload or an actual equation graph
port. It is not an all-model machine simulation or an iPRA proof.

The older 24-module window and the 342-module endpoint successor have six
unequal common `.olean` hashes. The wrapper rebuilds the audited
`CompactDummyBound`, `CompactMaskSlot`, and `CompactMixedIncrement` sources
against **each respective endpoint successor**, then compiles the final
composition on that same successor and the two separately audited list/mask
seeds. This audit independently compares both provider object sets, verifies
the six differences, and checks all source/object/log hashes, corresponding
paired outputs, direct imports, and the complete final overlays for all eight
compiler steps. It reruns the concrete-mask independent audit, which in turn
reruns the generic list and endpoint successor audits. Exact declaration names
and axiom reports are checked; all nine reports per side list Lean
metatheoretic `propext`, `Classical.choice`, and `Quot.sound`, with no warning
or `sorryAx` in the final logs. The paired outer session 22885 and all eight
compiler/dependency steps are recorded as exit 0.

The first wrapper preflight, session 48498, is retained as exit 1 before
output creation or Lean launch: it used the wrong field name for one parent
receipt. The corrected schema controls are synthetic checks of both exact
receipt-key conventions, missing/conflicting fields and a wrong digest; this
audit reruns them normally (exit 0) and with optimized Python (exit 1 by the
explicit guard). These controls are not an independent proof of the model
theorem.

The inherited provider has no complete printed axiom inventory;
package-transitive and dynamic ancestry are not fully authenticated. Memory
monitoring is sampled, not a hard process-tree quota, and `--deps` timeout is
not a whole-tree guarantee. The audit uses original `/tmp` objects, performs
point-in-time hash checks, and starts no Lean process.

Run from the repository root:

```
python3 -I -S Computability/DiophantineConsistency/reviews/compact44-concrete-increment-independent-audit/audit.py
```

Actual read-only audit session 45378 exited 0; see `CHECK.json` and
`terminal-observation.json`.
