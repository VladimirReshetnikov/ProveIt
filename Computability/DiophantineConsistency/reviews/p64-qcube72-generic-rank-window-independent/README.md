# Independent review of the generic 72-zero rank window

**PASS within the direct captured-provider scope.** The no-Lean `check.py`
rechecks the observed outer exit and child exit, source and runner snapshots,
compiler log, retained and live object hashes, all recorded direct guards,
and the residual provider against its separately successful producer receipt.
The other direct provider is the captured `P72Window.olean`; this audit does
not establish its source-to-object or full transitive ancestry. The axiom
report is `propext`, `Classical.choice`, and `Quot.sound`. The audit does
not replay Lean; dynamic and between-sample ancestry remains inherited.

The theorem assumes an `IΣ₁` model, natural ports, positive witnesses, an
actual zero of the 72 graph, and the explicit mask inequalities `p₂<p₀` and
`p₃<2p₀` in the model. It concludes `0<R` and `ι(R)+1<ι(q)^4` in the
model difference ring, for the actual natural-model rank `R` and
`q=p₀v₀+1`. The rank uses truncated subtraction in the natural model; the
proof extracts the unchanged transport residual to justify the cast used
by the ring window. The mathematical proof first obtains positive gap
`v₁+v₂<q`, binds the rank expression, then applies the captured generic
window under both mask hypotheses.

The compact-port specialization is a **separate unchecked draft**. This
generic result does not establish `2R<c`, the first-index relation, a reverse
witness map, or an iPRA endpoint. The source's “source-only draft” header is
historical and preserved byte-for-byte; the recorded attempt02 compiled.

Run while the live captured temporary paths remain present:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/p64-qcube72-generic-rank-window-independent/check.py
```
