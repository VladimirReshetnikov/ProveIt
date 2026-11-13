# Independent review: zeta-coordinate zero transport

The two pinned graphs both have 85 arithmetic rows, the same 13 inputs and four ports. Their complete generated Lean source rows and output fields match their respective JSON graphs. Parent `k=eta+zeta+1`; raising coordinate 10 makes the probe's `kbase=eta+zeta+1`. The parent `r0=(eta+zeta)-R`, while the raised probe has `r0=(eta+zeta+1-R)-1`, the same signed expression. Every remaining probe row matches after the `k` to `kbase` rename, yielding the claimed forward evaluation identity as an algebraic source-level derivation.

A parent zero therefore transfers to the raised probe valuation. Conversely a probe zero transfers to the parent at its coordinate-10 predecessor only when the probe coordinate is positive; the proposed `raise_lower` explicitly takes that hypothesis. The `SameNoZero` statement is ordered as probe-no-zero iff parent-no-zero, and its two proof branches use the appropriate zero maps. The conditional polynomial bridge has the corresponding direction: it requires probe `ForcedZeta K` and the parent `PolynomialBridge`, both at exactly `ports K`.

`proposed_forcing` composes the previously drafted compact zeta-positivity client, but that client's proof is unelaborated and has its own graph/model/provider obligations. The final native source still requires the original parent polynomial bridge. This transport does not assert an arbitrary-port forcing theorem, authenticate the physical coefficient/PDF instance, or reduce the operation count. No Lean proof or endpoint is established by the receipt.

The checker reproduces the author's receipt, independently compares both full generated graph transcripts and changed rows, and checks the source-level map and bridge interfaces. Run from `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/ordinary13-zeta-unshift85-zero-map-independent/check.py | cmp - reviews/ordinary13-zeta-unshift85-zero-map-independent/receipt.json
```
