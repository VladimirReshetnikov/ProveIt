# PA194 history-aware formula recursion

`PA194HistoryDispatch.lean` composes the primitive-recursive history and exact
PA194 decoder from `PA194StackHistory.lean` with a two-argument source-tag
dispatcher. It defines `sourceTranslation`, a primitive-recursive
course-of-values code with parameterized formula-constructor operations.

In every candidate-PRA model, its zero, membership, equality, implication,
and universal branch equations hold, including for nonstandard source
codes. The implication equation reads both recursively translated children.
The universal equation uses the **second** decoded source field as the bound
label and the **first** as the recursively translated body, matching the
transposed PA194 universal constructor. Theorems also specialize both
equations to the exact numerical implication and universal constructors;
the implication specialization explicitly excludes its zero-code alias.
The tag, child, and pair-projection
codes are assumed to carry candidate-PRA certificates; existence of these
codes is established in `PA194TagDecoder.lean` and
`PA194StackHistory.lean`. No IΣ₁ assumption is used.

This is a parameterized recursion: the truth, membership, equality,
implication, and binder-closing codes are inputs to the definition. The
implication and binder-closing codes in particular are not yet constructed or
certified here. The equations do not establish a full source-formula
translation, its semantic soundness, or either machine-specific consistency
implication. Rebuild with the pinned overlays:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-history-dispatch.sh
```
