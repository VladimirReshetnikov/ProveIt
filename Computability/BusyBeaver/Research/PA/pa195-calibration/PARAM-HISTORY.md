# PA194 parameter-preserving recursive history

`PA194ParamHistory.lean` adapts the reverse-indexed course-of-values history
from [STACK-HISTORY.md](STACK-HISTORY.md) to an update code `next : Code 4`
whose inputs are the stage, prior history, closing label, and binder depth.
The explicit PR history and translation codes take the stage and both model
parameters. The label and depth are preserved unchanged across recursion.

In every candidate-PRA model, `modelHistoryReverse` and `modelLookupEarlier`
show that the explicit lookup/distance codes recover the value at any strictly
earlier stage, even for nonstandard stages, reverse indices, labels, and
binder depths. The proof uses candidate-PRA open induction and certificates
for the two pairing projections, whose existential availability is proved in
`PA194StackCode`. It does not assume IΣ₁.

The update `next` remains an explicit parameter. These history equations do
not yet construct an encoded-syntax traversal, prove the required child-size
bounds, identify Foundation's internal syntax, or establish either iPRA
consistency implication.

Run from the repository root with the audited overlays:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-param-history.sh
```
