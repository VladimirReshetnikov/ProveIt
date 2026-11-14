# Candidate primitive-recursive variable closure cases

`PA194CloseVariable.lean` constructs explicit primitive-recursive codes for two
variable cases that a capture-avoiding named-variable closure operation needs.
Given a selected label, a free-variable index, and a binder depth,
`closeFreeCode` selects bound variable `depth` when the labels coincide and
leaves the free variable unchanged otherwise. Given a binder depth and an
existing bound-variable index, `closeBoundCode` preserves indices below the
depth and increments indices at or above it.

The numeric equations are checked in every candidate-PRA model, including
nonstandard labels, indices, and depths. The identification of the numeric
codes with Foundation's named `qqBvar` and `qqFvar` constructors has an
explicit IΣ₁ assumption.

These are isolated variable cases: no traversal of function terms, vectors,
formula trees, or binders is constructed here, and no theorem yet connects
these branches to the full `closeLabel` rewriting operation. In particular,
this package does not establish a valid closure code, a full source-formula
translator, PA calibration, or either consistency implication. Rebuild with
the pinned overlays:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-close-variable.sh
```
