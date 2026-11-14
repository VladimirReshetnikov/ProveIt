# A positive/negative-pair implication constructor

`PA194DualImpCode.lean` explores an alternative representation for the source
formula translator. Represent a translated formula by a bare numeric pair
`(positive, negative)` of negation-normal-form syntax codes. For a source
implication, a fixed primitive-recursive code forms the output pair
`(Or(left.negative, right.positive), And(left.positive, right.negative))`.
This avoids applying a general recursive negation operation to an arbitrary
syntax tree in the implication branch.

`modelDualImp` checks that exact numeric equation for arbitrary, including
nonstandard, inputs in every candidate-PRA model, assuming certificates for
the two pair projections; existence of such certificates is established by
`PA194StackCode.PRA_has_stackProjections`. `modelDualImpInternal` identifies
the numeric `Or` and `And` constructions with Foundation's named syntax only
under an explicit IΣ₁ assumption.

This is an isolated component, not yet the active source translator: dual
truth and atomic branches, the binder-closing operation, recursive duality
invariants, Foundation syntax correctness in weaker theories, PA
calibration, and the machine-consistency equivalence remain open. Rebuild
using the pinned overlays:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-dual-imp-code.sh
```
