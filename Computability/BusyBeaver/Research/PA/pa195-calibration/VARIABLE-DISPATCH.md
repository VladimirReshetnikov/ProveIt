# Closing encoded variable nodes

`PA194VariableDispatch.lean` constructs a primitive-recursive dispatcher
that decodes the pair-plus-one node, selects the bound-variable operation
for tag zero and the free-variable operation for tag one, and proves both
equations in every candidate-PRA model. It handles nonstandard labels,
indices and depths. The two pairing projection codes are parameters with
candidate-PRA certificates; `PRA_has_stackProjections` supplies them
existentially, without fixed serializations. Foundation named-variable constructor identification is additionally
proved under IΣ₁. Other tags are outside the theorem. This is a variable base case, not a generic term/formula traversal,
a `closeLabel` correctness theorem, or a machine consistency implication.

Rebuild with the audited overlays using `check-variable-dispatch.sh`.
