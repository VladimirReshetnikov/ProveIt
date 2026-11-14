# Concrete target proof relation and leaf witnesses

`PA194TargetProofLeaf.lean` defines `TargetProof program result` using a fixed
finite PRA root evaluator for the actual-length-guarded target history. A
proof program must have positive Foundation vector length and its last
history value must be `result + 1`. `TargetProvable result` existentially
quantifies the program. `targetProof_definable` and
`targetProvable_definable` prove that these relations are Σ₁-definable in
every candidate-PRA model whose arithmetic reduct satisfies IΣ₁.

For every such model, including nonstandard inputs, the package constructs a
one-line target proof for head1 and each of head2–head6, rho8, oldBundle and
the diagonal. The rho8 witness requires `u ≤ a`; the oldBundle witness
requires both `c ≠ a` and `c ≠ b`. `target_leaf_closure` collects the eight
additional leaf witnesses into the `LeafClosure` needed by the history
invariant. `targetProof_sound` instantiates that invariant for an arbitrary
Σ₁ predicate, retaining its head1, MP, generalization, and leaf closure
assumptions.

The separate [`pa194-target-proof-generalize`](../pa194-target-proof-generalize)
package proves model-uniform generalization closure; the separate
[`pa194-target-proof-mp`](../pa194-target-proof-mp) package proves MP closure
by combining proof histories and accounting for their reverse offsets.
This independent line encoding is not yet identified with the upstream
certificate format, and source-proof compilation and machine/calculus
calibration remain open. These results alone do not prove a PA194/Con(PA)
implication.

Run from the repository root with the matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-target-proof-leaves/check.sh
```

The final module was rebuilt against the freshly rebuilt actual-length module
and the previously checked history suffix. A full nested replay of this
wrapper has not yet been completed. Its printed axiom dependencies contain
no `sorryAx`.

An independent suffix replay recompiled this module against the separately
checked vector-length and target-history objects, reusing the other prerequisite
overlays. Its reported theorem axioms did not include `sorryAx`.
