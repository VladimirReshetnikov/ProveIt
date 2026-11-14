# Target history with actual vector length

`PA194TargetVectorLength.lean` constructs a fixed finite candidate-PRA
`lengthCode` and proves `length_model`: in every candidate-PRA model whose
arithmetic reduct satisfies IΣ₁, its result is exactly Foundation's `len v`
for the pair-plus-one vector `v`, including nonstandard vector codes. The
proof characterizes the first zero reached by repeated vector tail using
internal IΣ₁ induction, then uses bounded search and Foundation's `len v ≤ v`
bound.

The fixed code `autoNext` feeds that computed length into the guarded target
step. `autoNext_model` describes its behavior on every model input, and
`auto_rejects_past_length` proves that stages at or beyond the vector's actual
internal length reject. `autoHistory_sound` and `autoAccepted_sound` carry
the conditional history invariant through internal IΣ₁ induction. They still
require the Σ₁ predicate, head1, MP and generalization closure premises, and
the eight `LeafClosure` premises from the extended interpreter.

This proves the earlier length-correspondence obligation for Foundation's
vector encoding. The later [`pa194-target-proof-mp`](../pa194-target-proof-mp)
package supplies a concrete predicate satisfying the closure premises. It
does not construct the source-proof compiler, identify
the independent line encoding with the upstream certificate format, or prove
machine/calculus calibration or a PA194/Con(PA) implication.

Run from the repository root with the matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-target-history-length/check.sh
```

The final module was rebuilt against the freshly rebuilt extended-history
suffix and previously checked guarded-history and deeper prerequisites. A full
nested replay of this wrapper has not yet been completed. Its printed axiom
dependencies contain no `sorryAx`.

An independent suffix replay recompiled the length and automatic-guard module
against separately checked guarded/extended history objects and reused other
prerequisite overlays. The reported theorem axioms did not include `sorryAx`.
