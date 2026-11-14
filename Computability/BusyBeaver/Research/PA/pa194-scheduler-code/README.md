# Finite candidate-PRA scheduler dispatch

`PA194SchedulerCode.lean` assembles fixed finite candidate-PRA codes for a
modeled scheduler's fetch, triangular-Cantor command decoding, continuation,
SHIFT/MP/AX dispatch, register updates and SHIFT halt bit. The case formulas
follow the standard PA194 source scheduler's `seed`, `nextN`, `parse`, and
command effects. `store_preserves` proves that every selected update preserves
the concrete Σ₁ `SoundStore` invariant in every candidate-PRA model whose
arithmetic reduct satisfies IΣ₁, including nonstandard states.

The modeled fetch/dispatch assembly has not yet been proved equal to the
standard PA194 scheduler. Its component command effects have separate standard
bindings. This package does **not** connect the assembled step to a
nonstandard PA194 controller trace, identify target provability with internal
PA provability, or prove a PA194/Con(PA) implication.

Run from the repository root with the matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-scheduler-code/check.sh
```

The final module was rebuilt against the freshly generalized SHIFT/MP effect
object and previously checked prerequisite overlays. A full nested replay of
this wrapper has not yet been completed. Its printed axiom dependencies contain
no `sorryAx`.
