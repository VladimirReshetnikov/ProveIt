# Model-length iteration of the coded PA194 scheduler

`PA194SchedulerIteration.lean` packs the modeled scheduler's six registers
using Foundation pairing, defines a fixed finite candidate-PRA state update and
its iteration, and proves `run_sound` by **internal IΣ₁ induction**. Every
model-length iteration from a `SoundPacked` state preserves the Σ₁
`SoundStore` invariant. This includes nonstandard step counts.

The coded initial state is proved sound. Combining the invariant with the
separately checked scheduler halt endpoint yields
`initial_run_halt_provable`: if the modeled halt bit is one after any model
number of iterations from that state, then `TargetProvable 1`. The total
iteration continues mathematically even after a halt; the theorem asks for a
step at which the halt bit is set.

This is a theorem about the independently modeled scheduler, not yet the
literal PA194 controller or machine. The separate standard-input scheduler
binding does not establish their equality on nonstandard traces. Identifying
such a literal trace with the modeled run remains open. The separate
[target-to-PA bridge](../pa194-target-source/README.md) turns `TargetProvable 1`
into an internal PA refutation assuming guarded-gate preservation, which is
still open. No PA194/Con(PA) implication is claimed here.

Run from the repository root with the matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-scheduler-iteration/check.sh
```

The final module was rebuilt against previously checked scheduler and halt
objects and prerequisite overlays. A full nested replay of this wrapper has
not yet been completed. Its printed axiom dependencies contain no `sorryAx`.

An independent suffix replay rebuilt the iteration module against the
separately checked scheduler code and retained deeper prerequisite overlays.
It passed without `sorryAx`; this was not a full nested replay.
