# The primary_fast timing variant

`primary_fast.native.tm` is the 194-working-state primary PA194 table with
the two literal shortcuts documented in the
[core reductions report](../../../../docs/pa194_ax11gdh_research_2026-11-15/research/core_reductions/README.md).
They replace the transitions at native control 26 reading 1 and control 101
reading 0. The generator uses the pinned primary table and state map to
reconstruct the native table with the archived SHA-256
`d8f3b1b8e994cccb0ce2ce0950ff1ea0e1729570501538b6f0a6c110c8794233`
and emits its dense rows for Lean.

[`PA194FastInvariant`](PA194FastInvariant.lean) proves the needed tape
conditions throughout the blank run, using finite checks of the incoming
rows. [`PA194FastSegment.sameHalt`](PA194FastSegment.lean) matches each
fast step by one or three primary steps. The segment argument compares
halting in both directions at arbitrary clocks in models of `IΣ₁`.
[`PA194FastNative.consistency_iff_literal_nonhalt`](PA194FastNative.lean)
proves `Con(PA) ↔ ¬Halt(primary_fast)` in standard iPRA. Its Lean axiom
audit reports `propext`, `Classical.choice` and `Quot.sound`.

With the [primary literal](../../native-endpoint/README.md) and
[PA194B](../pa194b/README.md) replay outputs, run from the repository root.

```sh
pa=Computability/BusyBeaver/Research/PA
bash "$pa/pa194/ipra/variants/pa194fast/check.sh" "$literal" "$shared" /dev/shm/pa194fast-replay
```

The check regenerates the exact native bytes and rebuilds the candidate's
four Lean modules. It uses the retained lower dependencies of the primary
and PA194B stages.
