# Three PA194 timing variants

Each variant has 194 working states and uses the two literal shortcuts
documented in the
[core reductions report](../../../../../docs/pa194_ax11gdh_research_2026-11-15/research/core_reductions/README.md).
They replace native control 26 reading 1 with `1 R 91` and control 101
reading 0 with `0 R 17`. The generator applies those edits to each pinned
parent, retains its blank start at native control 74, and verifies the
resulting bytes against the [archive catalogue](../../../../../docs/MACHINE_FILES.tsv).

| Table | Exact native SHA-256 | iPRA derivation |
| --- | --- | --- |
| `primary_fast` | `d8f3b1b8e994cccb0ce2ce0950ff1ea0e1729570501538b6f0a6c110c8794233` | [`PA194FastNative.consistency_iff_literal_nonhalt`](PA194FastNative.lean) |
| PA194B with both shortcuts | `3310f1106c0d431cc7b56a8229cafa120f6030388cf8af4297cfd987136f5bc5` | [`PA194BFastNative.consistency_iff_literal_nonhalt`](PA194BFastNative.lean) |
| PA194SEL with both shortcuts | `e93b8634951bf934569e43e418b4b2bfcb329d61c3720f6880bf05003b112be1` | [`PA194SELFastNative.consistency_iff_literal_nonhalt`](PA194SELFastNative.lean) |

[`PA194GuardedShortcuts.sameHalt`](PA194GuardedShortcuts.lean) proves a
tape invariant along each blank run using kernel checks of the incoming
rows. Each fast step matches one or three parent steps. The segment
argument compares halting at arbitrary clocks in models of `IΣ₁`.
All three native endpoints derive `Con(PA) ↔ ¬Halt` in standard iPRA.
Their Lean axiom audits report `propext`, `Classical.choice`, and `Quot.sound`.

Run with the [primary literal](../../native-endpoint/README.md),
[PA194B](../pa194b/README.md), and [PA194SEL](../pa194sel/README.md)
replay outputs.

```sh
pa=Computability/BusyBeaver/Research/PA/verification
bash "$pa/pa194/ipra/variants/pa194fast/check.sh" "$literal" "$shared" /dev/shm/pa194fast-replay "$sel"
```

The fourth argument enables the two companion replays. With the first
three arguments the checker replays `primary_fast`. Each invocation
regenerates the selected native bytes and finite Lean certificates.
