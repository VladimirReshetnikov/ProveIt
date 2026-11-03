# Attempts at the static compact `PackingInput` fields

The separated clients prove the five static `PackingInput` fields for the
chosen compact dimensions and exact symbolic native masks: `1<N`, `w<N`,
`lowNat+1<B`, `1≤highNat`, and `highNat<B`. The native `highNat` is the mask
used by `PackingInput`; the graph's encoded high port includes an additional
`beta`. These are static fields only: no packed word, local no-carry, physical
dummy safety or other `PackingInput` field is established.

Attempts 01 and 02 exited 1 before elaboration because the symbolic-unit
overlay lacks a transitive `BusyBeaver` root. Attempt 02 replaced graph-port
names with the underlying mask recipes, but `CompactFixedBeta` still imported
that root. Attempt 03 used an isolated mixed overlay with BusyBeaver and
FirstOrder roots from the word-side provider and matching hashes for the
directly compared project objects and companions; it exited 1 before
elaboration because the overlay omitted the unit provider's top-level
`ActualRankCalibration` dependency. Attempt 04 exposed all top-level unit
objects and reached elaboration, but **Lean's deterministic heartbeat limit**
was exhausted while checking the mask theorem. It was not a wall-clock
timeout. The geometry declaration's axiom report was printed, but no full
object was emitted and no completed static-field module is claimed.

The four attempts retain exact sources or source hashes, direct dependency
listings, compiler logs, commands, exit receipts and point-in-time overlapping
object/companion observations in `observations/` through `observations04/`.
The mixed overlay is exploratory: matching selected direct inputs and their
companion absences does not authenticate the transitive, package, dynamic or
between-check dependency closure. Attempt 04 took 59.710 seconds and exited
1; its reported error is the 200,000-heartbeat `whnf` limit.

The fifth run compiled `CompactPackingGeometry.lean` without warnings, then
stopped on an addition-order mismatch in the generic mask algebra. That
failed source and log are retained in `observations05/`. After a one-line
commutativity repair, the resumed build compiled
`CompactPackingMaskAlgebra.lean`, `CompactSymbolicMaskData.lean`, and
`CompactSymbolicMaskFields.lean` without warnings or `sorryAx`. The exact
symbolic-mask data client proves definitional equalities to the
`CompactSymbolicPorts.lowNat` and `highNat` expressions, then uses explicit
equality transport to avoid normalizing the large values. The final mask
theorem reports only `propext`, `Classical.choice`, and `Quot.sound`. Checked
source hashes, dependency listings, commands, logs and object hashes are in
`observations05/` and `observations06/`; the words “uncompiled” in the four
checked sources are historical comments. The resumed runner rechecks the
previously captured direct overlaps and companions, but its inherited
transitive/package/dynamic and between-check limitations remain.

See the [field-by-field map](../compact44-packing-obligation-map/README.md)
for the word-dependent conditions and the distinction between the sparse
high-mask target and the full packed product.
