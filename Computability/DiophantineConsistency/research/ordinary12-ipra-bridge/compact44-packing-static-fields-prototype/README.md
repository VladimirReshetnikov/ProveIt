# Attempts at the static compact `PackingInput` fields

No complete module in this directory has compiled successfully. The intended
five fields are the chosen-dimension geometry `1<N` and `w<N`, and the exact
symbolic native-mask bounds `lowNat+1<B`, `1≤highNat`, and `highNat<B`.
These are static fields only; establishing them would not construct a packed
word, prove local no-carry or physical dummy safety, or establish the
remaining `PackingInput` fields.

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

`CompactPackingGeometry.lean`, `CompactPackingMaskAlgebra.lean`,
`CompactSymbolicMaskData.lean`, and `CompactSymbolicMaskFields.lean` are
**uncompiled** preparations. They isolate chosen-dimension geometry, the
generic inequality from `beta+1=B`, and the exact symbolic-mask data and
transport into separate modules. The latter retains definitional equalities
to `CompactSymbolicPorts.lowNat` and `highNat`; no port equality or mask
theorem is claimed until the separated sources are checked on an appropriately
documented provider. See the [field-by-field map](../compact44-packing-obligation-map/README.md)
for the word-dependent conditions and the distinction between the sparse
high-mask target and the full packed product.
