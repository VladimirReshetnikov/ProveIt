# Scope of the additional syzygy snapshots

The accepted [bounded obstruction](README.md) concerns corrections with
degree(A)≤22 and degree(B)≤26. Its frozen CHECKPOINT manifest and independent
root replay apply to that explicitly listed packet. They establish no
obstruction to higher-degree corrections whose leading terms cancel.

The additional `syzygy_probe.py`, `scaled_layer_probe.py`, `SYZYGY.json`,
`SCALED_LAYERS.json` and preexecution draft archived alongside it are
exploratory snapshots. They were included in commit1c93576246 without being
part of the original bounded-obstruction manifest or its root acceptance.
Their presence does not certify a new degree frontier or a complete circuit.

Subsequent work is separated into
[scaled-norm-syzygy-search](../scaled-norm-syzygy-search/PROPOSAL.md), whose
IMPORTED_SNAPSHOT manifest pins the original exploratory bytes. The new
proposal records the ordinary zero-set proof and a paid degree86 schedule;
its full candidate audit and Lean proof are separate work. None of this
changes the earlier bounded theorem, its files, or its limited quantifiers.
