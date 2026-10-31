# Conditional setShift graph replay (provisional parent)

`PRAWitnessSetShiftGraph.wb_setShiftGraph` bounds witnesses in the actual
Foundation `setShiftGraph`, conditional on `WB` for the actual `shiftGraph`.
The check reports exactly `propext`, `Classical.choice`, and `Quot.sound`.

Run from the repository root:

```
python3 Computability/DiophantineConsistency/reviews/pra-setshift-graph-provisional-replay/replay.py
```

The script rebuilds the theorem and check in an isolated directory and guards
the declared current project source closure (191 modules) and its 189 inherited
project objects, plus the direct `ZFCinPA.Instances` object. It checks those
hashes before and after the build. The parent is
`/tmp/pra-setshift-provisional/lib`, which is a mixed historical-provider
overlay. Inherited project objects have **not** been authenticated against
current sources, and the Foundation, ZFCinPA and package ancestry is inherited.
Therefore a pass establishes this conditional suffix only against the frozen
parent; it is not a source-current replay of the whole dependency closure.

The longer exploratory build failed at `PRAHistoryTruncation` because a
history object retained a reference to an old model-pairing constant. That
failure is distinct from the successful conditional graph suffix above.

A second independently launched replay at
`/tmp/pra-setshift-graph-independent-fqruqm8o` passed and matched both
source/object/full-log hashes against the first run. Its state and full logs
are in `independent-evidence/`. The same unauthenticated parent and explicit
`shiftGraph` witness-bound premise remain.
