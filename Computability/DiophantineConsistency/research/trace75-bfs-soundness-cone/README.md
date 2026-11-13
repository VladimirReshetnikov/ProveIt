# Captured BFS80 soundness dependency cone

`scan.py` traverses the previously captured serialized project-header graph
from `DirectBFS80ModelHalt` and computes the reverse cone of the two existing
graph-specific inputs `DirectBFS80Carry` and `Direct80FixedSlots`. The
capture has 739 project ancestors of the halt root and 21 objects in this
reverse cone, including both seeds and the halt endpoint. The result records
each affected object's captured direct imports and object hash.

`observations/attempt01/result.json` SHA-256
`e2d2aa8fd88852c79ad25a8348e7230e81bffea984be0272fb418f08b40d33e2`.
This is an adaptation inventory based on the historical BFS80 header graph;
it does not prove that an analogous trace75 client compiles, that the
dependencies are mathematically minimal, or that the reverse/completeness,
iPRA, external coefficient or PDF binding is complete.
