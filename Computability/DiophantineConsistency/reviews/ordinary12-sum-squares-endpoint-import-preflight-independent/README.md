# Independent review of the 94-operation endpoint import preflight

The preflight's two captured runs are internally consistent with their
pinned selected-object inventory and retained header output. An independent
breadth-first traversal reproduces all four complete ancestor and outside
lists. In particular, the 736 recorded `SumSquaresModelIff` selected ancestors
include the separately compiled root; every other ancestor belongs to the
1,288-object model union, and none is one of the 425 proposed rebuild modules.
The other three recorded roots also have empty intersections with the 425.
The roots reach names outside the selected-project graph; the top reaches 44.

The checker rehashes the 1,288 selected objects and the separate root object,
compares the 1,252 shared hashes and 36 additional objects with the recorded
inventory, and independently parses all three header logs. Each added object
has exactly one complete header record in each run. The added object tables,
direct imports and root results are identical across both runs. The first
scanner did not explicitly reject repeated object records or require selected
ancestors to be in the model union; the retained first-run logs pass both
additional checks. The revised second scanner checks both properties itself.

Run the independent read-only checks from any working directory:

```
python3 -I -S -B check.py attempt01
python3 -I -S -B check.py attempt02
```

Both exited 0 with empty stderr and identical captured stdout, reproduced in
`observations/`. They pin both result files and the three stdout logs by
SHA-256, check the result's source/input pins, and rehash the selected objects
before and after the graph analysis. They use the temporary absolute object
paths retained in the prior model receipt and require those files to remain
available. The reported resource checks are captured point observations, not
continuous process monitoring.

This is a review of the recorded import graph and captured batch logs, not a
new Lean header-reader execution or independent source-to-object replay. It
inherits the earlier inventory's header data. The 44 outside names are not
recursively traversed; package-transitive and dynamic ancestry, declaration
compatibility after rebuilding, full source-to-object provenance, and the
uncompiled iPRA endpoint remain open. The conclusion concerns serialized
imports, not semantic independence or proof of the proposed endpoint.
