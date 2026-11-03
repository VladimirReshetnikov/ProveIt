# Selected project objects: serialized-import reverse impact

`scan.py` read the direct imports serialized in every object of the selected
compact-first overlay plus the 59 historical nine-provider objects omitted
from that overlay. The bounded author run covered 2,616 object headers in
164 batches and exited 0. The exact per-batch output, commands and recorded
object paths/hashes are retained under `observations/attempt01/`. The helper,
selected overlay files and 59 historical omitted files matched the recorded
hashes before and after scanning. The manifest and prior endpoint source scan
were pinned. All direct imports not present in the selected graph resolved to
the recorded package or Lean toolchain root; this does not inspect their own
transitive or dynamic imports.

Following reverse edges from all 100 byte-conflicting compact/nine object
names finds 2,100 affected selected-or-omitted objects, including 810 selected
from the nine provider and all 59 originally omitted. An affected object is
one with a serialized-import path to a conflict; that does not assert the
objects are semantically inconsistent, but their coherent reuse needs a
separate source/object or dependency argument. In particular, the 59-module
`DiophantineConsistency.*`-only analysis did not capture these cross-namespace
paths and is not a complete integration rebuild cone.

The separate `compact12-ipra-expanded-cone-preflight` packet computes the
actual native endpoint ancestry, a proposed topological rebuild list and the
impact on the exploratory first 15 rebuilds. This scan does not authenticate
source-to-object origins, package or dynamic ancestry, or a final iPRA proof;
it is a single-author, point-in-time observation, not a paired replay.

`scan.py` SHA-256 `93285f578950003f69985b8d52de22696a83a3dbe1f350907a9b6cc291cf1d7e`;
`ReadObjectImports.lean` SHA-256 `886d46d27a94d512e47c4fe571654e4a432ab536f995b52bd1300324678fc10f`;
`observations/attempt01/result.json` SHA-256 `bf812db57d68117d47d3df792e4a0d6879019d442c4f0f2b0fbef8b861f363f2`.
