# Preliminary reverse-import survey for the Foundation rebuild

The replacement Foundation object for `Foundation.FirstOrder.Basic.Semantics.Semantics`
has a different SHA-256 from the historical record; see
[the comparison](../foundation-provider-recovery/initial-comparison.json).
For planning only, [`survey.py`](survey.py) follows import edges in the
historical 848-project-node graph and, separately, joins that graph to a
line-based scan of the pinned archived Foundation sources. The project-only
graph reaches 66 project nodes from this single changed object. The combined
source scan reaches 569 project nodes and 121 Foundation nodes; see
[receipt.json](receipt.json) for the node lists and pinned input hashes.

The larger count is an estimate, not a Lean dependency trace: it uses a
line-based import parser and archived source, whose identity with the old
objects' full transitive compile-time sources has not been established. Both
counts omit later endpoint modules and dynamic imports, and neither checks
other changed objects or external package ancestry. They do not establish a
minimum rebuild or compatibility of any reused object. A practical coherent
strategy is to rebuild the authenticated project closure needed by the chosen
endpoint against one new provider, tracing and guarding all declared and
dynamic dependencies; assuming only a few modules need rebuilding would require
separately authenticated historical transitive dependency identities.
