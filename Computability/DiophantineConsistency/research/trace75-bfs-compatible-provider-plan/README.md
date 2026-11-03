# Proposed BFS-compatible trace75 replay plan

This source-pinned planner follows the previously captured trace75 serialized
headers from the two original fresh seeds and the eight BFS/trace object
differences. It preserves the full 1,931-object BFS baseline. The plan records
31 affected trace75 modules absent from that baseline for rebuilding and four
affected modules already present there. Those four are retained baseline
objects, whose historical source/object ancestry is inherited; matching object
hashes alone do not establish that ancestry. The plan does not run Lean or
prove that its stage list suffices for all later clients.
