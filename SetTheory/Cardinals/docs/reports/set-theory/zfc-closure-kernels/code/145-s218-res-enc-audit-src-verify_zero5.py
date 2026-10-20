"""Verify the saved source reassociation, independent of the search trajectory."""
from pathlib import Path
import hashlib
import json
from environment import BASE_SOURCE, PACKET, s
p = PACKET / "research/encoding/audit/artifacts/zero5_208.sites.json"
old = json.loads(BASE_SOURCE.read_text())
new = json.loads(p.read_text())
assert [row[1:] for row in old] == [row[1:] for row in new]
oldgraph = s.graph_intervals(old)
assert s.graph_arithmetic(old)[0] == oldgraph
assert s.graph_intervals(new) == s.graph_arithmetic(new)[0] == oldgraph
assert s.metrics(s.tree(new)) == {"dag_nodes":208, "leaf_occurrences":4744,
    "maximum_depth":37, "maximum_zero_run":5}
print(json.dumps({"status":"SAVED_ZERO5_SOURCE_CFG_PASS", "sha256":hashlib.sha256(p.read_bytes()).hexdigest(), "metrics":s.metrics(s.tree(new)), "scope":"Source equivalence only; no 218-state compilation is claimed."}, indent=2))
