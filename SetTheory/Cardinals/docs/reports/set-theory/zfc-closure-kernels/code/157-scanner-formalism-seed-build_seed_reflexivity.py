#!/usr/bin/env python3
"""Rebuild the concrete 79-node certificate using the pinned Hilbert builder.

hilbert.py is an unchanged upstream file. The independent checker imports
neither this builder nor hilbert.py.
"""
from pathlib import Path
import json
import hilbert as h

root = h.eq_refl(h.T)
assert h.validate() and h.form(root) == h.E(h.T, h.T)
keep = set()


def visit(k):
    if k in keep:
        return
    keep.add(k)
    for p in h.nodes[k]["parents"]:
        visit(p)


visit(root)
ids = {k: i for i, k in enumerate(sorted(keep))}
nodes = []
for k in sorted(keep):
    n = h.nodes[k]
    assert not n["open"] and n["rule"] != "hyp"
    nodes.append({"id": ids[k], "rule": n["rule"], "formula": n["formula"],
                  "parents": [ids[p] for p in n["parents"]], "args": n["args"]})
payload = {
    "format": "closed_native_hilbert_v1",
    "theorem": "C222 derives E(0,0), whose literal native code is 3",
    "basis_scope": "K and S are inherited derived schemata of unrestricted native rho8. Other axiom leaves are literal retained native rows.",
    "nodes": nodes,
    "root": ids[root],
}
path = Path(__file__).with_name("seed_reflexivity_proof.json")
path.write_text(json.dumps(payload, separators=(",", ":")) + "\n")
print(json.dumps({"status": "BUILT", "nodes": len(nodes), "path": str(path)}))
