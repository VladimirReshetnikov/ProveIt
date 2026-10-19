"""Map decoder states to source-DAG nodes for an inherited-label table + sites file.

For every interior PC prefix p, walk from dispatcher 96 reading the bits of p, as long
as each row writes back the bit read and moves right ("plain" decoder steps). The state
reached implements the node at p. Prefixes whose walk leaves this pattern are "problem"
paths (special decoder routes). Reports per-state node sets: a state serving several
nodes is tag-shared. (Source 103's analyze.py, generalized to any table/source.)
Usage: decoder_map.py TABLE SITES [OUT.json]
"""
import json, sys
from collections import defaultdict
sys.path.insert(0, __file__.rsplit("\\", 1)[0] if "\\" in __file__ else ".")
from dag import DAG, load_sites

T = {}
for line in open(sys.argv[1]):
    if line.strip() and not line.startswith("#"):
        q, b, w, d, z = line.split()
        T[(int(q), int(b))] = (int(w), d, int(z))
d = DAG(load_sites(sys.argv[2]))
prefixes = sorted({p[:i] for p in d.leaf for i in range(len(p))})
qnodes, problem = defaultdict(set), []
for p in prefixes:
    q = 96
    for b in p:
        w, mv, z = T[(q, int(b))]
        if w != int(b) or mv != "R":
            problem.append(p); break
        q = z
    else:
        qnodes[q].add(d.pathnode[p])
shared = {q: sorted(ns) for q, ns in qnodes.items() if len(ns) > 1}
covered = set().union(*qnodes.values())
uncovered = [n for n in d.interior() if n not in covered]
states = {q for q, _ in T}
print(f"interior nodes {len(d.interior())}; decoder states on plain paths {len(qnodes)}; "
      f"tag-shared states {len(shared)}; problem prefixes {len(problem)}; "
      f"interior nodes never reached plainly {len(uncovered)}; table states {len(states)}")
if len(sys.argv) > 3:
    json.dump(dict(qnodes={q: sorted(ns) for q, ns in qnodes.items()}, shared=shared,
                   problem=problem, uncovered=uncovered), open(sys.argv[3], "w"), indent=1)
