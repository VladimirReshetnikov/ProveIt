#!/usr/bin/env python3
"""Reconstruct the exact two-row fold pair families used by the audit."""
from invariant_search import *

I={int(q):set(xs)for q,xs in json.loads(Path('invariant_r5.json').read_text()).items()}
nonpure={q for q in Q if any(T[q,c][:2]!=(c,1)for c in(0,1))}
for filename,eligible,want in [('disjoint_pairs.json',ENGINE,1806),
                               ('disjoint_nonpure_pairs.json',nonpure,4146)]:
    pairs=[]
    for a,b in itertools.combinations(Q,2):
        phi=lambda q:a if q==b else q
        if not {a,b}&eligible or I[a]&I[b]:continue
        if all((*T[a,c][:2],phi(T[a,c][2]))!=(*T[b,c][:2],phi(T[b,c][2]))for c in(0,1)):
            pairs.append([a,b])
    assert len(pairs)==want
    Path(filename).write_text(json.dumps(pairs)+'\n')
    print(filename,len(pairs))
