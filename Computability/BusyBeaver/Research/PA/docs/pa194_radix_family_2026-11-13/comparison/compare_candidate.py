#!/usr/bin/env python3
"""Exact candidate comparison against the recognized pinned table corpus."""
import argparse,json,hashlib
from pathlib import Path
from census import parse,canonical,digest

ap=argparse.ArgumentParser()
ap.add_argument('candidate',type=Path)
ap.add_argument('--census',type=Path,default=Path(__file__).with_name('census.json'))
ap.add_argument('--output',type=Path)
a=ap.parse_args()
data=a.candidate.read_bytes();p=parse(data)
assert p is not None,'Not a recognized complete numeric binary table'
t,states,halt=p
graph,spanning=canonical(t,states,halt)
assert graph is not None,'No spanning root; this comparison is inapplicable'
c=json.loads(a.census.read_text());matched=[]
for sha,v in c['forms'].items():
    if v['states']==len(states) and v['graph_digest']==graph:
        matched.append({'sha256':sha,'first_path':v['first_path']})
out={'candidate':str(a.candidate),'sha256':hashlib.sha256(data).hexdigest(),
     'states':len(states),'rows':len(t),'halt':halt,'spanning_roots':spanning,
     'root_reflection_complement_graph_digest':graph,'matches':matched,
     'graph_absent_from_census':not bool(matched),
     'scope':'Exact action-graph comparison under arbitrary state renaming and root choice, L/R reflection, global read/write-bit complementation; not a semantic consistency proof'}
if a.output:a.output.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
