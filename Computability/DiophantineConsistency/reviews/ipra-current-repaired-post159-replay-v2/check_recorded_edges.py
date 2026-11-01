#!/usr/bin/env python3
"""Recount frozen recorded dependency occurrences and distinct ordered pairs."""
from pathlib import Path
import hashlib,json
D=Path(__file__).resolve().parent;V=D.parent;M=D/'manifest.json';H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();mh=H(M);sh=H(__file__);m=json.loads(M.read_text());S=Path(m['candidate_survey_path']);F=V/'ipra-frozen-repair-plan-v2/manifest.json';orig=V/'ipra-current-repaired-survey/manifest.json';s=json.loads(S.read_text());plan=json.loads(F.read_text());o=json.loads(orig.read_text());states=[Path(x) for x in ['/tmp/ipra-post172-replay-81f0339y/state.json','/tmp/ipra-eleven-drift-replay-sfz0zyj0/state.json','/tmp/ipra-six-drift-replay-42b7hj5k/state.json','/tmp/ipra-current-repaired-build-y6kamkla/state.json']]+[Path(o['parent'])/'state.json'];inputs=[M,S,F,orig,*states,Path(__file__).resolve()];before={str(p.resolve()):H(p) for p in inputs};order=s['order'];positions={n:i for i,n in enumerate(order)};counts={};pairs=[]
def record(name,edges):
 edges=[(dep,owner) for dep,owner in edges if dep in positions and owner in positions]
 assert all(positions[d]<positions[o] for d,o in edges),name
 counts[name]=len(edges);pairs.extend(edges)
record('current_source',((dep,owner) for owner,row in s['sources'].items() for dep in row['imports']))
for p in states:
 x=json.loads(p.read_text());assert x['status']=='PASS';record(str(p),((dep,row['name']) for row in x['records'] for dep in row['direct_imports']))
record('retained_origin_environments',((dep,row['module']) for row in plan['origin_nodes'].values() for dep in row['project_environment']))
assert len(set(pairs))==m['recorded_order_edges']==3042 and len(pairs)==3742
assert {str(p.resolve()):H(p) for p in inputs}==before and H(M)==mh and H(__file__)==sh
out={'status':'PASS_RECORDED_EDGE_ORDER','input_sha256':before,'occurrences_by_origin':counts,'total_occurrences':len(pairs),'distinct_pairs':len(set(pairs)),'scope':'Checks recorded internal edges only; not a proof replay.'};p=D/'recorded-edge-order-receipt.json';assert not p.exists();p.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(out['status'],out['total_occurrences'],out['distinct_pairs'],H(p))
