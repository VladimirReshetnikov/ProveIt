#!/usr/bin/env python3
"""Audit the candidate order against every currently recorded project edge."""
from pathlib import Path
import collections,hashlib,json
D=Path(__file__).resolve().parent;V=D.parent;M=D/'manifest.json';F=V/'ipra-frozen-repair-plan-v2/manifest.json';O=V/'ipra-current-repaired-survey/manifest.json';H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();orig=json.loads(O.read_text());states=[Path(x) for x in ('/tmp/ipra-post159-replay-6c04l2wf/state.json','/tmp/ipra-post172-replay-81f0339y/state.json','/tmp/ipra-eleven-drift-replay-sfz0zyj0/state.json','/tmp/ipra-six-drift-replay-42b7hj5k/state.json','/tmp/ipra-current-repaired-build-y6kamkla/state.json')]+[Path(orig['parent'])/'state.json'];inputs=[Path(__file__).resolve(),M,F,O,*states];before={str(p.resolve()):H(p) for p in inputs};m=json.loads(M.read_text());plan=json.loads(F.read_text());order=m['order'];pos={n:i for i,n in enumerate(order)};assert len(pos)==len(order);rev=collections.defaultdict(set)
for own,row in m['sources'].items():
 for dep in row['imports']:rev[dep].add(own)
for p in states:
 state=json.loads(p.read_text());assert state['status']=='PASS'
 for row in state['records']:
  for dep in row['direct_imports']:rev[dep].add(row['name'])
for row in plan['origin_nodes'].values():
 for dep in row['project_environment']:rev[dep].add(row['module'])
edges=[(d,o) for d,owners in rev.items() if d in pos for o in owners if o in pos];bad=[(d,o) for d,o in edges if pos[d]>=pos[o]];assert not bad,bad[:10];assert {str(p.resolve()):H(p) for p in inputs}==before
out={'status':'PASS_RECORDED_EDGE_ORDER','input_sha256':before,'ordered_modules':len(order),'distinct_internal_edges':len(edges),'violations':bad,'scope':'Recorded source/direct-input and retained-origin environment edges only; no physical origin authentication or replay.'};p=D/'recorded-order-receipt.json';assert not p.exists();p.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(out['status'],len(order),len(edges),H(p))
