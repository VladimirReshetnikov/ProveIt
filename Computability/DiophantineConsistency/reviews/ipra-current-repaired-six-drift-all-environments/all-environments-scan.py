#!/usr/bin/env python3
"""Conservative graph cross-check, not physical-origin authentication."""
import collections,hashlib,json
from pathlib import Path
R=Path.cwd().resolve();V=R/'Computability/DiophantineConsistency/reviews';D=Path(__file__).resolve().parent
OLD=V/'ipra-current-repaired-survey/manifest.json';NEW=V/'ipra-current-repaired-six-drift-source-survey/manifest.json';PLAN=V/'ipra-frozen-repair-plan-v2/manifest.json';STATE=Path('/tmp/ipra-current-repaired-build-y6kamkla/state.json')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();inputs=[Path(__file__).resolve(),OLD,NEW,PLAN,STATE];before={str(p):H(p) for p in inputs}
s,c,p,b=(json.loads(x.read_text()) for x in (OLD,NEW,PLAN,STATE));assert b['status']=='PASS' and len(b['records'])==258
assert set(s['sources'])==set(c['sources']) and all(s['sources'][n]['imports']==c['sources'][n]['imports'] for n in s['sources'])
rev=collections.defaultdict(set)
for n,x in s['sources'].items():
 for dep in x['imports']:rev[dep].add(n)
for x in b['records']:
 for dep in x['direct_imports']:rev[dep].add(x['name'])
for x in p['origin_nodes'].values():
 for dep in x['project_environment']:rev[dep].add(x['module'])
seed={n for n in s['sources'] if s['sources'][n]['sha256']!=c['sources'][n]['sha256']};imp=set(seed);queue=list(seed)
while queue:
 for owner in rev[queue.pop()]:
  if owner not in imp:imp.add(owner);queue.append(owner)
assert imp<=set(s['sources']) and imp==set(c['order']) and len(seed)==6 and len(imp)==107
assert {str(q):H(q) for q in inputs}==before
out={'status':'PASS_CONSERVATIVE_GRAPH_FIXED_POINT','input_sha256':before,'seed':sorted(seed),'impacted':sorted(imp),'outside_candidate':sorted(imp-set(s['sources'])),'boundary':'Set closure over all recorded historical project environments and actual 258 peer direct inputs. This adds nonselected variants conservatively; it does not itself authenticate physical object origins or prove a replay.'}
path=D/'all-environments-scan-receipt.json'
with path.open('x') as f:json.dump(out,f,sort_keys=True,indent=2);f.write('\n')
print('PASS_CONSERVATIVE_GRAPH_FIXED_POINT',len(seed),len(imp),H(path))
