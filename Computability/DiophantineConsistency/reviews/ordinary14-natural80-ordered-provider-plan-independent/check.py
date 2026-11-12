#!/usr/bin/env python3
"""Independent bounded lexical order, files and collision observations; no Lean."""
from collections import deque
from pathlib import Path
import hashlib,json,os,re
D=Path(__file__).resolve().parents[2];P=D/'research/ordinary14-natural80-ordered-provider-plan'
def sha(data):return hashlib.sha256(data).hexdigest()
def pin(path,digest):
 b=path.read_bytes();assert sha(b)==digest,str(path);return b
plan=json.loads(pin(P/'plan.json','c99e528e09727720dbad410b475ea612e758fc4eb0d705c40ef4da555dac5e54'))
cut=json.loads(pin(D/'research/ordinary14-natural80-qualified-provider-cut/observation.json','c88630304b866b29fe68a11f14f44af210fcd8ea5eed173523ae687c8c157979'))
over=json.loads(pin(D/'research/ordinary14-natural80-combined-slim-overlay/inventory.json','bd10f4c2b320ce1255f57f5bf1e9aefc346d2b2a2b5a8b989547f78f060c2be7'))
rows=plan['candidate_stages'];assert len(rows)==189 and len({r['module'] for r in rows})==189
by={r['module']:r for r in rows};index={r['module']:i for i,r in enumerate(rows)}
assert [r['module'] for r in rows[:5]]==['DiophantineConsistency.DiscreteOrderedRingFacts','DiophantineConsistency.Compact44.FreeJ13','DiophantineConsistency.Compact44.FreeJ13Halt','DiophantineConsistency.BFS943.Direct80IndexOne','DiophantineConsistency.HAExpressionNoZeroEquiv']
assert [r['module'] for r in rows[5:]]==[r['module'] for r in over['drafts_topological']] and rows[-1]['module']=='Natural80Endpoint'
front=plan['selected_project_frontier_objects'];ext=plan['selected_external_cut_objects'];assert len(front)==40 and len(ext)==4
assert front=={n:r['object'] for n,r in cut['selected_project_frontier'].items()} and ext==cut['selected_external']
assert set(front).isdisjoint(ext) and set(front).isdisjoint(by) and set(ext).isdisjoint(by)
# Rehash each point-in-time recorded object and all associated current project source files.
def evidence(p):
 if not os.path.lexists(p):return None
 if not p.is_file():return {'path':str(p),'file':False,'symlink':p.is_symlink()}
 return {'path':str(p),'realpath':str(p.resolve(strict=True)),'sha256':sha(p.read_bytes()),'symlink':p.is_symlink()}
for n,obj in {**front,**ext}.items(): assert evidence(Path(obj['path']))==obj,n
for n,row in cut['selected_project_frontier'].items():pin(D/row['current_source_path'],row['current_source_sha256'])
base=D/'research/ordinary14-natural80-combined-slim-overlay'; overlay={r['module']:r for r in over['drafts_topological']};direct=set()
for r in rows:
 name=r['module'];path=D/r['source'];data=pin(path,r['source_sha256'])
 if r['kind']=='bare-inert-overlay':
  assert name in overlay and path==base/overlay[name]['overlay_path'] and not path.is_symlink()
  assert r['source_sha256']==overlay[name]['overlay_sha256'] and r['unreserved_output_name']==name+'.olean'
 else:
  assert name in cut['source_candidates'] and r['kind']=='qualified-source-candidate'
  assert r['source']==cut['source_candidates'][name]['path'] and r['unreserved_output_name']==name.replace('.','/')+'.olean'
 imports=[]
 for line in data.decode().splitlines():
  if not line.strip():continue
  m=re.fullmatch(r'import\s+([A-Za-z0-9_.]+(?:\s+[A-Za-z0-9_.]+)*)\s*',line)
  if not m:break
  imports+=m.group(1).split()
 assert imports==r['lexical_imports'],name
 for dep in imports:
  assert dep in front or dep in ext or (dep in index and index[dep]<index[name]),(name,dep)
# All source candidates should be in lexical ancestry of the endpoint; frontier is a cut.
queue=deque(['Natural80Endpoint']);seen=set()
while queue:
 n=queue.popleft()
 if n in seen:continue
 seen.add(n);queue.extend(d for d in by[n]['lexical_imports'] if d in by)
assert seen==set(by)
scan=plan['bounded_collision_scan'];assert len(scan['roots'])==8 and len(scan['suffixes'])==13 and scan['names']==189
hits=[]
for name in sorted(by):
 for label,root in scan['roots'].items():
  for suffix in scan['suffixes']:
   p=Path(root)/(name.replace('.','/')+suffix)
   if os.path.lexists(p):hits.append({'root':label,'module':name,'suffix':suffix,'evidence':evidence(p)})
key=lambda r:(r['root'],r['module'],r['suffix'])
assert sorted(hits,key=key)==sorted(scan['hits'],key=key)==sorted(cut['collision_scan']['hits'],key=key)
assert len(hits)==2 and all(x['module']=='DiophantineConsistency.DiscreteOrderedRingFacts' and x['suffix']=='.olean' for x in hits)
print(json.dumps({'scope':'point-in-time lexical source order, selected object hashes and bounded slot observations; no Lean or full provider closure','candidate_stages':len(rows),'candidate_ancestors':len(seen),'qualified_candidates':5,'inert_drafts':184,'project_frontier_objects':len(front),'external_frontier_objects':len(ext),'collision_roots':len(scan['roots']),'collision_suffixes':len(scan['suffixes']),'observed_collisions':len(hits)},sort_keys=True,indent=2))
