#!/usr/bin/env python3
"""Independent BFS and bounded object-slot review; never invoke Lean."""
import hashlib,json,os,re,sys
from collections import deque
from pathlib import Path
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):raise SystemExit('Use python3 -I -S -B')
D=Path(__file__).resolve().parents[2];ROOT=D.parents[1];R=D/'research';O=R/'ordinary14-natural79-combined-slim-overlay';P=R/'ordinary14-natural79-qualified-provider-cut'
P72=Path('/tmp/p72-current-base-extension-attempt02-20261105');BASE=Path('/tmp/current14-standard-fresh-build-20261104');PKG=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(path,digest):
 raw=path.read_bytes();assert sha(raw)==digest,(str(path),sha(raw));return raw
obs=json.loads(pin(P/'observation.json','c978df77d6a2c68947f827a31e45ede8070b5b76cd26c7eab2306811d6b2610c'))
pin(P/'inspect.py','8b14b6edf791236fb20ffede9e88db93a2316bc7a6bfa7e38e26b363fd2af81e')
inv=json.loads(pin(O/'inventory.json','7f8f722c1a96194dc453a797a2ffafbcfea614b2c8c83fda9a51daefb0558483'))
old=json.loads(pin(R/'ordinary14-natural80-qualified-provider-cut/observation.json','c88630304b866b29fe68a11f14f44af210fcd8ea5eed173523ae687c8c157979'))
progress=json.loads(pin(P72/'progress.json','f4bbe5f0b543497d543f243e10d8ead6d778cc3d0bf0aec96dfa73f7e622dd5a'))
snapshot=json.loads(pin(P72/'source-snapshot.json','4536c44c399dc42037b692a39a36cc74c807693e1e5a76e2f5db299691fff7d8'))
base=json.loads(pin(BASE/'state.json','f618a1c0970874ad349ea29b128cd8f775dd6a09036af3a75731e91f7982e014'))
assert progress['status']==base['status']=='PASS'
records={r['module']:r for r in base['records']}
def observation(p):
 if not os.path.lexists(p):return None
 if not p.is_file():return {'path':str(p),'file':False,'symlink':p.is_symlink()}
 return {'path':str(p),'realpath':str(p.resolve(strict=True)),'sha256':sha(p.read_bytes()),'symlink':p.is_symlink()}
def obj(root,n):return root/(n.replace('.','/')+'.olean')
def imports(raw):
 out=[]
 for t in raw.decode().splitlines():
  t=t.strip()
  if not t:continue
  if not t.startswith('import '):break
  assert re.fullmatch(r'import\s+[A-Za-z0-9_.]+(?:\s+[A-Za-z0-9_.]+)*',t),t
  out.extend(t.split()[1:])
 return out
q={r['module']:r for r in inv['qualified_direct_sources']};ext={r['module']:r for r in inv['external_direct_sources']};assert len(q)==42 and len(ext)==2
front_seeds=set()
for row in inv['drafts_topological']:
 path=O/row['overlay_path'];assert path.is_file() and not path.is_symlink();raw=pin(path,row['overlay_sha256'])
 imps=imports(raw);assert [x for x in imps if '.' not in x]==row['bare_imports'] and [x for x in imps if '.' in x]==row['qualified_imports']
 front_seeds.update(x for x in imps if '.' in x)
assert len(inv['drafts_topological'])==195 and front_seeds==set(q)|set(ext) and len(front_seeds)==44
for n,row in q.items():assert row['path']=='Lean/'+n.replace('.','/')+'.lean' and sha((D/row['path']).read_bytes())==row['sha256']
for n,row in ext.items():assert row['path']=='.lake/packages/mathlib/'+n.replace('.','/')+'.lean' and sha((ROOT/row['path']).read_bytes())==row['sha256']
queue=deque(sorted(front_seeds));seen=set();missing={};front={};external={}
while queue:
 n=queue.popleft()
 if n in seen:continue
 seen.add(n)
 if not n.startswith('DiophantineConsistency.'):
  external[n]=observation(obj(PKG,n));continue
 src=D/'Lean'/(n.replace('.','/')+'.lean');raw=src.read_bytes();sourcehash=sha(raw);o=obj(P72/'lib',n)
 if o.is_file():
  assert snapshot.get(n)==sourcehash or records.get(n,{}).get('source_sha256')==sourcehash,n
  if n in records:assert records[n]['object_sha256']==sha(o.read_bytes())
  front[n]={'object':observation(o),'current_source_path':str(src.relative_to(D)),'current_source_sha256':sourcehash,
   'p72_snapshot_source_sha256':snapshot.get(n),'base_record_source_sha256':records.get(n,{}).get('source_sha256'),
   'base_record_object_sha256':records.get(n,{}).get('object_sha256')}
 else:
  deps=imports(raw);missing[n]={'path':str(src.relative_to(D)),'sha256':sourcehash,'lexical_imports':deps};queue.extend(deps)
assert missing==obs['source_candidates'] and front==obs['selected_project_frontier'] and external==obs['selected_external']
assert len(missing)==44 and len(front)==46 and len(external)==5 and all(external.values()) and obs['missing_external_objects']==[]
for field,now,oldfield in [('source_candidates',set(missing),'source_candidates'),('project_frontier',set(front),'selected_project_frontier'),('external',set(external),'selected_external')]:
 prev=set(old[oldfield]);assert sorted(now-prev)==obs['additional_'+field+'_vs_natural80'];assert sorted(prev-now)==obs['omitted_'+field+'_vs_natural80']
assert len(obs['additional_source_candidates_vs_natural80'])==39 and len(obs['additional_project_frontier_vs_natural80'])==6
assert obs['additional_external_vs_natural80']==['Mathlib.Algebra.Ring.Basic']
scan=obs['collision_scan']; names=sorted({r['module'] for r in inv['drafts_topological']}|set(missing));assert len(names)==239==scan['names']
assert len(scan['roots'])==8 and len(scan['suffixes'])==13
hits=[]
for label,root in scan['roots'].items():
 for name in names:
  for suff in scan['suffixes']:
   p=Path(root)/(name.replace('.','/')+suff)
   if os.path.lexists(p):hits.append({'root':label,'module':name,'suffix':suff,'evidence':observation(p)})
key=lambda r:(r['root'],r['module'],r['suffix'])
assert sorted(hits,key=key)==sorted(scan['hits'],key=key) and len(hits)==6
assert {x['module'].rsplit('.',1)[-1] for x in hits}=={'ArithmeticPellPigeonhole','DiscreteOrderedRingFacts','ModelProductPell'}
assert all(x['suffix']=='.olean' and x['root'] in ('captured_p72_endpoint','carrier_retry05') for x in hits)
print(json.dumps({'scope':'bounded independent BFS source/presence and selected-root collision observation; no Lean or provider closure',
 'overlay_snapshots':len(inv['drafts_topological']),'direct_qualified_names':len(front_seeds),
 'missing_project_objects_with_source':len(missing),'selected_project_objects':len(front),'selected_external_objects':len(external),
 'new_source_candidates_vs_natural80':39,'new_project_frontier_vs_natural80':6,'candidate_output_names':len(names),
 'collision_roots':len(scan['roots']),'suffixes':len(scan['suffixes']),'observed_hits':len(hits)},sort_keys=True,indent=2))
