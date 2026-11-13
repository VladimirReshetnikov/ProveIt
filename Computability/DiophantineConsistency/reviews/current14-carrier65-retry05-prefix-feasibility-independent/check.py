#!/usr/bin/env python3
"""Independently recheck recorded retry05 prefix evidence; no Lean or writes."""
from pathlib import Path
from collections import Counter
import hashlib,json,os,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2];ROOT=D.parents[1]
R=D/'research/current14-coherent-extension-refactor-retry05-runner'
A=R/'attempt01';OUT=Path('/tmp/current14-coherent490-refactor-retry05-20261110')
BASE=Path('/tmp/current14-standard-fresh-build-20261104')
PKG=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
TOOL=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')
S=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash','.so','.dll','.dylib')
cache={}
def digest(path):
 p=Path(path).resolve(strict=True)
 if p not in cache:
  with p.open('rb') as f: cache[p]=hashlib.file_digest(f,'sha256').hexdigest()
 return cache[p]
def pinned(p,h):
 assert digest(p)==h,str(p)
 return json.loads(p.read_bytes())
aud=D/'research/current14-carrier65-retry05-prefix-feasibility'
assert digest(aud/'inspect.py')=='971d616f6216ad3f62ccf0a1084e1b6346a9e1c97e34072d76eb909556046349'
obs=pinned(aud/'observation.json','4d5e69018251752909159818e193b8f64784f51c645941291facd1658b7e292b')
plan=pinned(R/'plan.json','b0006cd71994ebafccbd65a30d41e11cb8d953f52751b2c98f3884df3e63744c')
state=pinned(A/'state.json','8b7d9a84b2bae01871a6417cb1529f85d5e0a35a1ec21a0cac1007dd159dcc82')
outer=pinned(A/'outer-result.json','11e4abc49bceea5a05faaab13d56a1dacdebe4ec5c4b32742633288b657df4a7')
base=pinned(BASE/'state.json','f618a1c0970874ad349ea29b128cd8f775dd6a09036af3a75731e91f7982e014')
assert digest(OUT/'state.json')==digest(A/'state.json')
assert state['status']==outer['status']=='FAILED' and state['failure']==outer['failure']=="Refusal('disk_floor')"
assert base['status']=='PASS' and len(plan['entries'])==529 and len(state['rows'])==240
base_rows={r['module']:r for r in base['records']};assert len(base_rows)==len(state['base_links'])==1000
# Check every recorded selected source and its retained snapshot.
for e in plan['entries']:
 name=e['module']; src=ROOT/e['source']; snap=OUT/'src'/(name.replace('.','/')+'.lean')
 assert digest(src)==digest(snap)==e['source_sha256'],name
client=R/'Current14CoherentAudit.lean'; snapshot=OUT/'src/DiophantineConsistency/Current14CoherentAudit.lean'
assert digest(client)==digest(snapshot)=='b490d50244da4088a3258f290535aceb8b75e89b8cf030277be4cc15e32bf64e'
for path,record in state['base_links'].items():
 p=Path(path);assert p.is_symlink() and str(p.resolve(strict=True))==record['realpath'] and digest(p)==record['sha256']
# Walk stages in recorded order, separately reconstructing the producer map.
producers={}; routes=Counter(); guards={}; outputs=Counter(); logs=0; names=set()
for i in range(239):
 e,row=plan['entries'][i],state['rows'][i];name=e['module'];assert name==row['module']
 assert row['source_sha256']==e['source_sha256']
 assert set(row['dependencies'])-{'Init'}==set(e['imports'])-{'Init'}
 for kind in ('deps','compile'):
  c=row[kind];assert c['exit']==0 and c['stop_reason'] is None and not c['monitor_errors'] and not c['observed_descendant_pids']
  live=Path(c['log']); saved=A/'logs'/live.name
  assert digest(live)==digest(saved)==c['log_sha256']==outer['captured_logs'][saved.name];logs+=1
 expected_paths={str(OUT/'lib'/(name.replace('.','/')+suffix)) for suffix in S}
 assert set(row['output_guard'])==expected_paths
 for path,v in row['output_guard'].items():
  p=Path(path)
  if v is None:assert not os.path.lexists(p);outputs['absent']+=1
  else:
   assert path.endswith('.olean') and p.is_file() and not p.is_symlink()
   assert str(p.resolve(strict=True))==v['realpath'] and digest(p)==v['sha256'];outputs['present']+=1
 obj=OUT/'lib'/(name.replace('.','/')+'.olean');assert digest(obj)==row['object_sha256']
 for dep,info in row['dependencies'].items():
  names.add(dep);path=Path(info['path']);assert path.is_file()
  assert str(path.resolve(strict=True))==info['realpath'] and digest(path)==info['sha256']
  if dep in producers: cat='prefix'; expected=producers[dep]
  elif dep in base_rows: cat='base';expected=base_rows[dep]['object_sha256']
  else: cat='external';assert dep in plan['external_direct'];expected=plan['external_direct'][dep]['sha256']
  assert info['sha256']==expected
  if cat=='prefix': assert info['realpath']==str((OUT/'lib'/(dep.replace('.','/')+'.olean')).resolve(strict=True))
  if cat=='base': assert info['realpath']==str((BASE/'lib'/(dep.replace('.','/')+'.olean')).resolve(strict=True))
  if cat=='external': assert info['realpath']==plan['external_direct'][dep]['realpath']
  choices=[root/(dep.replace('.','/')+'.olean') for root in (OUT/'lib',PKG,TOOL)]
  present=[p for p in choices if p.is_file()];assert present and str(present[0])==info['path']
  routes[cat]+=1
 for path,v in row['direct_guard'].items():
  if path in guards:assert guards[path]==v
  else:guards[path]=v
 producers[name]=row['object_sha256']
counts=Counter()
for path,v in guards.items():
 p=Path(path)
 if v is None:assert not os.path.lexists(p);counts['absent']+=1
 else:assert p.is_file() and str(p.resolve(strict=True))==v['realpath'] and digest(p)==v['sha256'];counts['present']+=1
assert len(producers)==239 and logs==478 and outputs=={'present':239,'absent':2868}
assert routes=={'prefix':325,'base':48,'external':343} and len(names)==310
assert counts=={'present':804,'absent':11286}
stub=state['rows'][239];e=plan['entries'][239]
assert stub['module']==e['module']=='DiophantineConsistency.Sign17KWeightAggregateProbe'
assert not set(stub)&{'deps','compile','object_sha256','output_guard'}
assert not list((OUT/'logs').glob('239-*'))
assert plan['entries'][223]['module']=='DiophantineConsistency.Sign17ExactDegree'
assert set(e['imports'])=={'DiophantineConsistency.Sign17ExactDegree'}
for e2 in plan['entries'][239:]:
 for suffix in S:assert not os.path.lexists(OUT/'lib'/(e2['module'].replace('.','/')+suffix))
for root in (OUT/'lib',PKG,TOOL):
 for suffix in S:assert not os.path.lexists(root/(e['module'].replace('.','/')+suffix))
for suffix in S:assert not os.path.lexists(OUT/'lib'/('DiophantineConsistency/Current14CoherentAudit'+suffix))
cs={}
for dep in sorted(set(e['imports'])|{'Init'}):
 cs[dep]=[]
 for root in (OUT/'lib',PKG,TOOL):
  q=root/(dep.replace('.','/')+'.olean')
  if q.is_file():cs[dep].append({'path':str(q),'realpath':str(q.resolve()),'sha256':digest(q)})
assert cs==obs['stage240_static_import_candidates']
assert obs['recorded_dependency_edges_by_producer']==dict(routes)
assert obs['direct_guard_distinct_counts']=={'direct_distinct_absent':counts['absent'],'direct_distinct_present':counts['present']}
assert obs['completed_stages']==239 and obs['pending_planned_stages']==290
print(json.dumps({'scope':'bounded independent point-in-time recheck of recorded files and routes; no Lean resolution or reuse authorization',
 'planned_source_pairs':529,'completed_objects':239,'archive_live_log_pairs':logs,
 'base_links':1000,'dependency_edges':dict(routes),'output_slots':dict(outputs),
 'direct_guard_slots':dict(counts),'pending_output_slots':290*len(S),
 'stage240_three_root_slots':3*len(S),'stage240_stub_has_no_child':True,
 'stage240_candidate_names':sorted(cs),'audit_output_slots':len(S)},sort_keys=True,indent=2))
