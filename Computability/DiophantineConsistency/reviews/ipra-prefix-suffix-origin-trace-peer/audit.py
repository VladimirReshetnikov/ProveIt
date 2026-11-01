#!/usr/bin/env python3
"""Trace physical original project environments for 136 captured historical roots."""
from pathlib import Path
import json,hashlib,collections
D=Path(__file__).resolve().parent;R=D.parents[3];V=R/'Computability/DiophantineConsistency/reviews';G=V/'ipra-adaptive-current-after-atom-plan/manifest.json';F=V/'ipra-adaptive-native-fixed-continuation/manifest.json';CAP=D/'captured-peer-state.json';B=Path('/tmp/ipra-adaptive-native-fixed-continuation-n1l8kvzg');h=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
g=json.loads(G.read_text());f=json.loads(F.read_text());state=json.loads(CAP.read_text());gh=h(G);fh=h(F);cap=h(CAP);ah=h(__file__);assert cap=='a8addd1d7cf90089dbe16e71406ca0e0f325627a17478466fc2ef8d003ac9acb' and state['status']=='RUNNING' and len(state['records'])==139
assert state['manifest_sha256']==fh and state['driver_sha256']==f['driver_sha256']
rev=collections.defaultdict(set)
for n,ds in g['direct_project_imports'].items():
 for d in ds:rev[d].add(n)
cone=set(g['changed_reverse_cone'])|{'DiophantineConsistency.PRAPositiveCode','DiophantineConsistency.PRAPositivePackedNormal'};todo=list(cone)
while todo:
 for d in rev[todo.pop()]-cone:cone.add(d);todo.append(d)
assert len(cone)==247
safe=set(g['source_files'])-cone;prefix=set(f['prefix']+f['second_prefix']+f['third_prefix']+f['fourth_prefix']);compiled={r['name'] for r in state['records']};roots=sorted((prefix|compiled)&safe);assert len(roots)==136 and len(prefix&safe)==71 and len(compiled&safe)==65
affected=set(f['affected']);chosen={k.removesuffix('.olean').replace('/','.'):v for k,v in f['parent_objects'].items() if k.removesuffix('.olean').replace('/','.') not in affected}
for key in ['prefix_records','second_prefix_records','third_prefix_records','fourth_prefix_records']:
 for n,r in f[key].items():chosen[n]=r['object_sha256']
for row in state['records']:chosen[row['name']]=row['object_sha256']
cache={};state_hash={};manifests={};object_hash={};external={'Foundation','Mathlib','Lean','Init','Std','Batteries','Qq','Aesop','Plausible','ProofWidgets','ImportGraph','LeanSearchClient','Lake'}
def obj(p):
 p=str(Path(p).resolve())
 if p not in object_hash:object_hash[p]=h(p)
 return p,object_hash[p]
def getstate(owner):
 if owner==str(B):return state
 if owner not in cache:
  p=Path(owner)/'state.json';assert p.is_file(),str(p);raw=p.read_bytes();state_hash[str(p)]=hashlib.sha256(raw).hexdigest();cache[owner]=json.loads(raw)
 return cache[owner]
def findrow(st,n,sha):
 for row in st.get('records',[]):
  name=row.get('module',row.get('name',''))
  if '.' not in name:name='DiophantineConsistency.'+name
  if name==n and row.get('object_sha256')==sha:return row
 return None
nodes={};selected={};root_nodes={};project=set()
for root in roots:
 stack=[(root,chosen[root],str((B/'lib'/(root.replace('.','/')+'.olean')).resolve()))];vis=set()
 while stack:
  n,sha,path=stack.pop();path,actual=obj(path);key=(n,sha,path)
  if key in vis:continue
  vis.add(key);assert actual==sha,(root,n,path,sha,actual)
  parts=Path(path).parts;assert 'lib' in parts,path;owner='/'+'/'.join(parts[1:parts.index('lib')]);st=getstate(owner);row=findrow(st,n,sha);assert row is not None,(root,n,sha,owner)
  entry={'module':n,'sha256':sha,'physical_path':path,'provider_state':str(Path(owner)/'state.json'),'project_imports':{}}
  if row.get('transitive_manifest'):
   q=Path(owner)/'transitive-manifests'/row['transitive_manifest'];mh=h(q);assert mh==row['transitive_manifest_sha256'];manifests[str(q)]=mh;entry['transitive_manifest']={'path':str(q),'sha256':mh}
   imports={d:{'sha256':v['sha256'],'resolved_path':None} for d,v in json.loads(q.read_text()).items() if v.get('kind')=='project'}
  elif 'direct_imports' in row:imports=row['direct_imports']
  elif 'dependency_hashes' in row:imports={d:{'sha256':v,'resolved_path':str((Path(owner)/'lib'/(d.replace('.','/')+'.olean')).resolve())} for d,v in row['dependency_hashes'].items()}
  else:raise AssertionError((root,n,'missing original dependency record'))
  for dep,v in imports.items():
   if dep.split('.')[0] in external:continue
   project.add(dep);want=v['sha256'];assert chosen.get(dep)==want,(root,n,dep,want,chosen.get(dep))
   selected_path,selected_sha=obj(B/'lib'/(dep.replace('.','/')+'.olean'));assert selected_sha==want,(root,dep,selected_path,want,selected_sha)
   selected[dep]={'sha256':want,'resolved_path':selected_path};entry['project_imports'][dep]={'sha256':want,'recorded_resolved_path':v.get('resolved_path'),'selected_resolved_path':selected_path}
   if v.get('resolved_path'):stack.append((dep,want,v['resolved_path']))
  nodes['|'.join(key)]=entry
 root_nodes[root]=sorted('|'.join(k) for k in vis)
assert len(nodes)==411 and len(project)==389 and len(manifests)==0,(len(nodes),len(project),len(manifests))
# Check the frozen records and all physical project objects a second time.
assert h(G)==gh and h(F)==fh and h(CAP)==cap and h(__file__)==ah
assert all(h(p)==v for p,v in state_hash.items()) and all(h(p)==v for p,v in manifests.items()) and all(h(p)==v for p,v in object_hash.items())
trace={'status':'PASS','scope':'historical five-source graph plus two known stale-object repair roots; captured 139-row peer prefix only; project objects and recorded dependencies only','captured_peer_state_sha256':cap,'graph_sha256':gh,'fixed_manifest_sha256':fh,'audit_sha256':ah,'roots':roots,'root_nodes':root_nodes,'nodes':nodes,'selected_project_dependencies':selected,'provider_state_sha256':state_hash,'ancestor_manifest_sha256':manifests,'physical_project_object_sha256':object_hash,'source_current_boundary':'The current workspace has subsequently changed additional source files; recompute the complete source graph and reverse cone before reuse.','external_boundary':'External/package transitive and dynamic ancestry remain inherited; this trace makes no claim about them.'}
(D/'trace.json').write_text(json.dumps(trace,sort_keys=True,indent=2)+'\n')
receipt={'status':'PASS','captured_peer_state_sha256':cap,'graph_sha256':gh,'fixed_manifest_sha256':fh,'audit_sha256':ah,'trace_sha256':h(D/'trace.json'),'captured_completed_rows':139,'historical_repair_cone':247,'root_count':len(roots),'prefix_root_count':len(prefix&safe),'completed_root_count':len(compiled&safe),'project_node_count':len(nodes),'distinct_project_dependency_count':len(project),'physical_project_object_count':len(object_hash),'provider_state_sha256':state_hash,'ancestor_manifest_count':len(manifests),'mismatch_count':0,'unknown_count':0,'boundary':trace['source_current_boundary']+' '+trace['external_boundary']}
(D/'receipt.json').write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n');print('PASS',len(roots),'roots',len(nodes),'project nodes',len(object_hash),'objects',flush=True)
