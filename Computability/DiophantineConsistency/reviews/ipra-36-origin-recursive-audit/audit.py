#!/usr/bin/env python3
"""Trace actual original physical project-object environments."""
from pathlib import Path
import hashlib,json
D=Path(__file__).resolve().parent;R=D.parents[3];V=R/'Computability/DiophantineConsistency/reviews';F=V/'ipra-adaptive-native-fixed-continuation/manifest.json';G=V/'ipra-adaptive-current-after-atom-plan/manifest.json';OLD=V/'ipra-inherited-object-ancestry-audit/receipt.json';P41=Path('/tmp/ipra-bounded-induction-postmerge-wgkld2w0');P94=Path('/tmp/ipra-bounded-induction-rebase-companions-p8ekt8vt');P848=Path('/tmp/pra14-full-transitive-2x6o__to');M41=V/'ipra-bounded-induction-postmerge-replay/manifest.json';M94=V/'ipra-bounded-induction-rebase-companions/manifest.json';h=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();read=lambda p:json.loads(Path(p).read_text());f=read(F);g=read(G);old=read(OLD);s41=read(P41/'state.json');s94=read(P94/'state.json');s848=read(P848/'state.json');assert s41['status']==s94['status']=='PASS';inputs={str(p):h(p) for p in [F,G,OLD,P41/'state.json',P94/'state.json',P848/'state.json',M41,M94,Path(__file__)]};assert inputs[str(F)]==old['fixed_manifest_sha256'] and inputs[str(G)]==old['historical_graph_sha256'] and inputs[str(P848/'state.json')]==old['ancestor_state_sha256'];assert s41['manifest_sha256']==inputs[str(M41)] and s94['manifest_sha256']==inputs[str(M94)]
selected={rel.removesuffix('.olean').replace('/','.'):{'sha256':v,'path':str((P41/'lib'/rel).resolve())} for rel,v in f['parent_objects'].items()}
for path,key in [(Path('/tmp/ipra-adaptive-native-current-qpk97_3z'),'prefix_records'),(Path('/tmp/ipra-adaptive-native-continuation-l58un8d6'),'second_prefix_records'),(Path('/tmp/ipra-adaptive-native-warning-continuation-x2wbh2da'),'third_prefix_records'),(Path('/tmp/ipra-adaptive-native-second-continuation-8ziag05a'),'fourth_prefix_records')]:
 for n,row in f[key].items():selected[n]={'sha256':row['object_sha256'],'path':str((path/'lib'/(n.replace('.','/')+'.olean')).resolve())}
records={}
for label,state,provider in [('41',s41,P41),('94',s94,P94)]:
 for row in state['records']:
  n='DiophantineConsistency.'+row['name'];path=str((provider/'lib'/(n.replace('.','/')+'.olean')).resolve());records[(n,row['object_sha256'],path)]=(label,row)
ancestor={(row['module'],row['object_sha256']):row for row in s848['records']}
roots=old['different_from_ancestor']+old['without_ancestor_manifest'];assert len(roots)==36;todo=[(n,selected[n]['sha256'],selected[n]['path']) for n in roots];seen={};manifest_files={};selected_seen={};original_seen={};external=[];ns={'Foundation','Mathlib','Lean','Init','Std','Batteries','Qq','Aesop','Plausible','ProofWidgets','ImportGraph','LeanSearchClient','Lake'}
def check_cached(p,v,d):
 if p not in d:assert h(p)==v;d[p]=v
 else:assert d[p]==v
def selected_check(n,v):
 assert n in selected,(n,'not selected');assert selected[n]['sha256']==v,(n,selected[n]['sha256'],v);check_cached(selected[n]['path'],v,selected_seen)
while todo:
 n,sha,path=todo.pop();path=str(Path(path).resolve());key=(n,sha,path)
 if key in seen:continue
 selected_check(n,sha);check_cached(path,sha,original_seen)
 if key in records:label,row=records[key]
 else:
  assert (n,sha) in ancestor,('unrecorded original project object',key);label,row='848',ancestor[(n,sha)]
  assert str((P848/'lib'/(n.replace('.','/')+'.olean')).resolve())==path,('ancestor physical origin mismatch',key)
 edges={}
 if label in ['41','94']:
  for dep,x in row['direct_imports'].items():
   if dep.split('.')[0] in ns:external.append({'module':dep,'observed_by':n,**x})
   else:edges[dep]={'sha256':x['sha256'],'original_path':str(Path(x['resolved_path']).resolve())}
 elif row.get('transitive_manifest'):
  path2=P848/'transitive-manifests'/row['transitive_manifest'];assert h(path2)==row['transitive_manifest_sha256'];manifest_files[str(path2)]=h(path2)
  for dep,x in read(path2).items():
   if x['kind']=='project':selected_check(dep,x['sha256'])
 else:
  for dep,v in row['dependency_hashes'].items():
   if dep.split('.')[0] not in ns:edges[dep]={'sha256':v,'original_path':str((P848/'lib'/(dep.replace('.','/')+'.olean')).resolve())}
 for dep,x in edges.items():selected_check(dep,x['sha256']);todo.append((dep,x['sha256'],x['original_path']))
 seen[key]={'provider':label,'module':n,'object_sha256':sha,'original_path':path,'project_edges':edges,'transitive_manifest':row.get('transitive_manifest')}
assert len(roots)==36 and len(seen)==50 and len(manifest_files)==14,(len(roots),len(seen),len(manifest_files))
assert all(h(p)==v for p,v in inputs.items()) and all(h(p)==v for p,v in manifest_files.items()) and all(h(p)==v for p,v in selected_seen.items()) and all(h(p)==v for p,v in original_seen.items()) and all(h(x['resolved_path'])==x['sha256'] for x in external)
receipt={'status':'PROJECT_ENVIRONMENTS_MATCH','inputs':inputs,'roots':roots,'records':list(seen.values()),'selected_project_objects':selected_seen,'original_project_objects':original_seen,'transitive_manifest_hashes':manifest_files,'external_direct_observations':external,'boundary':'Historical 41/94/848 provider project environments only; 848 author-only and all package-transitive/dynamic ancestry remain inherited. Separate two ancestor-identical stale users remain unresolved.'};(D/'receipt.json').write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n');print('PASS roots',len(roots),'records',len(seen),'selected projects',len(selected_seen),'manifests',len(manifest_files))
