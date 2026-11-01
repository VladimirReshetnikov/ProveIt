#!/usr/bin/env python3
"""Prepare a 14-variable fixed-snapshot replay only after both 13-variable parents PASS."""
from pathlib import Path
import hashlib,json,os,sys
D=Path(__file__).resolve().parent;R=D.parents[3];V=R/'Computability/DiophantineConsistency/reviews';G=V/'ipra-current-native14-frozen-graph/manifest.json';E=V/'ipra-current-native14-frozen-extra/manifest.json';F=V/'ipra-adaptive-native-fixed-continuation/manifest.json';A=Path('/tmp/ipra-adaptive-native-fixed-continuation-8mckr1yj');B=Path('/tmp/ipra-adaptive-native-fixed-continuation-n1l8kvzg');OUT=V/'ipra-current-native14-fixed-replay';OUT.mkdir(exist_ok=True)
h=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read_and_hash(p):
 raw=Path(p).read_bytes();return json.loads(raw),hashlib.sha256(raw).hexdigest()
g,gh=read_and_hash(G);e,eh=read_and_hash(E);f,fh=read_and_hash(F);a,ah=read_and_hash(A/'state.json');b,bh=read_and_hash(B/'state.json');assert a['status']==b['status']=='PASS';assert a['manifest_sha256']==b['manifest_sha256']==fh;assert a['driver_sha256']==b['driver_sha256']==f['driver_sha256'];assert len(a['records'])==len(b['records'])==len(f['order']);assert [r['name'] for r in a['records']]==[r['name'] for r in b['records']]==f['order']
for x,y in zip(a['records'],b['records']):
 assert all(x.get(k)==y.get(k) for k in ['name','exit','object_sha256','log_sha256','warnings']) and x['exit']==0
 assert {n:v['sha256'] for n,v in x['direct_imports'].items()}=={n:v['sha256'] for n,v in y['direct_imports'].items()}
 for root,row in [(A,x),(B,y)]:
  n=row['name'];assert h(root/'lib'/(n.replace('.','/')+'.olean'))==row['object_sha256'] and h(root/'logs'/(n.replace('.','_')+'.log'))==row['log_sha256'];assert all(h(v['resolved_path'])==v['sha256'] for v in row['direct_imports'].values())
assert h(F)==g['fixed_manifest_sha256'] and h(E)==g['extra_manifest_sha256'];snap=V/'ipra-adaptive-fixed-snapshot-prefix/sources';extra=V/'ipra-current-native14-frozen-extra/sources';sp=lambda n:(extra if n in e['sources'] else snap)/(n.replace('.','/')+'.lean');assert all(h(sp(n))==v for n,v in g['project_source_sha256'].items())
base=Path('/tmp/ipra-bounded-induction-postmerge-wgkld2w0');excluded={n.replace('.','/')+'.olean' for n in f['affected']}
assert h(base/'state.json')==f['parent_state_sha256'];assert all(h(base/'lib'/rel)==v and (rel in excluded or h(B/'lib'/rel)==v) for rel,v in f['parent_objects'].items())
for path,key in [(Path('/tmp/ipra-adaptive-native-current-qpk97_3z'),'prefix_records'),(Path('/tmp/ipra-adaptive-native-continuation-l58un8d6'),'second_prefix_records'),(Path('/tmp/ipra-adaptive-native-warning-continuation-x2wbh2da'),'third_prefix_records'),(Path('/tmp/ipra-adaptive-native-second-continuation-8ziag05a'),'fourth_prefix_records')]:
 for n,row in f[key].items():
  assert h(B/'lib'/(n.replace('.','/')+'.olean'))==row['object_sha256'] and h(path/'lib'/(n.replace('.','/')+'.olean'))==row['object_sha256'] and h(path/'logs'/(n.replace('.','_')+'.log'))==row['log_sha256'];assert all(h(v['resolved_path'])==v['sha256'] for v in row['direct_imports'].values())
ancestor=Path('/tmp/pra14-full-transitive-2x6o__to');ancestor_state,ancestor_state_hash=read_and_hash(ancestor/'state.json');anc_records={r['module']:r for r in ancestor_state['records']};ancestral_manifests={};ancestral_project=set()
for n,row in g['five_base_checks'].items():
 assert h(B/'lib'/(n.replace('.','/')+'.olean'))==row['selected_base_object_sha256'];record=anc_records[n];path=ancestor/'transitive-manifests'/record['transitive_manifest'];manifest,manifest_hash=read_and_hash(path);assert manifest_hash==record['transitive_manifest_sha256'];ancestral_manifests[str(path)]=manifest_hash
 for dep,item in manifest.items():
  if item['kind']=='project':
   assert dep not in f['affected'] and h(B/'lib'/(dep.replace('.','/')+'.olean'))==item['sha256'];assert dep in g['project_source_sha256'] and g['project_source_sha256'][dep]==anc_records[dep]['source_sha256'];ancestral_project.add(dep)
inv={}
for d,_,fs in os.walk(B/'lib',followlinks=True):
 for name in fs:
  if name.endswith(('.olean','.olean.private','.olean.server','.ir')):
   p=Path(d)/name;inv[str(p.relative_to(B/'lib'))]={'sha256':h(p),'resolved_path':str(p.resolve())}
# Bind the later inventory to the exact passed rows, prefix records and base hashes.
for row in b['records']:
 rel=row['name'].replace('.','/')+'.olean';assert inv[rel]['sha256']==row['object_sha256']
for key in ['prefix_records','second_prefix_records','third_prefix_records','fourth_prefix_records']:
 for n,row in f[key].items():assert inv[n.replace('.','/')+'.olean']['sha256']==row['object_sha256']
for rel,v in f['parent_objects'].items():
 if rel not in excluded:assert inv[rel]['sha256']==v
assert h(A/'state.json')==ah and h(B/'state.json')==bh and h(F)==fh and h(G)==gh and h(E)==eh
assert all(h(sp(n))==v for n,v in g['project_source_sha256'].items())
assert h(ancestor/'state.json')==ancestor_state_hash and all(h(path)==v for path,v in ancestral_manifests.items())
order=['DiophantineConsistency.HACurrentPolynomialBridge2011','DiophantineConsistency.HACurrentEquation2011','DiophantineConsistency.PRACurrentZFCStrict','DiophantineConsistency.IPRACurrentTranslatedRefutation','DiophantineConsistency.IPRACurrentNativeZFC','DiophantineConsistency.IPRACurrentNativeZFCChecks']
manifest={'author':str(A),'peer':str(B),'author_state_sha256':ah,'peer_state_sha256':bh,'frozen_13_manifest_sha256':fh,'graph_sha256':gh,'extra_manifest_sha256':eh,'parent_inventory':inv,'order':order,'source_sha256':g['project_source_sha256'],'extra_names':list(e['sources']),'direct_imports':{n:g['project_dependencies'][n] for n in order},'external_direct':f['external_direct'],'lean_sha256':f['lean_sha256'],'ancestor_state':str(ancestor/'state.json'),'ancestor_state_sha256':ancestor_state_hash,'ancestral_manifests':ancestral_manifests,'ancestral_project_count':len(ancestral_project),'boundary':'Fixed historical snapshot; 848 ancestor author-only; package-transitive and dynamic ancestry inherited. Exact 13-variable independent peers must PASS first.'}
replay=(D/'replay.py').read_bytes();(OUT/'replay.py').write_bytes(replay);manifest['driver_sha256']=hashlib.sha256(replay).hexdigest();(OUT/'manifest.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n');print('DRIVER',manifest['driver_sha256'],'MANIFEST',h(OUT/'manifest.json'),'PARENT_OBJECT_FILES',len(inv))
