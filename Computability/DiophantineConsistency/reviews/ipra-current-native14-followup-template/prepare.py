#!/usr/bin/env python3
"""Prepare a 14-variable fixed-snapshot replay only after both 13-variable parents PASS."""
from pathlib import Path
import hashlib,json,os,sys
D=Path(__file__).resolve().parent;R=D.parents[3];V=R/'Computability/DiophantineConsistency/reviews';G=V/'ipra-current-native14-frozen-graph/manifest.json';E=V/'ipra-current-native14-frozen-extra/manifest.json';F=V/'ipra-adaptive-native-fixed-continuation/manifest.json';A=Path('/tmp/ipra-adaptive-native-fixed-continuation-8mckr1yj');B=Path('/tmp/ipra-adaptive-native-fixed-continuation-n1l8kvzg');OUT=V/'ipra-current-native14-fixed-replay';OUT.mkdir(exist_ok=True)
h=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();g=json.loads(G.read_text());e=json.loads(E.read_text());f=json.loads(F.read_text());a=json.loads((A/'state.json').read_text());b=json.loads((B/'state.json').read_text());assert a['status']==b['status']=='PASS';assert a['manifest_sha256']==b['manifest_sha256']==h(F);assert len(a['records'])==len(b['records'])==len(f['order'])
for x,y in zip(a['records'],b['records']):
 assert all(x.get(k)==y.get(k) for k in ['name','exit','object_sha256','log_sha256','warnings']) and x['exit']==0
 assert {n:v['sha256'] for n,v in x['direct_imports'].items()}=={n:v['sha256'] for n,v in y['direct_imports'].items()}
assert h(F)==g['fixed_manifest_sha256'] and h(E)==g['extra_manifest_sha256'];snap=V/'ipra-adaptive-fixed-snapshot-prefix/sources';extra=V/'ipra-current-native14-frozen-extra/sources';sp=lambda n:(extra if n in e['sources'] else snap)/(n.replace('.','/')+'.lean');assert all(h(sp(n))==v for n,v in g['project_source_sha256'].items())
for n,row in g['five_base_checks'].items():assert h(B/'lib'/(n.replace('.','/')+'.olean'))==row['selected_base_object_sha256']
inv={}
for d,_,fs in os.walk(B/'lib',followlinks=True):
 for name in fs:
  if name.endswith(('.olean','.olean.private','.olean.server','.ir')):
   p=Path(d)/name;inv[str(p.relative_to(B/'lib'))]={'sha256':h(p),'resolved_path':str(p.resolve())}
order=['DiophantineConsistency.HACurrentPolynomialBridge2011','DiophantineConsistency.HACurrentEquation2011','DiophantineConsistency.PRACurrentZFCStrict','DiophantineConsistency.IPRACurrentTranslatedRefutation','DiophantineConsistency.IPRACurrentNativeZFC','DiophantineConsistency.IPRACurrentNativeZFCChecks']
manifest={'author':str(A),'peer':str(B),'author_state_sha256':h(A/'state.json'),'peer_state_sha256':h(B/'state.json'),'frozen_13_manifest_sha256':h(F),'graph_sha256':h(G),'extra_manifest_sha256':h(E),'parent_inventory':inv,'order':order,'source_sha256':g['project_source_sha256'],'extra_names':list(e['sources']),'direct_imports':{n:g['project_dependencies'][n] for n in order},'external_direct':f['external_direct'],'lean_sha256':f['lean_sha256'],'boundary':'Fixed historical snapshot; 848 ancestor author-only; package-transitive and dynamic ancestry inherited. Exact 13-variable independent peers must PASS first.'}
replay=(D/'replay.py').read_bytes();(OUT/'replay.py').write_bytes(replay);manifest['driver_sha256']=hashlib.sha256(replay).hexdigest();(OUT/'manifest.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n');print('DRIVER',manifest['driver_sha256'],'MANIFEST',h(OUT/'manifest.json'),'PARENT_OBJECT_FILES',len(inv))
