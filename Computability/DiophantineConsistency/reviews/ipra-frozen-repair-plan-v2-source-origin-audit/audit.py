#!/usr/bin/env python3
"""Independently bind every retained node to its physical provider's source record."""
from pathlib import Path
import hashlib,json
D=Path(__file__).resolve().parent;R=D.parents[3];V=R/'Computability/DiophantineConsistency/reviews';M=V/'ipra-frozen-repair-plan-v2/manifest.json';F=V/'ipra-adaptive-native-fixed-continuation/manifest.json';h=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):
 raw=Path(p).read_bytes();return json.loads(raw),hashlib.sha256(raw).hexdigest()
m,mh=read(M);f,fh=read(F);ah=h(__file__);assert m['fixed_manifest_sha256']==fh and m['source_sha256']==f['source_sha256'];guard=m['origin_guard'];cache={};checked={};rows_out={}
def pin(p,expected):
 p=Path(p);k=str(p.resolve());assert guard.get(k)==expected,(k,guard.get(k),expected);assert h(p)==expected,(k,expected);checked[k]=expected
for key,node in m['origin_nodes'].items():
 owner=node['owner'];n=node['module'];sha=node['sha256'];root=Path(owner)
 if owner not in cache:
  state,sh=read(root/'state.json');pin(root/'state.json',sh);manifest={}
  if 'manifest_sha256' in state:
   manifest,ph=read(root/'manifest.json');assert ph==state['manifest_sha256'];pin(root/'manifest.json',ph)
  idx={}
  for r in state.get('records',[]):
   name=r.get('module',r.get('name',''))
   if '.' not in name:name='DiophantineConsistency.'+name
   idx[(name,r.get('object_sha256'))]=r
  cache[owner]=(state,manifest,idx,sh)
 state,manifest,idx,sh=cache[owner];row=idx.get((n,sha));assert row is not None and row.get('exit',0)==0 and row.get('verified',True) is True,(owner,n)
 short=n.removeprefix('DiophantineConsistency.');expected=row.get('source_sha256') or manifest.get('source_sha256',{}).get(n) or manifest.get('observed_sources',{}).get(short);assert expected is not None and expected==node['source_sha256'],(owner,n,expected,node['source_sha256'])
 if n in m['source_sha256']:assert expected==m['source_sha256'][n],n
 pin(node['physical_path'],sha);pin(node['source_path'],expected);pin(node['log_path'],row['log_sha256'])
 rows_out[key]={'module':n,'owner':owner,'provider_state_sha256':sh,'source_path':node['source_path'],'source_sha256':expected,'log_path':node['log_path'],'log_sha256':row['log_sha256'],'object_sha256':sha}
assert len(rows_out)==1025 and h(M)==mh and h(F)==fh and h(__file__)==ah;assert all(h(path)==v for path,v in checked.items())
(D/'source-nodes.json').write_text(json.dumps(rows_out,sort_keys=True,indent=2)+'\n');receipt={'status':'PASS_PROJECT_SOURCE_ORIGINS','plan_manifest_sha256':mh,'fixed_manifest_sha256':fh,'audit_sha256':ah,'source_nodes_sha256':h(D/'source-nodes.json'),'node_count':len(rows_out),'provider_count':len(cache),'guarded_file_count':len(checked),'boundary':'Physical provider source/log/object records only; no Lean replay, current-source theorem, package-transitive or dynamic ancestry is claimed.'};(D/'receipt.json').write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n');print('PASS_PROJECT_SOURCE_ORIGINS',len(rows_out),'nodes',len(cache),'providers',len(checked),'files',flush=True)
