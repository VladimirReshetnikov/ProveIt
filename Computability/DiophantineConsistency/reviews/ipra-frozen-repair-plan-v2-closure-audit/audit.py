#!/usr/bin/env python3
"""Independently reconstruct retained project environments from provider records."""
from pathlib import Path
import hashlib,json,re,collections
D=Path(__file__).resolve().parent;R=D.parents[3];V=R/'Computability/DiophantineConsistency/reviews';M=V/'ipra-frozen-repair-plan-v2/manifest.json';F=V/'ipra-adaptive-native-fixed-continuation/manifest.json';SNAP=V/'ipra-adaptive-fixed-snapshot-prefix/sources';h=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):
 b=Path(p).read_bytes();return json.loads(b),hashlib.sha256(b).hexdigest()
m,mh=read(M);f,fh=read(F);ah=h(__file__);assert fh==m['fixed_manifest_sha256'];assert m['source_sha256']==f['source_sha256'];assert all(h(SNAP/(n.replace('.','/')+'.lean'))==v for n,v in m['source_sha256'].items())
EXT={'Foundation','Mathlib','Lean','Init','Std','Batteries','Qq','Aesop','Plausible','ProofWidgets','ImportGraph','LeanSearchClient','Lake'};nodes=m['origin_nodes'];guard=m['origin_guard'];P=Path(m['peer_state_path']).parent;chosen={rel.removesuffix('.olean').replace('/','.'):v for rel,v in m['parent_inventory'].items() if rel.endswith('.olean')};states={};rows={};edges=0;externals=0

def provider(owner):
 if owner not in states:
  p=Path(owner)/'state.json';key=str(p.resolve());assert key in guard and h(p)==guard[key];st,_=read(p);states[owner]=st;idx={}
  for r in st.get('records',[]):
   name=r.get('module',r.get('name',''))
   if '.' not in name:name='DiophantineConsistency.'+name
   idx[(name,r.get('object_sha256'))]=r
  rows[owner]=idx
 return states[owner]
def nodekey(n,sha,path):return '|'.join((n,sha,str(Path(path).resolve())))
def matchfile(path,digest):
 key=str(Path(path).resolve());assert guard.get(key)==digest and h(path)==digest,(str(path),digest,guard.get(key))
for key,node in nodes.items():
 n=node['module'];sha=node['sha256'];owner=node['owner'];assert key==nodekey(n,sha,node['physical_path']);st=provider(owner);row=rows[owner].get((n,sha));assert row is not None,(owner,n,sha);matchfile(node['physical_path'],sha);matchfile(node['source_path'],node['source_sha256']);matchfile(node['log_path'],row['log_sha256'])
 if n in m['source_sha256']:assert node['source_sha256']==m['source_sha256'][n],n
 # None of the selected physical records in this plan use a reconstructed
 # transitive-manifest shortcut; if that changes, extend this verifier first.
 assert not row.get('transitive_manifest'),(owner,n,'unsupported manifest source')
 if 'direct_imports' in row:imports=row['direct_imports']
 elif 'dependency_hashes' in row:
  roots=[Path(x) for x in st.get('LEAN_PATH','').split(':') if x];assert roots,(owner,n)
  imports={}
  for dep,want in row['dependency_hashes'].items():
   rel=dep.replace('.','/')+'.olean';path=next((p/rel for p in roots if (p/rel).is_file()),None);assert path is not None,(owner,n,dep);imports[dep]={'sha256':want,'resolved_path':str(path.resolve())}
 else:raise AssertionError(('missing recorded imports',owner,n))
 expected={}
 for dep,v in imports.items():
  want=v['sha256'];original=str(Path(v['resolved_path']).resolve());matchfile(original,want)
  if dep.split('.')[0] in EXT:
   # The chosen package/toolchain object and all companions are separately
   # inventoried; package-transitive ancestry is not asserted here.
   paths=[Path('/tmp/pra14-full-transitive-2x6o__to/package-lib')/(dep.replace('.','/')+'.olean'),Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')/(dep.replace('.','/')+'.olean')];selected=next((p for p in paths if p.is_file()),None);assert selected is not None and h(selected)==want,(n,dep);assert m['external_direct_paths'].get(str(selected))==want;externals+=1;continue
  edges+=1;rec=chosen.get(dep);assert rec is not None and rec['sha256']==want,(n,dep,want,rec);expected[dep]=want
  for p in {original,rec['resolved_path']}:
   child=nodes.get(nodekey(dep,want,p));assert child is not None,('missing original or selected origin node',n,dep,p)
   for k,v in child['project_environment'].items():
    assert k not in expected or expected[k]==v,(n,k,'conflicting transitive hashes');expected[k]=v
 assert expected==node['project_environment'],('project environment differs from recorded provider graph',n,owner)
# Independently derive target closure and the dirty-set reuse fixed point.
seen=set();deps={}
def visit(n):
 if n in seen:return
 seen.add(n);imps=re.findall(r'^import\s+([A-Z][\w.]*)',(SNAP/(n.replace('.','/')+'.lean')).read_text(),re.M);deps[n]=[x for x in imps if x.split('.')[0] not in EXT]
 for x in deps[n]:visit(x)
visit('DiophantineConsistency.IPRAAdaptiveNativeZFCChecks');dirty=set(m['order']);assert dirty<=seen and set(m['known_seeds'])<=dirty
order_seen=set()
for n in m['order']:
 assert all(d not in dirty or d in order_seen for d in deps[n]);order_seen.add(n)
for n in seen-dirty:
 rec=chosen[n];node=nodes.get(nodekey(n,rec['sha256'],rec['resolved_path']));assert node is not None,('missing selected retained origin',n);assert not dirty.intersection(node['project_environment']),('retained original environment contains dirty object',n)
assert len(seen)==1098 and len(dirty)==73
# The recorded expected files are guarded before and after this verifier.
assert all(h(p)==v for p,v in guard.items());assert h(M)==mh and h(F)==fh and h(__file__)==ah;assert all(h(p)==v for p,v in guard.items())
receipt={'status':'PASS_PROJECT_CLOSURE','plan_manifest_sha256':mh,'fixed_manifest_sha256':fh,'audit_sha256':ah,'reachable':len(seen),'dirty':len(dirty),'retained':len(seen-dirty),'original_nodes':len(nodes),'recorded_project_edges_checked':edges,'recorded_external_edges_checked':externals,'guarded_files':len(guard),'boundary':'Independently reconstructed project dependency environments only; no Lean replay, current-source theorem, package-transitive or dynamically loaded ancestry is claimed.'};(D/'receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n');print('PASS_PROJECT_CLOSURE',len(nodes),'nodes',edges,'project edges',externals,'external edges',flush=True)
