#!/usr/bin/env python3
"""Prepare a conservative physical-project-origin repair plan after both fixed peers pass.

This produces a plan, not a proof.  Unknown original ancestry dirties its current
source owner and all dependents; an unresolved object is never silently reused.
"""
from pathlib import Path
import collections,graphlib,hashlib,json,os,re,sys

D=Path(__file__).resolve().parent;R=D.parents[3];V=R/'Computability/DiophantineConsistency/reviews'
F=V/'ipra-adaptive-native-fixed-continuation/manifest.json';SNAP=V/'ipra-adaptive-fixed-snapshot-prefix/sources'
A=Path('/tmp/ipra-adaptive-native-fixed-continuation-8mckr1yj');B=Path('/tmp/ipra-adaptive-native-fixed-continuation-n1l8kvzg')
PKG=Path('/tmp/pra14-full-transitive-2x6o__to/package-lib');LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');TOOL=LEAN.parent.parent/'lib/lean'
REPLAY=V/'ipra-frozen-repair-replay-template/replay.py';OUT=V/'ipra-frozen-repair-plan-v2-independent'
EXT={'Foundation','Mathlib','Lean','Init','Std','Batteries','Qq','Aesop','Plausible','ProofWidgets','ImportGraph','LeanSearchClient','Lake'}
SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean','.ilean.hash')
h=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
inputs={};guard={}
def readjson(p):
 p=Path(p);raw=p.read_bytes();key=str(p.resolve());digest=hashlib.sha256(raw).hexdigest();inputs[key]=digest;return json.loads(raw)
def pin(p,expected=None):
 p=Path(p);assert p.is_file(),str(p);q=str(p.resolve());digest=h(p)
 if expected is not None:assert digest==expected,(str(p),digest,expected)
 if q in guard:assert guard[q]==digest,q
 guard[q]=digest;return digest
prepare_bytes=Path(__file__).read_bytes();replay_bytes=REPLAY.read_bytes()
inputs[str(Path(__file__).resolve())]=hashlib.sha256(prepare_bytes).hexdigest()
inputs[str(REPLAY.resolve())]=hashlib.sha256(replay_bytes).hexdigest()
f=readjson(F);a=readjson(A/'state.json');b=readjson(B/'state.json');assert a['status']==b['status']=='PASS'
assert a['manifest_sha256']==b['manifest_sha256']==h(F) and a['driver_sha256']==b['driver_sha256']==f['driver_sha256']
assert [r['name'] for r in a['records']]==[r['name'] for r in b['records']]==f['order']
for x,y in zip(a['records'],b['records']):
 assert all(x.get(k)==y.get(k) for k in ['name','exit','object_sha256','log_sha256','warnings']) and x['exit']==0
 assert {n:v['sha256'] for n,v in x['direct_imports'].items()}=={n:v['sha256'] for n,v in y['direct_imports'].items()}
 for root,row in [(A,x),(B,y)]:
  n=row['name'];pin(root/'lib'/(n.replace('.','/')+'.olean'),row['object_sha256']);pin(root/'logs'/(n.replace('.','_')+'.log'),row['log_sha256'])
  for v in row['direct_imports'].values():pin(v['resolved_path'],v['sha256'])
pin(LEAN,f['lean_sha256']);pin(F);pin(A/'state.json');pin(B/'state.json')
# Inventory every parent project object and present companion; verify it binds
# to the PASS output rows and the original selected prefix and base records.
parent_inventory={}
for d,_,fs in os.walk(B/'lib',followlinks=True):
 for name in fs:
  if name.endswith(('.olean','.olean.private','.olean.server','.ir','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean','.ilean.hash')):
   p=Path(d)/name;rel=str(p.relative_to(B/'lib'));parent_inventory[rel]={'sha256':pin(p),'resolved_path':str(p.resolve())}
for row in b['records']:assert parent_inventory[row['name'].replace('.','/')+'.olean']['sha256']==row['object_sha256']
for key in ['prefix_records','second_prefix_records','third_prefix_records','fourth_prefix_records']:
 for n,row in f[key].items():assert parent_inventory[n.replace('.','/')+'.olean']['sha256']==row['object_sha256']
excluded={n.replace('.','/')+'.olean' for n in f['affected']}
for rel,digest in f['parent_objects'].items():
 if rel not in excluded:assert parent_inventory[rel]['sha256']==digest
source_sha=f['source_sha256'];assert set(source_sha)==set(f['source_files'])
for n,digest in source_sha.items():pin(SNAP/(n.replace('.','/')+'.lean'),digest)
# Derive the current project source graph exclusively from the complete frozen
# source universe. Missing project source means the plan must not be emitted.
source_imports={};graph={};reachable=set()
def imports(n):
 if n not in source_imports:
  p=SNAP/(n.replace('.','/')+'.lean');assert n in source_sha and p.is_file(),('missing frozen project source',n)
  source_imports[n]=re.findall(r'^import\s+([A-Z][\w.]*)',p.read_text(),re.M)
 return source_imports[n]
def visit(n):
 if n in reachable:return
 reachable.add(n);graph[n]=[x for x in imports(n) if x.split('.')[0] not in EXT]
 for x in graph[n]:visit(x)
target='DiophantineConsistency.IPRAAdaptiveNativeZFCChecks';visit(target)
reverse=collections.defaultdict(set)
for n,ds in graph.items():
 for d in ds:reverse[d].add(n)
chosen={rel.removesuffix('.olean').replace('/','.'):v['sha256'] for rel,v in parent_inventory.items() if rel.endswith('.olean')}
for n in reachable:assert n in chosen,('missing selected object',n)

# Selected direct external resolution follows Lean's package mirror first and
# toolchain second. Record both presences/absences to prevent later shadowing.
external_files={};external_absent=set();external_direct_paths={};external_resolved_paths={};external_absent_paths=set();external_lookup={}
def extlookup(n):
 if n in external_lookup:return external_lookup[n]
 stem=n.replace('.','/');pkg=PKG/(stem+'.olean');tool=TOOL/(stem+'.olean');pick=next((p for p in [pkg,tool] if p.is_file()),None)
 if pick is None:raise ValueError(('missing direct external object',n))
 for suffix in SUFFIXES:
  rel=stem+suffix
  for root in [PKG,TOOL]:
   p=root/rel
   if p.is_file():
    digest=pin(p);external_direct_paths[str(p)]=digest;external_resolved_paths[str(p)]=str(p.resolve())
    if root==PKG:external_files[rel]={'sha256':digest,'resolved_path':str(p.resolve())}
   else:
    assert not os.path.lexists(p),('broken external symlink',str(p));external_absent_paths.add(str(p))
    if root==PKG:external_absent.add(rel)
 v={'sha256':pin(pick),'resolved_path':str(pick.resolve())};external_lookup[n]=v;return v

class UnknownOrigin(Exception):pass
state_cache={};index_cache={};manifest_cache={};node_cache={};error_cache={};active=set();origin_nodes={};origin_edges=collections.defaultdict(set)
def stateof(owner):
 if owner in state_cache:return state_cache[owner]
 path=Path(owner)/'state.json'
 if not path.is_file():raise UnknownOrigin(('missing physical provider state',str(path)))
 st=readjson(path);pin(path)
 manifest=Path(owner)/'manifest.json'
 if 'manifest_sha256' in st:
  if not manifest.is_file():raise UnknownOrigin(('missing physical provider manifest',owner))
  try:pin(manifest,st['manifest_sha256'])
  except AssertionError as exc:raise UnknownOrigin(('physical manifest mismatch',owner,str(exc)))
  manifest_cache[owner]=readjson(manifest)
 state_cache[owner]=st;return st
def rowof(owner,n,sha):
 st=stateof(owner)
 if owner not in index_cache:
  idx={}
  for row in st.get('records',[]):
   name=row.get('module',row.get('name',''))
   if '.' not in name:name='DiophantineConsistency.'+name
   idx[(name,row.get('object_sha256'))]=row
  index_cache[owner]=idx
 row=index_cache[owner].get((n,sha))
 if row is None:raise UnknownOrigin(('physical provider record missing',owner,n,sha))
 if row.get('exit',0)!=0 or row.get('verified',True) is not True:raise UnknownOrigin(('unsuccessful original record',owner,n))
 return row

def source_and_log(owner,n,row):
 root=Path(owner);short=n.removeprefix('DiophantineConsistency.');m=manifest_cache.get(owner,{})
 expected=row.get('source_sha256') or m.get('source_sha256',{}).get(n) or m.get('observed_sources',{}).get(short)
 choices=[root/'src'/(n.replace('.','/')+'.lean'),root/'source-snapshots'/(n.replace('.','_')+'.lean'),root/'logs'/(short+'.lean')]
 shared={'/tmp/ipra-adaptive-native-second-continuation-8ziag05a':'ipra-adaptive-native-second-continuation','/tmp/ipra-adaptive-native-warning-continuation-x2wbh2da':'ipra-adaptive-native-warning-continuation'}.get(owner)
 if shared:
  packet=V/shared;st=stateof(owner)
  try:
   pin(packet/'manifest.json',st['manifest_sha256']);pin(root/'driver.py',st['driver_sha256'])
  except (OSError,AssertionError) as exc:raise UnknownOrigin(('shared frozen source packet authentication failed',owner,n,str(exc)))
  if "src=D/'sources'" not in (root/'driver.py').read_text():raise UnknownOrigin(('unexpected shared source-root driver',owner,n))
  choices.insert(0,packet/'sources'/(n.replace('.','/')+'.lean'))
 if root==B:choices.insert(0,SNAP/(n.replace('.','/')+'.lean'))
 path=next((p for p in choices if p.is_file()),None)
 if path is None or expected is None:raise UnknownOrigin(('missing original source evidence',owner,n))
 try:pin(path,expected)
 except AssertionError as exc:raise UnknownOrigin(('original source hash mismatch',owner,n,str(exc)))
 logname=row.get('log_file');logs=([root/'logs'/logname] if logname else [])+[root/'logs'/(n.replace('.','_')+'.log'),root/'logs'/(short+'.log')]
 log=next((p for p in logs if p.is_file()),None)
 if log is None or not row.get('log_sha256'):raise UnknownOrigin(('missing original compiler log',owner,n))
 try:pin(log,row['log_sha256'])
 except AssertionError as exc:raise UnknownOrigin(('original log mismatch',owner,n,str(exc)))
 if n in source_sha and source_sha[n]!=expected:raise UnknownOrigin(('original source differs from frozen source',owner,n,expected,source_sha[n]))
 return str(path.resolve()),str(log.resolve()),expected

def trace(n,sha,path):
 real=str(Path(path).resolve());key=(n,sha,real)
 if key in node_cache:return node_cache[key]
 if key in error_cache:raise UnknownOrigin(error_cache[key])
 if key in active:raise UnknownOrigin(('cyclic original provenance',key))
 active.add(key)
 try:
  try:pin(real,sha)
  except (AssertionError,OSError) as exc:raise UnknownOrigin(('original project object mismatch',key,str(exc)))
  parts=Path(real).parts
  if 'lib' not in parts:raise UnknownOrigin(('unrecognized project object owner',key))
  owner='/'+'/'.join(parts[1:parts.index('lib')]);row=rowof(owner,n,sha);src,log,ssha=source_and_log(owner,n,row);st=stateof(owner);deps={}
  if row.get('transitive_manifest'):
   mp=Path(owner)/'transitive-manifests'/row['transitive_manifest']
   try:pin(mp,row['transitive_manifest_sha256']);data=readjson(mp)
   except (OSError,AssertionError) as exc:raise UnknownOrigin(('missing original transitive manifest',n,str(exc)))
   rawdeps={d:{'sha256':v['sha256'],'resolved_path':str((Path(owner)/'lib'/(d.replace('.','/')+'.olean')).resolve())} for d,v in data.items() if v.get('kind')=='project'}
  elif 'direct_imports' in row:rawdeps=row['direct_imports']
  elif 'dependency_hashes' in row:
   rawdeps={}
   roots=[Path(x) for x in st.get('LEAN_PATH','').split(':') if x]
   if not roots:raise UnknownOrigin(('original LEAN_PATH unavailable',owner,n))
   for d,expected in row['dependency_hashes'].items():
    rel=d.replace('.','/')+'.olean';p=next((x/rel for x in roots if (x/rel).is_file()),None)
    if p is None:raise UnknownOrigin(('original import path unavailable',owner,n,d))
    rawdeps[d]={'sha256':expected,'resolved_path':str(p.resolve())}
  else:raise UnknownOrigin(('missing original import record',owner,n))
  for dep,v in rawdeps.items():
   want=v['sha256'];op=v.get('resolved_path')
   if not op:raise UnknownOrigin(('original import path unavailable',owner,n,dep))
   if dep.split('.')[0] in EXT:
    try:pin(op,want);selected=extlookup(dep)
    except (AssertionError,OSError,ValueError) as exc:raise UnknownOrigin(('original direct external unavailable',owner,n,dep,str(exc)))
    if selected['sha256']!=want:raise UnknownOrigin(('original external hash differs',owner,n,dep,want,selected['sha256']))
    continue
   origin_edges[dep].add(n);deps[dep]=want
   try:pin(op,want)
   except (AssertionError,OSError) as exc:raise UnknownOrigin(('original project dependency unavailable',owner,n,dep,str(exc)))
   if chosen.get(dep)!=want:raise UnknownOrigin(('selected original project dependency differs',owner,n,dep,want,chosen.get(dep)))
   original_env=trace(dep,want,op)
   selected_path=str((B/'lib'/(dep.replace('.','/')+'.olean')).resolve())
   environments=[original_env]
   if selected_path!=str(Path(op).resolve()):
    # Same object bytes can have different recorded provider environments.
    environments.append(trace(dep,want,selected_path))
   for nested in environments:
    for child,chash in nested.items():
     if child in deps and deps[child]!=chash:raise UnknownOrigin(('conflicting original environment',n,child))
     deps[child]=chash
  origin_nodes['|'.join(key)]={'module':n,'sha256':sha,'physical_path':real,'owner':owner,'source_path':src,'source_sha256':ssha,'log_path':log,'project_environment':deps}
  node_cache[key]=deps;return deps
 except UnknownOrigin as exc:
  error_cache[key]=str(exc);raise
 finally:active.remove(key)

# Seed known stale-origin objects; every retained candidate is independently
# traced, including original project nodes outside the current target graph.
seed={'DiophantineConsistency.PRAPositiveCode','DiophantineConsistency.PRAPositivePackedNormal'};assert seed<=reachable
# Record all direct externals in the frozen reachable graph. This is more
# conservative than the dirty set and avoids repeated resolution during closure.
for n in sorted(reachable):
 for dep in imports(n):
  if dep.split('.')[0] in EXT:extlookup(dep)
failed={}
for n in sorted(reachable-seed):
 path=B/'lib'/(n.replace('.','/')+'.olean')
 try:
  environment=trace(n,chosen[n],path)
  # Add the full recorded environment directly to each reachable reused root,
  # including dependencies whose modules are outside the current source graph.
  for dep in environment:origin_edges[dep].add(n)
 except (UnknownOrigin,OSError,AssertionError) as exc:failed[n]=repr(exc)
# Each original node's full environment provides reverse edges, including
# recorded project dependencies not in the source graph. Unknown candidates are
# dirty. Monotone closure accounts for both source and original dependencies.
dirty=set(seed)|set(failed);queue=list(dirty)
while queue:
 dep=queue.pop()
 for owner in reverse[dep]|origin_edges[dep]:
  if owner in reachable and owner not in dirty:dirty.add(owner);queue.append(owner)
assert target in dirty
order=list(graphlib.TopologicalSorter({n:[d for d in graph[n] if d in dirty] for n in dirty}).static_order());assert order[-1]==target
# Ensure every dependency needed by a rebuilt source is either scheduled or
# selected from the verified baseline. Unknown preserved dependencies are not
# allowed even if they appeared only outside the current target graph.
for n in order:
 for dep in graph[n]:assert dep in dirty or dep in chosen,('unavailable build dependency',n,dep)
# Pin exact direct external imports for the generated replay.
lookup={d:extlookup(d) for n in dirty for d in imports(n) if d.split('.')[0] in EXT}
# All captured files, original states/logs/objects/sources, snapshots and binary
# are reread before plan emission. Source unknowns only cause rebuilding.
assert all(h(path)==digest for path,digest in guard.items());assert all(h(path)==digest for path,digest in inputs.items());assert all(not os.path.lexists(path) for path in external_absent_paths) and all(str(Path(path).resolve())==v for path,v in external_resolved_paths.items())
assert all(h(PKG/rel)==v['sha256'] and str((PKG/rel).resolve())==v['resolved_path'] for rel,v in external_files.items())
assert not OUT.exists(),('refusing to overwrite existing plan',str(OUT));OUT.mkdir()
(OUT/'prepare.py').write_bytes(prepare_bytes);(OUT/'replay.py').write_bytes(replay_bytes)
pin(OUT/'prepare.py',hashlib.sha256(prepare_bytes).hexdigest());pin(OUT/'replay.py',hashlib.sha256(replay_bytes).hexdigest())
plan={'author_state_path':str(A/'state.json'),'author_state_sha256':h(A/'state.json'),'peer_state_path':str(B/'state.json'),'peer_state_sha256':h(B/'state.json'),'fixed_manifest_sha256':h(F),'source_sha256':source_sha,'parent_inventory':parent_inventory,'origin_guard':guard,'order':order,'direct_imports':{n:imports(n) for n in order},'external_files':external_files,'external_absent':sorted(external_absent),'external_direct_paths':external_direct_paths,'external_resolved_paths':external_resolved_paths,'external_absent_paths':sorted(external_absent_paths),'external_lookup':lookup,'lean_sha256':h(LEAN),'driver_sha256':hashlib.sha256(replay_bytes).hexdigest(),'known_seeds':sorted(seed),'unknown_or_mismatched_origins':failed,'origin_nodes':origin_nodes,'reachable_source_count':len(reachable),'source_graph_sha256':hashlib.sha256(json.dumps(graph,sort_keys=True).encode()).hexdigest(),'origin_preparer_sha256':hashlib.sha256(prepare_bytes).hexdigest(),'boundary':'Fixed historical source snapshot; all reused project objects have physically traced recorded project environments matching selected bytes. Original external direct objects/companions are pinned; package-transitive and dynamic ancestry remain inherited, and the 848-project ancestor is author-only.'}
(OUT/'manifest.json').write_text(json.dumps(plan,sort_keys=True,indent=2)+'\n');print('PASS-plan dirty',len(dirty),'unknown',len(failed),'traced nodes',len(origin_nodes),'manifest',h(OUT/'manifest.json'),'driver',h(OUT/'replay.py'),flush=True)
