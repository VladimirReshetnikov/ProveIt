#!/usr/bin/env python3
"""Bounded, non-atomic inspection of retry05 evidence; never invokes Lean."""
import hashlib, json, os, sys
from collections import Counter
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]; REPO=D.parents[1]
P=D/'research/current14-coherent-extension-refactor-retry05-runner'; A=P/'attempt01'
OUT=Path('/tmp/current14-coherent490-refactor-retry05-20261110')
BASE=Path('/tmp/current14-standard-fresh-build-20261104')
PKG=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
TOOL=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')
SUFFIXES=['.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash','.so','.dll','.dylib']
cache={}
def sha(p):
 p=Path(p); r=str(p.resolve(strict=True))
 if r not in cache:
  h=hashlib.sha256()
  with p.open('rb') as f:
   for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
  cache[r]=h.hexdigest()
 return cache[r]
def pin(p,h):
 assert sha(p)==h,str(p)
 return json.loads(p.read_text())
plan=pin(P/'plan.json','b0006cd71994ebafccbd65a30d41e11cb8d953f52751b2c98f3884df3e63744c')
state=pin(A/'state.json','8b7d9a84b2bae01871a6417cb1529f85d5e0a35a1ec21a0cac1007dd159dcc82')
outer=pin(A/'outer-result.json','11e4abc49bceea5a05faaab13d56a1dacdebe4ec5c4b32742633288b657df4a7')
base=pin(BASE/'state.json','f618a1c0970874ad349ea29b128cd8f775dd6a09036af3a75731e91f7982e014')
assert sha(OUT/'state.json')==sha(A/'state.json')
assert state['status']==outer['status']=='FAILED' and state['failure']==outer['failure']=="Refusal('disk_floor')" and base['status']=='PASS'
assert len(plan['entries'])==529 and len(state['rows'])==240 and len(base['records'])==1000
assert len(state['base_links'])==1000
base_rows={r['module']:r for r in base['records']}; assert len(base_rows)==1000
# The selected source and copy checks are current point-in-time observations,
# not proof of Git cleanliness or of external providers.
for e in plan['entries']:
 src=REPO/e['source']; snap=OUT/'src'/(e['module'].replace('.','/')+'.lean')
 assert src.is_file() and snap.is_file() and sha(src)==sha(snap)==e['source_sha256'],e['module']
client=P/'Current14CoherentAudit.lean'; client_snap=OUT/'src/DiophantineConsistency/Current14CoherentAudit.lean'
assert sha(client)==sha(client_snap)=='b490d50244da4088a3258f290535aceb8b75e89b8cf030277be4cc15e32bf64e'
for path,v in state['base_links'].items():
 assert path.endswith('.olean'),path
 q=Path(path); assert q.is_symlink() and str(q.resolve(strict=True))==v['realpath'] and sha(q)==v['sha256'],path
# Outputs and previously recorded direct-dependency guards. No mutation of an
# absent guard path is performed. A direct guard may be repeated in many rows.
counts=Counter(); direct_paths={}; produced={}; route=Counter(); unique_deps=set(); stage_logs=0
for e,row in zip(plan['entries'][:239],state['rows'][:239]):
 n=e['module']; assert row['module']==n and row['source_sha256']==e['source_sha256']
 assert set(row['dependencies'])-{'Init'}==set(e['imports'])-{'Init'},n
 for kind in ('deps','compile'):
  child=row[kind];assert child['exit']==0 and child['stop_reason'] is None and not child['monitor_errors'] and not child['observed_descendant_pids']
  archived=A/'logs'/Path(child['log']).name; assert sha(archived)==sha(child['log'])==child['log_sha256']==outer['captured_logs'][archived.name];stage_logs+=1
 for path,v in row['output_guard'].items():
  q=Path(path); assert q.is_relative_to(OUT/'lib')
  suff=next((s for s in SUFFIXES if str(q)==str(OUT/'lib'/(n.replace('.','/')+s))),None); assert suff
  if v is None:
   assert not os.path.lexists(q),path; counts['output_absent']+=1
  else:
   assert q.is_file() and not q.is_symlink() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256'],path
   counts['output_present']+=1;counts['output_present_'+suff]+=1
 assert len(row['output_guard'])==len(SUFFIXES)
 obj=OUT/'lib'/(n.replace('.','/')+'.olean');assert sha(obj)==row['object_sha256'];produced[n]=row['object_sha256']
 for path,v in row['direct_guard'].items():
  if path in direct_paths: assert direct_paths[path]==v,path
  else: direct_paths[path]=v
 for dep,v in row['dependencies'].items():
  q=Path(v['path']);assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256'],(n,dep)
  unique_deps.add(dep)
  if dep in produced and dep!=n:
   expected=produced[dep];real=str((OUT/'lib'/(dep.replace('.','/')+'.olean')).resolve(strict=True));cat='prefix'
  elif dep in base_rows:
   expected=base_rows[dep]['object_sha256'];real=str((BASE/'lib'/(dep.replace('.','/')+'.olean')).resolve(strict=True));cat='base'
  else:
   assert dep in plan['external_direct'],(n,dep);expected=plan['external_direct'][dep]['sha256'];real=plan['external_direct'][dep]['realpath'];cat='external'
  assert v['sha256']==expected and v['realpath']==real,(n,dep,cat);route[cat]+=1
  # Observed ordered olean candidates only. Actual Lean --deps is not rerun.
  candidates=[r/(dep.replace('.','/')+'.olean') for r in (OUT/'lib',PKG,TOOL) if (r/(dep.replace('.','/')+'.olean')).is_file()]
  assert candidates and str(candidates[0])==v['path'],(n,dep)
for path,v in direct_paths.items():
 q=Path(path)
 if v is None: assert not os.path.lexists(q),path;counts['direct_distinct_absent']+=1
 else:
  assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256'],path
  counts['direct_distinct_present']+=1
assert len(produced)==239 and stage_logs==478
# At every pending module path inspect the retained output tree's 13 suffixes.
# External search-root collisions and imports remain separate unresolved work.
pending=[]
for e in plan['entries'][239:]:
 for suffix in SUFFIXES:
  p=OUT/'lib'/(e['module'].replace('.','/')+suffix)
  if os.path.lexists(p): pending.append(str(p))
assert not pending,pending[:10]
e=plan['entries'][239];stub=state['rows'][239]
assert e['module']==stub['module']=='DiophantineConsistency.Sign17KWeightAggregateProbe'
assert not any(k in stub for k in ('deps','compile','object_sha256','output_guard'))
assert not list((OUT/'logs').glob('239-*'))
assert plan['entries'][223]['module']=='DiophantineConsistency.Sign17ExactDegree'
stage240_all_root_collisions=[]
for root in (OUT/'lib',PKG,TOOL):
 for suffix in SUFFIXES:
  p=root/(e['module'].replace('.','/')+suffix)
  if os.path.lexists(p):stage240_all_root_collisions.append(str(p))
assert not stage240_all_root_collisions,stage240_all_root_collisions
audit_collisions=[]
for suffix in SUFFIXES:
 p=OUT/'lib'/('DiophantineConsistency/Current14CoherentAudit'+suffix)
 if os.path.lexists(p):audit_collisions.append(str(p))
assert not audit_collisions,audit_collisions
# Header-declared next imports are merely static candidate observations;
# no claim of dependency completeness or Lean selection is made.
candidates={}
for dep in sorted(set(e['imports'])|{'Init'}):
 cs=[]
 for root in (OUT/'lib',PKG,TOOL):
  p=root/(dep.replace('.','/')+'.olean')
  if p.is_file():cs.append({'path':str(p),'realpath':str(p.resolve()),'sha256':sha(p)})
 candidates[dep]=cs
print(json.dumps({'scope':'bounded non-atomic recorded prefix inspection; no Lean, complete provider closure or reuse authorization',
 'completed_stages':len(produced),'pending_planned_stages':len(plan['entries'])-len(produced),
 'selected_and_snapshotted_planned_sources':len(plan['entries']),'final_audit_source_snapshot_checked':True,
 'base_olean_links_verified':len(state['base_links']),'archived_and_live_child_logs_checked':stage_logs,
 'output_guard_counts':{k:v for k,v in sorted(counts.items()) if k.startswith('output_')},
 'direct_guard_distinct_counts':{k:v for k,v in sorted(counts.items()) if k.startswith('direct_')},
 'recorded_dependency_edges_by_producer':dict(sorted(route.items())), 'unique_recorded_dependency_names':len(unique_deps),
 'pending_output_suffix_slots_checked':(len(plan['entries'])-len(produced))*len(SUFFIXES),
 'pending_output_collisions':pending,'final_audit_output_suffix_slots_checked':len(SUFFIXES),
 'stage240':e['module'],'stage240_recorded_children':0,
 'stage240_declared_project_import_producer_stage':224,
 'stage240_all_root_suffix_slots_checked':3*len(SUFFIXES),
 'stage240_all_root_suffix_collisions':stage240_all_root_collisions,
 'stage240_static_import_candidates':candidates},sort_keys=True,indent=2))
