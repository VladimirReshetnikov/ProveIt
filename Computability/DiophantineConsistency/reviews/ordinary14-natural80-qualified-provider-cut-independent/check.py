#!/usr/bin/env python3
"""Independent bounded BFS and filesystem comparison; never invokes Lean."""
from pathlib import Path
from collections import deque
import hashlib,json,os,re,sys
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):raise SystemExit('Use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];ROOT=D.parents[1]
R=D/'research/ordinary14-natural80-qualified-provider-cut'
P72=Path('/tmp/p72-current-base-extension-attempt02-20261105')
BASE=Path('/tmp/current14-standard-fresh-build-20261104')
PKG=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
TOOL=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')
def digest(path):
 with path.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def pinned(path,sha):
 assert digest(path)==sha,str(path)
 return json.loads(path.read_bytes())
obs=pinned(R/'observation.json','c88630304b866b29fe68a11f14f44af210fcd8ea5eed173523ae687c8c157979')
inv=pinned(D/'research/ordinary14-natural80-combined-slim-overlay/inventory.json','bd10f4c2b320ce1255f57f5bf1e9aefc346d2b2a2b5a8b989547f78f060c2be7')
prior=pinned(D/'research/ordinary14-root74-provider-survey/observation.json','14732a54d8f2d3592d31f78d731497a1d804780ca8ec643e3851314868e7b4ab')
snapshot=pinned(P72/'source-snapshot.json','4536c44c399dc42037b692a39a36cc74c807693e1e5a76e2f5db299691fff7d8')
progress=pinned(P72/'progress.json','f4bbe5f0b543497d543f243e10d8ead6d778cc3d0bf0aec96dfa73f7e622dd5a')
base=pinned(BASE/'state.json','f618a1c0970874ad349ea29b128cd8f775dd6a09036af3a75731e91f7982e014')
assert progress['status']==base['status']=='PASS'
base_records={row['module']:row for row in base['records']}
def source(name):return D/'Lean'/Path(*name.split('.')).with_suffix('.lean')
def object_path(root,name,suffix='.olean'):return root/Path(*name.split('.')).with_suffix(suffix)
def header(path):
 out=[]
 for line in path.read_text().splitlines():
  line=line.strip()
  if not line:continue
  m=re.fullmatch(r'import ([A-Za-z0-9_.]+(?:\s+[A-Za-z0-9_.]+)*)',line)
  if not m:break
  out.extend(m.group(1).split())
 return out
def evidence(path):
 if not os.path.lexists(path):return None
 if not path.is_file():return {'path':str(path),'file':False,'symlink':path.is_symlink()}
 return {'path':str(path),'realpath':str(path.resolve(strict=True)),'sha256':digest(path),'symlink':path.is_symlink()}
# Independently reconstruct direct headers from all 184 overlay snapshots.
rows=inv['drafts_topological'];assert len(rows)==184
assert len({r['module'] for r in rows})==184
actual_direct=set()
for row in rows:
 path=D/'research/ordinary14-natural80-combined-slim-overlay'/row['overlay_path']
 assert path.is_file() and not path.is_symlink() and digest(path)==row['overlay_sha256']
 imps=header(path)
 assert [x for x in imps if '.' not in x]==row['bare_imports']
 assert [x for x in imps if '.' in x]==row['qualified_imports']
 actual_direct.update(x for x in imps if '.' in x)
direct={r['module']:r for r in inv['qualified_direct_sources']}
assert set(direct)==actual_direct and len(direct)==40
for n,row in direct.items():
 path=source(n);assert row['path']==str(path.relative_to(D)) and digest(path)==row['sha256']
# FIFO traversal differs from the author's stack traversal; stop at selected
# object presence or an external name, never inspect compiled imports.
queue=deque(sorted(direct));seen=set();missing={};front={};external=set()
while queue:
 n=queue.popleft()
 if n in seen:continue
 seen.add(n)
 if not n.startswith('DiophantineConsistency.'):
  external.add(n);continue
 obj=object_path(P72/'lib',n);sp=source(n);assert sp.is_file()
 sh=digest(sp)
 if obj.is_file():
  assert snapshot.get(n)==sh or base_records.get(n,{}).get('source_sha256')==sh,n
  if n in base_records:assert base_records[n]['object_sha256']==digest(obj),n
  front[n]={'object':evidence(obj),'current_source_path':str(sp.relative_to(D)),
   'current_source_sha256':sh,'p72_snapshot_source_sha256':snapshot.get(n),
   'base_record_source_sha256':base_records.get(n,{}).get('source_sha256'),
   'base_record_object_sha256':base_records.get(n,{}).get('object_sha256')}
 else:
  missing[n]={'path':str(sp.relative_to(D)),'sha256':sh,'lexical_imports':header(sp)}
  queue.extend(header(sp))
expected={'DiophantineConsistency.BFS943.Direct80IndexOne','DiophantineConsistency.Compact44.FreeJ13',
 'DiophantineConsistency.Compact44.FreeJ13Halt','DiophantineConsistency.DiscreteOrderedRingFacts',
 'DiophantineConsistency.HAExpressionNoZeroEquiv'}
assert set(missing)==expected and missing==obs['source_candidates']
assert len(front)==40 and front==obs['selected_project_frontier']
assert sum(v['p72_snapshot_source_sha256']==v['current_source_sha256'] for v in front.values())==32
assert sum(v['base_record_source_sha256']==v['current_source_sha256'] for v in front.values())==8
assert len(external)==4 and external==set(prior['slim_cut_external'])
assert {n:evidence(object_path(PKG,n)) for n in external}==obs['selected_external']
assert sorted(set(missing)-set(prior['slim_cut_new_sources']))==obs['additional_source_candidates_vs_root74']
assert sorted(set(front)-set(prior['slim_cut_frontier']))==obs['additional_selected_frontier_vs_root74']
assert len(obs['additional_selected_frontier_vs_root74'])==9
roots={'selected_p72':P72/'lib','linked_base':BASE/'lib','guarded_package':PKG,'toolchain':TOOL,
 'workspace_build':ROOT/'.lake/build/lib/lean','prior_p72_attempt':Path('/tmp/p72-current-base-extension-20261105/lib'),
 'captured_p72_endpoint':Path('/tmp/p72-p13-p14-captured-endpoint-20261105/lib'),
 'carrier_retry05':Path('/tmp/current14-coherent490-refactor-retry05-20261110/lib')}
suffixes=['.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash','.so','.dll','.dylib']
assert obs['collision_scan']['roots']=={k:str(v) for k,v in roots.items()}
assert obs['collision_scan']['suffixes']==suffixes
names=sorted({r['module'] for r in rows}|set(missing));assert len(names)==189
hits=[]
for label,root in roots.items():
 for n in names:
  for suffix in suffixes:
   path=object_path(root,n,suffix)
   if os.path.lexists(path):hits.append({'root':label,'module':n,'suffix':suffix,'evidence':evidence(path)})
assert hits==obs['collision_scan']['hits'] and len(hits)==2
assert {r['module'] for r in hits}=={'DiophantineConsistency.DiscreteOrderedRingFacts'}
assert len({r['evidence']['sha256'] for r in hits})==1
assert len({r['evidence']['realpath'] for r in hits})==2
alts={n:{label:evidence(object_path(root,n)) for label,root in roots.items() if os.path.lexists(object_path(root,n))} for n in sorted(direct)}
assert alts==obs['direct_object_candidates']
different=[]
for n,paths in alts.items():
 selected=paths.get('selected_p72')
 if selected and any(p and p.get('file',True) and p['sha256']!=selected['sha256'] for label,p in paths.items() if label!='selected_p72'):
  different.append(n)
assert len(different)==6 and 'DiophantineConsistency.ModelDifferenceRing' in different
print(json.dumps({'scope':'independent bounded BFS, hashes and selected-root slots; no Lean/provider-closure claim',
 'overlay_modules':184,'direct_qualified':len(direct),'missing_project_sources':len(missing),
 'selected_project_frontier':len(front),'selected_external':len(external),
 'frontier_source_snapshot_matches':32,'frontier_base_source_matches':8,
 'additional_frontier_vs_root74':9,'scan_names':len(names),'scan_roots':len(roots),
 'scan_suffixes':len(suffixes),'slots_examined':len(names)*len(roots)*len(suffixes),
 'occupied_output_slots':len(hits),'different_direct_object_names':sorted(different)},sort_keys=True,indent=2))
