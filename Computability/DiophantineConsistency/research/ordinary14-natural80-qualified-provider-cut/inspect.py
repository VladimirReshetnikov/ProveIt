#!/usr/bin/env python3
"""Read-only lexical qualified-provider cut and bounded path scan; no Lean."""
import hashlib,json,os,re,sys
from pathlib import Path
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):raise SystemExit('Use python3 -I -S -B')
D=Path(__file__).resolve().parents[2];ROOT=D.parents[1]
P72=Path('/tmp/p72-current-base-extension-attempt02-20261105');BASE=Path('/tmp/current14-standard-fresh-build-20261104')
PKG=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');TOOL=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,(str(p),sha(b));return json.loads(b)
inv=pin(D/'research/ordinary14-natural80-combined-slim-overlay/inventory.json','bd10f4c2b320ce1255f57f5bf1e9aefc346d2b2a2b5a8b989547f78f060c2be7')
prior=pin(D/'research/ordinary14-root74-provider-survey/observation.json','14732a54d8f2d3592d31f78d731497a1d804780ca8ec643e3851314868e7b4ab')
progress=pin(P72/'progress.json','f4bbe5f0b543497d543f243e10d8ead6d778cc3d0bf0aec96dfa73f7e622dd5a')
snapshot=pin(P72/'source-snapshot.json','4536c44c399dc42037b692a39a36cc74c807693e1e5a76e2f5db299691fff7d8')
base=pin(BASE/'state.json','f618a1c0970874ad349ea29b128cd8f775dd6a09036af3a75731e91f7982e014')
assert progress['status']==base['status']=='PASS'
direct={r['module']:r for r in inv['qualified_direct_sources']};assert len(direct)==40
for name,row in direct.items():
 b=(D/row['path']).read_bytes();assert sha(b)==row['sha256'] and row['path']=='Lean/'+name.replace('.','/')+'.lean'
def obj(root,name):return root/(name.replace('.','/')+'.olean')
def file_evidence(path):
 if not os.path.lexists(path):return None
 if not path.is_file():return {'path':str(path),'file':False,'symlink':path.is_symlink()}
 return {'path':str(path),'realpath':str(path.resolve(strict=True)),'sha256':sha(path.read_bytes()),'symlink':path.is_symlink()}
def source_path(n):return D/'Lean'/(n.replace('.','/')+'.lean')
def imports(path):
 out=[]
 for line in path.read_text().splitlines():
  line=line.strip()
  if not line:continue
  if not line.startswith('import '):break
  assert re.fullmatch(r'import [A-Za-z0-9_.]+(?:\s+[A-Za-z0-9_.]+)*',line),(str(path),line)
  out.extend(line.split()[1:])
 return out
overlay=D/'research/ordinary14-natural80-combined-slim-overlay'
observed_direct=set()
for row in inv['drafts_topological']:
 path=overlay/row['overlay_path'];assert path.is_file() and not path.is_symlink()
 assert sha(path.read_bytes())==row['overlay_sha256'],row['module']
 names=imports(path)
 assert [n for n in names if '.' not in n]==row['bare_imports'],row['module']
 qual=[n for n in names if '.' in n]
 assert qual==row['qualified_imports'],row['module']
 observed_direct.update(qual)
assert len(inv['drafts_topological'])==184 and observed_direct==set(direct)
pending=sorted(direct,reverse=True);seen=set();missing={};front={};external=set()
records={r['module']:r for r in base['records']}
while pending:
 n=pending.pop()
 if n in seen:continue
 seen.add(n)
 if not n.startswith('DiophantineConsistency.'):
  external.add(n);continue
 p=obj(P72/'lib',n)
 if p.is_file():
  sp=source_path(n);assert sp.is_file(); sourcehash=sha(sp.read_bytes())
  assert snapshot.get(n)==sourcehash or records.get(n,{}).get('source_sha256')==sourcehash,n
  if n in records:
   assert records[n]['object_sha256']==sha(p.read_bytes()),n
  front[n]={'object':file_evidence(p),'current_source_path':str(sp.relative_to(D)),'current_source_sha256':sourcehash,
    'p72_snapshot_source_sha256':snapshot.get(n),'base_record_source_sha256':records.get(n,{}).get('source_sha256'),
    'base_record_object_sha256':records.get(n,{}).get('object_sha256')}
  continue
 sp=source_path(n);assert sp.is_file(),n
 imps=imports(sp);missing[n]={'path':str(sp.relative_to(D)),'sha256':sha(sp.read_bytes()),'lexical_imports':imps}
 pending.extend(imps)
expected={'DiophantineConsistency.BFS943.Direct80IndexOne','DiophantineConsistency.Compact44.FreeJ13','DiophantineConsistency.Compact44.FreeJ13Halt','DiophantineConsistency.DiscreteOrderedRingFacts','DiophantineConsistency.HAExpressionNoZeroEquiv'}
assert set(missing)==expected and len(front)==40 and len(external)==4
assert set(prior['slim_cut_new_sources'])<=set(missing) and set(prior['slim_cut_frontier'])<=set(front)
assert set(external)==set(prior['slim_cut_external'])
external_obj={n:file_evidence(obj(PKG,n)) for n in sorted(external)}
for n,item in external_obj.items():
 old=prior['slim_cut_external'][n]
 assert item and item['path']==old['path'] and item['realpath']==old['realpath'] and item['sha256']==old['sha256']
# Named observation roots, not a global search. Additional roots are evidence
# of alternate files only, never candidates authenticated for this route.
roots={'selected_p72':P72/'lib','linked_base':BASE/'lib','guarded_package':PKG,'toolchain':TOOL,
 'workspace_build':ROOT/'.lake/build/lib/lean','prior_p72_attempt':Path('/tmp/p72-current-base-extension-20261105/lib'),
 'captured_p72_endpoint':Path('/tmp/p72-p13-p14-captured-endpoint-20261105/lib'),
 'carrier_retry05':Path('/tmp/current14-coherent490-refactor-retry05-20261110/lib')}
suffixes=['.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash','.so','.dll','.dylib']
names=sorted({r['module'] for r in inv['drafts_topological']}|set(missing));assert len(names)==189
hits=[]
for label,root in roots.items():
 for n in names:
  for suffix in suffixes:
   p=root/(n.replace('.','/')+suffix)
   if os.path.lexists(p):hits.append({'root':label,'module':n,'suffix':suffix,'evidence':file_evidence(p)})
# Independently report all direct-module candidate objects in the same roots;
# repeated paths may resolve to the same producer and do not imply a conflict.
direct_paths={n:{label:file_evidence(obj(root,n)) for label,root in roots.items() if os.path.lexists(obj(root,n))} for n in sorted(direct)}
print(json.dumps({'scope':'point-in-time lexical source/presence cut and bounded selected-root slots; no Lean, provider closure or launch-readiness claim',
 'direct_qualified_count':len(direct),'source_candidates':dict(sorted(missing.items())),
 'selected_project_frontier':dict(sorted(front.items())),'selected_external':external_obj,
 'additional_source_candidates_vs_root74':sorted(set(missing)-set(prior['slim_cut_new_sources'])),
 'additional_selected_frontier_vs_root74':sorted(set(front)-set(prior['slim_cut_frontier'])),
 'collision_scan':{'names':len(names),'roots':{k:str(v) for k,v in roots.items()},'suffixes':suffixes,'hits':hits},
 'direct_object_candidates':direct_paths},sort_keys=True,indent=2))
