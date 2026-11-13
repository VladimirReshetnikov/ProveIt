#!/usr/bin/env python3
"""Read-only bounded natural79 lexical provider cut; never invokes Lean."""
from pathlib import Path
import hashlib,json,os,re,sys
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):raise SystemExit('Use python3 -I -S -B')
D=Path(__file__).resolve().parents[2];ROOT=D.parents[1];O=D/'research/ordinary14-natural79-combined-slim-overlay'
P72=Path('/tmp/p72-current-base-extension-attempt02-20261105');BASE=Path('/tmp/current14-standard-fresh-build-20261104')
PKG=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');TOOL=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(path,h):
 b=path.read_bytes();assert sha(b)==h,(str(path),sha(b));return json.loads(b)
inv=pin(O/'inventory.json','7f8f722c1a96194dc453a797a2ffafbcfea614b2c8c83fda9a51daefb0558483')
prev=pin(D/'research/ordinary14-natural80-qualified-provider-cut/observation.json','c88630304b866b29fe68a11f14f44af210fcd8ea5eed173523ae687c8c157979')
progress=pin(P72/'progress.json','f4bbe5f0b543497d543f243e10d8ead6d778cc3d0bf0aec96dfa73f7e622dd5a')
snapshot=pin(P72/'source-snapshot.json','4536c44c399dc42037b692a39a36cc74c807693e1e5a76e2f5db299691fff7d8')
base=pin(BASE/'state.json','f618a1c0970874ad349ea29b128cd8f775dd6a09036af3a75731e91f7982e014')
assert progress['status']==base['status']=='PASS'
def evidence(path):
 if not os.path.lexists(path):return None
 if not path.is_file():return {'path':str(path),'file':False,'symlink':path.is_symlink()}
 return {'path':str(path),'realpath':str(path.resolve(strict=True)),'sha256':sha(path.read_bytes()),'symlink':path.is_symlink()}
def obj(root,name):return root/(name.replace('.','/')+'.olean')
def imports(path):
 out=[]
 for line in path.read_text().splitlines():
  if not line.strip():continue
  m=re.fullmatch(r'import\s+([A-Za-z0-9_.]+(?:\s+[A-Za-z0-9_.]+)*)\s*',line)
  if not m:break
  out+=m.group(1).split()
 return out
qual={r['module']:r for r in inv['qualified_direct_sources']};extdirect={r['module']:r for r in inv['external_direct_sources']}
assert len(inv['drafts_topological'])==195 and len(qual)==42 and set(extdirect)=={'Mathlib.Algebra.Ring.Basic','Mathlib.Tactic.Ring'}
direct=set()
for r in inv['drafts_topological']:
 p=O/r['overlay_path'];assert p.is_file() and not p.is_symlink() and sha(p.read_bytes())==r['overlay_sha256'],r['module']
 names=imports(p);assert [x for x in names if '.' not in x]==r['bare_imports'] and [x for x in names if '.' in x]==r['qualified_imports'],r['module']
 direct.update(n for n in names if '.' in n)
assert direct==set(qual)|set(extdirect)
for n,r in qual.items():
 p=D/r['path'];assert p.is_file() and r['path']=='Lean/'+n.replace('.','/')+'.lean' and sha(p.read_bytes())==r['sha256']
for n,r in extdirect.items():assert sha((ROOT/r['path']).read_bytes())==r['sha256']
records={r['module']:r for r in base['records']};pending=list(direct);seen=set();missing={};front={};external=set()
while pending:
 n=pending.pop()
 if n in seen:continue
 seen.add(n)
 if not n.startswith('DiophantineConsistency.'):
  external.add(n);continue
 p=obj(P72/'lib',n);sp=D/'Lean'/(n.replace('.','/')+'.lean');assert sp.is_file(),n
 sourcehash=sha(sp.read_bytes())
 if p.is_file():
  assert snapshot.get(n)==sourcehash or records.get(n,{}).get('source_sha256')==sourcehash,n
  if n in records:assert records[n]['object_sha256']==sha(p.read_bytes()),n
  front[n]={'object':evidence(p),'current_source_path':str(sp.relative_to(D)),'current_source_sha256':sourcehash,
   'p72_snapshot_source_sha256':snapshot.get(n),'base_record_source_sha256':records.get(n,{}).get('source_sha256'),
   'base_record_object_sha256':records.get(n,{}).get('object_sha256')}
 else:
  deps=imports(sp);missing[n]={'path':str(sp.relative_to(D)),'sha256':sourcehash,'lexical_imports':deps};pending.extend(deps)
for n in missing:assert n not in front
external_obj={n:evidence(obj(PKG,n)) for n in sorted(external)}
# Name observations in the same eight historical roots and thirteen suffixes
# as the natural80 cut. This is not a global search or a future reservation.
roots={'selected_p72':P72/'lib','linked_base':BASE/'lib','guarded_package':PKG,'toolchain':TOOL,
 'workspace_build':ROOT/'.lake/build/lib/lean','prior_p72_attempt':Path('/tmp/p72-current-base-extension-20261105/lib'),
 'captured_p72_endpoint':Path('/tmp/p72-p13-p14-captured-endpoint-20261105/lib'),
 'carrier_retry05':Path('/tmp/current14-coherent490-refactor-retry05-20261110/lib')}
suffixes=['.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash','.so','.dll','.dylib']
names=sorted({r['module'] for r in inv['drafts_topological']}|set(missing));hits=[]
for label,root in roots.items():
 for n in names:
  for suffix in suffixes:
   p=root/(n.replace('.','/')+suffix)
   if os.path.lexists(p):hits.append({'root':label,'module':n,'suffix':suffix,'evidence':evidence(p)})
print(json.dumps({'scope':'bounded point-in-time lexical qualified-source/presence cut and selected-root collision observations; no Lean/provider closure or build-readiness claim',
 'overlay_sha256':sha((O/'inventory.json').read_bytes()),'natural80_cut_sha256':sha((D/'research/ordinary14-natural80-qualified-provider-cut/observation.json').read_bytes()),
 'direct_qualified_count':len(direct),'source_candidates':dict(sorted(missing.items())), 'selected_project_frontier':dict(sorted(front.items())), 'selected_external':external_obj,
 'missing_external_objects':sorted(n for n,v in external_obj.items() if v is None),
 'additional_source_candidates_vs_natural80':sorted(set(missing)-set(prev['source_candidates'])),
 'omitted_source_candidates_vs_natural80':sorted(set(prev['source_candidates'])-set(missing)),
 'additional_project_frontier_vs_natural80':sorted(set(front)-set(prev['selected_project_frontier'])),
 'omitted_project_frontier_vs_natural80':sorted(set(prev['selected_project_frontier'])-set(front)),
 'additional_external_vs_natural80':sorted(set(external)-set(prev['selected_external'])),
 'omitted_external_vs_natural80':sorted(set(prev['selected_external'])-set(external)),
 'collision_scan':{'names':len(names),'roots':{k:str(v) for k,v in roots.items()},'suffixes':suffixes,'hits':hits}},sort_keys=True,indent=2))
