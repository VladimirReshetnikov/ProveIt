#!/usr/bin/env python3
"""Provisional 14-variable successor of a matched 107-module parent.

Usage from repo root: prepare.py OUTPUT COMPARISON_A COMPARISON_B AUTHOR_EXIT
PEER_EXIT WRAPPER_A_EXIT WRAPPER_B_EXIT. Requires completed real evidence.
"""
import hashlib,json,os,sys
from pathlib import Path
if len(sys.argv)!=8:raise SystemExit('usage: prepare.py OUTPUT COMPARISON_A COMPARISON_B AUTHOR_EXIT PEER_EXIT WRAPPER_A_EXIT WRAPPER_B_EXIT')
OUT,CA,CB,AE,BE,WA,WB=(Path(x).absolute() for x in sys.argv[1:])
R=Path.cwd().resolve();V=R/'Computability/DiophantineConsistency/reviews'
S13=V/'ipra-current-repaired-six-drift-source-survey';S14=V/'ipra-current-native14-six-drift-source-survey'
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');PKG=Path('/tmp/pra14-full-transitive-2x6o__to/package-lib');TOOL=LEAN.parent.parent/'lib/lean'
SIDECARS=('.olean','.olean.private','.olean.server','.ir','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean','.ilean.hash')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();gate={}
def pin(path,expected=None):
 p=Path(path).absolute();assert p.is_file() and p.resolve()==p,('noncanonical gate',str(p));h=H(p)
 assert expected is None or expected==h,(str(p),expected,h);assert str(p) not in gate or gate[str(p)]==h;gate[str(p)]=h;return h
def read(path):pin(path);return json.loads(Path(path).read_text())
def inventory(root):
 out={}
 for d,_,names in os.walk(root/'lib',followlinks=True):
  for name in names:
   if name.endswith(SIDECARS):
    p=Path(d)/name;out[str(p.relative_to(root/'lib'))]={'sha256':H(p),'resolved_path':str(p.resolve())}
 return out
def observation(path,field,target,digest):
 x=read(path);assert x['status']=='PASS_EXIT_0' and x['exit_code']==0 and x['evidence_kind']=='tool_session_observation' and x['session_id']
 assert x[field+'_path']==str(target) and x[field+'_sha256']==digest;return x
def comparison(directory,obs):
 r=read(directory/'receipt.json');t=read(directory/'terminal.json');assert r['status']=='MATCHED_PASS' and r['rows']==107
 assert t['status']=='PASS_COMPARATOR_EXIT_0' and t['comparator_exit_code']==0 and t['before']==t['after'] and t['receipt_sha256']==H(directory/'receipt.json')
 pin(directory/'compare.py',r['compare_sha256']);pin(directory/'run.py',t['before'][str((directory/'run.py').resolve())]);pin(directory/'run.log',t['log_sha256'])
 for path,h in t['before'].items():pin(path,h)
 assert (directory/'run.log').read_text()==f"MATCHED_PASS 107 rows {r['guarded_file_count']} files workspace_matches {r['workspace_matches_snapshot_through_observations']}\n"
 observation(obs,'terminal',directory/'terminal.json',H(directory/'terminal.json'));return r
assert not OUT.exists(),'refusing to overwrite'
prep=Path(__file__).read_bytes();driver=(Path(__file__).resolve().parent/'replay.py').read_bytes()
ra,rb=comparison(CA,WA),comparison(CB,WB);assert ra==rb and H(CA/'receipt.json')==H(CB/'receipt.json')
A,B=Path(ra['author_path']),Path(ra['peer_path']);assert A.resolve()!=B.resolve() and not os.path.samefile(A/'state.json',B/'state.json')
a,b=read(A/'state.json'),read(B/'state.json');ah,bh=H(A/'state.json'),H(B/'state.json');assert ah==ra['author_state_sha256'] and bh==ra['peer_state_sha256']
assert a['status']==b['status']=='PASS' and len(a['records'])==len(b['records'])==107
observation(AE,'state',A/'state.json',ah);observation(BE,'state',B/'state.json',bh)
plans=[Path(p) for p,h in read(CA/'terminal.json')['before'].items() if Path(p).name=='manifest.json' and h==ra['manifest_sha256']]
assert len(plans)==1;mp=plans[0];m=read(mp);pin(mp.parent/'replay.py',ra['driver_sha256']);pin(mp.parent/'prepare.py',m['preparer_sha256'])
assert m['status']=='PROVISIONAL_REBASE_INPUT' and m['driver_sha256']==ra['driver_sha256'] and a['manifest_sha256']==b['manifest_sha256']==ra['manifest_sha256']
assert a['driver_sha256']==b['driver_sha256']==ra['driver_sha256'] and m['candidate_survey_sha256']==ra['survey_manifest_sha256']
s13,s14=read(S13/'manifest.json'),read(S14/'manifest.json');assert H(S13/'manifest.json')==m['candidate_survey_sha256']
assert s14['status']=='CANDIDATE_SOURCE_SNAPSHOT' and len(s14['sources'])==995 and len(s14['extra_order'])==11 and s14['extra_order'][-1]==s14['target']
# Pin independent source-coverage and compositional Lean-header evidence.
deps=read(S14/'dependency-inheritance-receipt.json')
assert deps['status']=='PASS_DEPENDENCY_RECEIPT_COVERAGE' and deps['unchanged_shared_count']==978 and deps['changed_shared_count']==6 and deps['additional_count']==11
for path,h in deps['input_sha256'].items():pin(path,h)
assert deps['input_sha256'][str((S14/'manifest.json').absolute())]==H(S14/'manifest.json')
source_audit=V/'ipra-current-native14-six-drift-source-audit';sa=read(source_audit/'receipt.json')
assert sa['status']=='PASS_SOURCE_SNAPSHOT' and sa['sources']==995 and sa['shared']==984 and sa['additional']==11 and sa['manifest_sha256']==H(S14/'manifest.json')
pin(source_audit/'audit.py',sa['auditor_sha256'])
for path,h in s14['input_sha256'].items():pin(path,h)
assert set(s14['external'])<=set(s13['external']) and len(s13['sources'])==1099 and len(m['workspace_sources'])==1104
for path,h in m['gate_guard'].items():pin(path,h)
for path,h in m['origin_guard'].items():pin(path,h)
assert H(LEAN)==m['lean_sha256']
assert [x['name'] for x in a['records']]==[x['name'] for x in b['records']]==m['order']==s13['order']
excluded={n.replace('.', '/')+s for n in m['order'] for s in SIDECARS};base={k:v for k,v in m['parent_inventory'].items() if k not in excluded};expected=[]
for root,state in ((A,a),(B,b)):
 inv=dict(base);pin(root/'driver.py',ra['driver_sha256']);pin(root/'manifest.json',ra['manifest_sha256'])
 for row in state['records']:
  n=row['name'];obj=root/'lib'/(n.replace('.', '/')+'.olean');assert row['exit']==0 and 'warnings' in row and obj.is_file() and not obj.is_symlink() and obj.resolve()==obj.absolute()
  pin(obj,row['object_sha256']);pin(root/'logs'/(n.replace('.', '_')+'.log'),row['log_sha256'])
  for v in row['direct_imports'].values():pin(v['resolved_path'],v['sha256'])
  inv[n.replace('.', '/')+'.olean']={'sha256':row['object_sha256'],'resolved_path':str(obj.absolute())}
 assert inventory(root)==inv;expected.append(inv)
for x,y in zip(a['records'],b['records']):
 assert all(x.get(k)==y.get(k) for k in ('name','exit','object_sha256','log_sha256','warnings'))
 assert {n:v['sha256'] for n,v in x['direct_imports'].items()}=={n:v['sha256'] for n,v in y['direct_imports'].items()}
extra=set(s14['extra_order']);assert extra==set(s14['sources'])-set(s13['sources']) and len(set(s14['sources'])&set(s13['sources']))==984
for n,row in s13['sources'].items():
 p=S13/'sources'/(n.replace('.', '/')+'.lean');assert p.is_file() and not p.is_symlink() and p.resolve()==p.absolute();pin(p,row['sha256'])
for n,row in s14['sources'].items():
 p=S14/'sources'/(n.replace('.', '/')+'.lean');assert p.is_file() and not p.is_symlink() and p.resolve()==p.absolute();pin(p,row['sha256'])
 if n not in extra:assert row['sha256']==s13['sources'][n]['sha256'] and row['imports']==s13['sources'][n]['imports']
seen=set()
for n in s14['extra_order']:
 assert all(d not in extra or d in seen for d in s14['sources'][n]['imports']);seen.add(n)
 for root in (PKG,TOOL):
  for suf in SIDECARS:assert not os.path.lexists(root/(n.replace('.', '/')+suf)),('project fallback present',n,suf)
for n in set(s14['sources'])-extra:assert n.replace('.', '/')+'.olean' in expected[1],('missing parent object',n)
def external():
 assert set(m['parent_external_direct_paths'])==set(m['parent_external_resolved_paths'])
 for path,h in m['parent_external_direct_paths'].items():assert H(path)==h and str(Path(path).resolve())==m['parent_external_resolved_paths'][path]
 assert all(not os.path.lexists(p) for p in m['parent_external_absent_paths'])
 for name,row in s13['external'].items():
  rel=name.replace('.', '/')+'.olean';pick=next((p for p in (PKG/rel,TOOL/rel) if p.is_file()),None);assert pick is not None and str(pick.resolve())==row['selected']
  for path,x in row['companions'].items():
   if x is None:assert not os.path.lexists(path)
   else:assert Path(path).is_file() and str(Path(path).resolve())==x['realpath'] and H(path)==x['sha256']
 for path,x in m['fallback_companions'].items():
  if x is None:assert not os.path.lexists(path)
  else:assert Path(path).is_file() and str(Path(path).resolve())==x['realpath'] and H(path)==x['sha256']
def audit():
 assert all(str(Path(p).resolve())==p and H(p)==h for p,h in gate.items());assert inventory(A)==expected[0] and inventory(B)==expected[1];external()
 for n in extra:
  for root in (PKG,TOOL):
   for suf in SIDECARS:assert not os.path.lexists(root/(n.replace('.', '/')+suf))
 assert H(__file__)==hashlib.sha256(prep).hexdigest() and H(Path(__file__).resolve().parent/'replay.py')==hashlib.sha256(driver).hexdigest()
assert set(extra).isdisjoint(m['workspace_sources']);workspace=m['workspace_sources']|{n:s14['sources'][n] for n in extra};assert len(workspace)==1115
def drift():
 out=[]
 for n,row in workspace.items():
  p=R/row['path']
  try:h=H(p) if p.is_file() else None
  except OSError:h=None
  if h!=row['sha256']:out.append({'module':n,'expected':row['sha256'],'actual':h})
 return out
before=drift();audit();after=drift();audit();assert not OUT.exists()
OUT.mkdir();snap=OUT/'sources'
for n,row in s14['sources'].items():
 src=S14/'sources'/(n.replace('.', '/')+'.lean');dst=snap/(n.replace('.', '/')+'.lean');dst.parent.mkdir(parents=True,exist_ok=True)
 with dst.open('xb') as f:f.write(src.read_bytes())
 assert not dst.is_symlink() and H(dst)==row['sha256']
audit();assert all(H(snap/(n.replace('.', '/')+'.lean'))==row['sha256'] for n,row in s14['sources'].items())
manifest={'status':'PROVISIONAL_14_AFTER_107_INPUT','workspace_root':str(R),'parent_state_path':str(B/'state.json'),'parent_state_sha256':bh,
 'parent_inventory':expected[1],'gate_guard':gate,'origin_guard':m['origin_guard'],'external':s13['external'],
 'parent_external_direct_paths':m['parent_external_direct_paths'],'parent_external_resolved_paths':m['parent_external_resolved_paths'],
 'parent_external_absent_paths':m['parent_external_absent_paths'],'parent_fallback_companions':m['fallback_companions'],
 'sources':s14['sources'],'workspace_sources':workspace,'order':s14['extra_order'],'target':s14['target'],'lean_sha256':m['lean_sha256'],
 'preparer_sha256':hashlib.sha256(prep).hexdigest(),'driver_sha256':hashlib.sha256(driver).hexdigest(),
 'workspace_drift_before':before,'workspace_drift_after':after,'parent_comparison_receipt_path':str(CA/'receipt.json'),
 'parent_comparison_receipt_sha256':H(CA/'receipt.json'),'parent_workspace_matches':ra['workspace_matches_snapshot_through_observations'],
 'boundary':'Provisional 14-after-107 design. Source-current status requires the matched parent comparison workspace flag, both child before/after scans and a fresh independent child comparison scan; observations are point-in-time. The 848-project ancestor is author-only and package-transitive/dynamic ancestry is inherited.'}
with (OUT/'prepare.py').open('xb') as f:f.write(prep)
with (OUT/'replay.py').open('xb') as f:f.write(driver)
with (OUT/'manifest.json').open('x') as f:json.dump(manifest,f,indent=2,sort_keys=True);f.write('\n')
print('PROVISIONAL_INPUT',len(s14['sources']),len(extra),'manifest',H(OUT/'manifest.json'),'workspace_drift_before',len(before),'workspace_drift_after',len(after),flush=True)
