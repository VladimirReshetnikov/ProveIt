#!/usr/bin/env python3
"""Freeze a focused fourteen-module native 17-variable rank witness suffix."""
import hashlib,json,os,re,sys
from pathlib import Path
if len(sys.argv)!=2:raise SystemExit('usage: prepare.py OUTPUT_DIR')
OUT=Path(sys.argv[1]).absolute();R=Path.cwd().resolve();V=R/'Computability/DiophantineConsistency/reviews';SRC=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'
M13=V/'adaptive-square-sums-model-replay';M14=V/'adaptive-square-sums14-direct-model-replay';M15=V/'adaptive-square-sums15-model-replay';M16=V/'adaptive-square-sums16-model-replay';M17=V/'adaptive-square-sums17-model-replay';P258=Path('/tmp/ipra-current-repaired-build-y6kamkla');M107=V/'ipra-current-repaired-six-drift-replay/manifest.json';SUR=V/'ipra-current-repaired-survey'
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');PKG=Path('/tmp/pra14-full-transitive-2x6o__to/package-lib');TOOL=LEAN.parent.parent/'lib/lean'
SIDECARS=('.olean','.olean.private','.olean.server','.ir','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean','.ilean.hash')
order=['PRAExpressionZFCStrict','HAExpressionSameZero','HAExpressionNoZeroEquiv','HAExpressionNoZeroEquivChecks','IPRAExpressionNative','IPRAExpressionNativeChecks','IPRASquareWitnessDirect14Native','IPRASquareWitnessDirect14NativeChecks','IPRAScaleWitness15Native','IPRAScaleWitness15NativeChecks','IPRAMainScaleWitness16Native','IPRAMainScaleWitness16NativeChecks','IPRARankWitness17Native','IPRARankWitness17NativeChecks']
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();gate={}
def pin(path,expected=None):
 p=Path(path).absolute();assert p.is_file() and p.resolve()==p,('noncanonical gate',str(p));h=H(p);assert expected is None or expected==h,(str(p),expected,h);assert str(p) not in gate or gate[str(p)]==h;gate[str(p)]=h;return h
def read(path):pin(path);return json.loads(Path(path).read_text())
def inventory(root):
 out={}
 for d,_,fs in os.walk(root/'lib',followlinks=True):
  for n in fs:
   if n.endswith(SIDECARS):
    p=Path(d)/n;out[str(p.relative_to(root/'lib'))]={'sha256':H(p),'resolved_path':str(p.resolve())}
 return out
def guards(rows):
 for path,row in rows.items():
  if row is None:assert not os.path.lexists(path),path
  else:assert Path(path).is_file() and str(Path(path).resolve())==row['realpath'] and H(path)==row['sha256'],path
def authenticate_model(dir,r,count):
 assert r['status']=='MATCHED_PASS' and len(r['runs'])==2 and r['base']['lean']==H(LEAN)
 for label,x in zip(('author','peer'),r['runs']):
  assert x['label']==label and len(x['rows'])==count and x['guarded_companion_paths']==len(x['guards']);guards(x['guards'])
  for row in x['rows']:
   n=row['module'];assert row['exit']==0 and row['source_sha256']==r['base']['sources'][n]
   pin(dir/label/'src'/'DiophantineConsistency'/(n+'.lean'),row['source_sha256']);pin(dir/label/'logs'/(n+'.log'),row['log_sha256'])
   obj=Path(x['run'])/'lib'/'DiophantineConsistency'/(n+'.olean');assert obj.is_file() and not obj.is_symlink() and obj.resolve()==obj.absolute();pin(obj,row['object_sha256'])
   for dep,h in row['direct_inputs'].items():
    p=Path(dep) if Path(dep).is_absolute() else Path(x['run'])/'lib'/dep;assert H(p)==h
 for a,b in zip(r['runs'][0]['rows'],r['runs'][1]['rows']):assert a==b
 A,B=(Path(x['run']) for x in r['runs']);assert A.resolve()!=B.resolve();return A,B
assert not OUT.exists(),'refusing to overwrite';prep=Path(__file__).read_bytes();driver=(Path(__file__).resolve().parent/'replay.py').read_bytes()
r13,r14,r15,r16,r17=read(M13/'receipt.json'),read(M14/'receipt.json'),read(M15/'receipt.json'),read(M16/'receipt.json'),read(M17/'receipt.json');m=read(M107);survey=read(SUR/'manifest.json');parent=read(P258/'state.json')
assert parent['status']=='PASS' and r13['base']['parent_state']==m['parent_state_sha256']==H(P258/'state.json')
assert r14['base']['parent_state']==H(M13/'receipt.json') and r15['base']['parent_state']==H(M14/'receipt.json') and r16['base']['parent_state']==H(M15/'receipt.json') and r17['base']['parent_state']==H(M16/'receipt.json') and m['lean_sha256']==H(LEAN)
pin(R/'Computability/DiophantineConsistency/research/adaptive-square-sums/replay_model.py',r13['base']['driver'])
pin(R/'Computability/DiophantineConsistency/research/adaptive-square-sums14-direct/replay_model.py',r14['base']['driver'])
pin(R/'Computability/DiophantineConsistency/research/adaptive-square-sums15/replay_model.py',r15['base']['driver'])
pin(R/'Computability/DiophantineConsistency/research/adaptive-square-sums16/replay_model.py',r16['base']['driver'])
pin(R/'Computability/DiophantineConsistency/research/adaptive-square-sums17/replay_model.py',r17['base']['driver'])
for path,h in m['gate_guard'].items():pin(path,h)
for path,h in m['origin_guard'].items():pin(path,h)
for n,row in survey['sources'].items():
 p=SUR/'sources'/(n.replace('.', '/')+'.lean');assert p.is_file() and not p.is_symlink() and p.resolve()==p.absolute();pin(p,row['sha256'])
A13,B13=authenticate_model(M13,r13,3);A14,B14=authenticate_model(M14,r14,2);A15,B15=authenticate_model(M15,r15,2);A16,B16=authenticate_model(M16,r16,2);A17,B17=authenticate_model(M17,r17,2)
base=inventory(P258);assert base==m['parent_inventory'],'258 parent inventory mismatch'
def extended(base,root,rows):
 out=dict(base)
 for row in rows:
  rel='DiophantineConsistency/'+row['module']+'.olean';assert rel not in out;obj=root/'lib'/rel;out[rel]={'sha256':row['object_sha256'],'resolved_path':str(obj.absolute())}
 return out
expected13=[]
for root,x in ((A13,r13['runs'][0]),(B13,r13['runs'][1])):
 inv=extended(base,root,x['rows']);assert inventory(root)==inv;expected13.append(inv)
expected14=[]
for root,x in ((A14,r14['runs'][0]),(B14,r14['runs'][1])):
 inv=extended(expected13[1],root,x['rows']);assert inventory(root)==inv;expected14.append(inv)
assert r14['runs'][0]['run']==str(A14) and r14['runs'][1]['run']==str(B14)
expected15=[]
for root,x in ((A15,r15['runs'][0]),(B15,r15['runs'][1])):
 inv=extended(expected14[1],root,x['rows']);assert inventory(root)==inv;expected15.append(inv)
assert r15['runs'][0]['run']==str(A15) and r15['runs'][1]['run']==str(B15)
expected16=[]
for root,x in ((A16,r16['runs'][0]),(B16,r16['runs'][1])):
 inv=extended(expected15[1],root,x['rows']);assert inventory(root)==inv;expected16.append(inv)
assert r16['runs'][0]['run']==str(A16) and r16['runs'][1]['run']==str(B16)
expected17=[]
for root,x in ((A17,r17['runs'][0]),(B17,r17['runs'][1])):
 inv=extended(expected16[1],root,x['rows']);assert inventory(root)==inv;expected17.append(inv)
assert r17['runs'][0]['run']==str(A17) and r17['runs'][1]['run']==str(B17)
for path,h in m['parent_external_direct_paths'].items():assert H(path)==h and str(Path(path).resolve())==m['parent_external_resolved_paths'][path]
assert all(not os.path.lexists(p) for p in m['parent_external_absent_paths'])
for name,row in survey['external'].items():guards(row['companions'])
guards(m['fallback_companions'])
sources={};seen=set();indices=set('DiophantineConsistency.'+n for n in order)
for n in order:
 raw=(SRC/(n+'.lean')).read_bytes();imports=re.findall(r'^import\s+([A-Z][\w.]*)',raw.decode(),re.M);assert imports and all(d not in indices or d in seen for d in imports);seen.add('DiophantineConsistency.'+n)
 sources[n]={'sha256':hashlib.sha256(raw).hexdigest(),'imports':imports}
for n in order:
 for suf in SIDECARS:assert not os.path.lexists(B17/'lib'/'DiophantineConsistency'/(n+suf)),('output already exists',n,suf)
fallback={}
for n in order:
 for root in (PKG,TOOL):
  for suf in SIDECARS:
   p=(root/'DiophantineConsistency'/(n+suf)).absolute()
   if os.path.lexists(p):assert p.is_file();fallback[str(p)]={'sha256':H(p),'realpath':str(p.resolve())}
   else:fallback[str(p)]=None
def audit():
 assert all(str(Path(p).resolve())==p and H(p)==h for p,h in gate.items())
 assert inventory(P258)==base==m['parent_inventory'] and inventory(A13)==expected13[0] and inventory(B13)==expected13[1] and inventory(A14)==expected14[0] and inventory(B14)==expected14[1] and inventory(A15)==expected15[0] and inventory(B15)==expected15[1] and inventory(A16)==expected16[0] and inventory(B16)==expected16[1] and inventory(A17)==expected17[0] and inventory(B17)==expected17[1]
 for r in (r13,r14,r15,r16,r17):
  for x in r['runs']:guards(x['guards'])
 for path,h in m['parent_external_direct_paths'].items():assert H(path)==h and str(Path(path).resolve())==m['parent_external_resolved_paths'][path]
 assert all(not os.path.lexists(p) for p in m['parent_external_absent_paths'])
 for row in survey['external'].values():guards(row['companions'])
 guards(m['fallback_companions'])
 guards(fallback);assert all(H(SRC/(n+'.lean'))==row['sha256'] for n,row in sources.items())
 assert H(__file__)==hashlib.sha256(prep).hexdigest() and H(Path(__file__).resolve().parent/'replay.py')==hashlib.sha256(driver).hexdigest()
audit();OUT.mkdir();snap=OUT/'sources'/'DiophantineConsistency';snap.mkdir(parents=True)
for n,row in sources.items():
 with (snap/(n+'.lean')).open('xb') as f:f.write((SRC/(n+'.lean')).read_bytes())
 assert H(snap/(n+'.lean'))==row['sha256']
audit();assert all(H(snap/(n+'.lean'))==row['sha256'] for n,row in sources.items())
out={'status':'FOCUSED_RANK17_NATIVE_INPUT','workspace_root':str(R),'parent':str(B17),'parent_inventory':expected17[1],
 'model13_receipt_sha256':H(M13/'receipt.json'),'model14_receipt_sha256':H(M14/'receipt.json'),'model15_receipt_sha256':H(M15/'receipt.json'),'model16_receipt_sha256':H(M16/'receipt.json'),'model17_receipt_sha256':H(M17/'receipt.json'),'sources':sources,'order':order,'gate_guard':gate,'origin_guard':m['origin_guard'],
 'model_guards':[x['guards'] for r in (r13,r14,r15,r16,r17) for x in r['runs']],'parent_external_direct_paths':m['parent_external_direct_paths'],
 'parent_external_resolved_paths':m['parent_external_resolved_paths'],'parent_external_absent_paths':m['parent_external_absent_paths'],
 'external':survey['external'],'fallback_companions':fallback,'inherited_fallback_companions':m['fallback_companions'],'lean_sha256':m['lean_sha256'],
 'preparer_sha256':hashlib.sha256(prep).hexdigest(),'driver_sha256':hashlib.sha256(driver).hexdigest(),
 'boundary':'Focused source-directed same-provider suffix on matched historical 17-variable rank-model peers. Original 258 project ancestry, 848 author-only ancestry, external package-transitive ancestry and dynamic imports remain inherited. Workspace checks cover the fourteen rebuilt sources only; no full current-source closure is claimed.'}
with (OUT/'prepare.py').open('xb') as f:f.write(prep)
with (OUT/'replay.py').open('xb') as f:f.write(driver)
with (OUT/'manifest.json').open('x') as f:json.dump(out,f,indent=2,sort_keys=True);f.write('\n')
print('PASS_INPUT',len(order),'manifest',H(OUT/'manifest.json'),flush=True)
