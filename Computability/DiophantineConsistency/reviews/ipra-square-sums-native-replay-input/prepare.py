#!/usr/bin/env python3
"""Freeze a focused six-module native-square suffix on matched model peers."""
import hashlib,json,os,re,shutil,sys
from pathlib import Path
if len(sys.argv)!=2:raise SystemExit('usage: prepare.py OUTPUT_DIR')
OUT=Path(sys.argv[1]).absolute();R=Path.cwd().resolve();V=R/'Computability/DiophantineConsistency/reviews';SRC=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'
MODEL=V/'adaptive-square-sums-model-replay';P258=Path('/tmp/ipra-current-repaired-build-y6kamkla');M107=V/'ipra-current-repaired-six-drift-replay/manifest.json';SUR=V/'ipra-current-repaired-survey'
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');PKG=Path('/tmp/pra14-full-transitive-2x6o__to/package-lib');TOOL=LEAN.parent.parent/'lib/lean'
SIDECARS=('.olean','.olean.private','.olean.server','.ir','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean','.ilean.hash')
order=['PRAExpressionZFCStrict','HAExpressionSameZero','IPRAExpressionNative','IPRAExpressionNativeChecks','IPRASquareSumsNative','IPRASquareSumsNativeChecks']
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
assert not OUT.exists(),'refusing to overwrite';prep=Path(__file__).read_bytes();driver=(Path(__file__).resolve().parent/'replay.py').read_bytes()
r=read(MODEL/'receipt.json');m=read(M107);survey=read(SUR/'manifest.json');parent=read(P258/'state.json')
assert r['status']=='MATCHED_PASS' and len(r['runs'])==2 and parent['status']=='PASS'
assert r['base']['lean']==m['lean_sha256']==H(LEAN) and r['base']['parent_state']==H(P258/'state.json')
pin(R/'Computability/DiophantineConsistency/research/adaptive-square-sums/replay_model.py',r['base']['driver'])
assert m['parent_state_sha256']==H(P258/'state.json')
for path,h in m['gate_guard'].items():pin(path,h)
for path,h in m['origin_guard'].items():pin(path,h)
for name,row in survey['sources'].items():
 p=SUR/'sources'/(name.replace('.', '/')+'.lean');assert p.is_file() and not p.is_symlink() and p.resolve()==p.absolute();pin(p,row['sha256'])
for label,x in zip(('author','peer'),r['runs']):
 assert x['label']==label and len(x['rows'])==3 and x['guarded_companion_paths']==len(x['guards'])
 guards(x['guards'])
 for row in x['rows']:
  name=row['module'];assert row['exit']==0 and row['source_sha256']==r['base']['sources'][name]
  pin(MODEL/label/'src'/'DiophantineConsistency'/(name+'.lean'),row['source_sha256'])
  pin(MODEL/label/'logs'/(name+'.log'),row['log_sha256'])
  obj=Path(x['run'])/'lib'/'DiophantineConsistency'/(name+'.olean');assert obj.is_file() and not obj.is_symlink() and obj.resolve()==obj.absolute();pin(obj,row['object_sha256'])
  for dep,h in row['direct_inputs'].items():
   p=Path(dep) if Path(dep).is_absolute() else Path(x['run'])/'lib'/dep;assert H(p)==h
for a,b in zip(r['runs'][0]['rows'],r['runs'][1]['rows']):assert a==b
A,B=(Path(x['run']) for x in r['runs']);assert A.resolve()!=B.resolve()
base=inventory(P258);assert base==m['parent_inventory'], '258 parent inventory mismatch';expected=[]
for run,x in ((A,r['runs'][0]),(B,r['runs'][1])):
 inv=dict(base)
 for row in x['rows']:
  rel='DiophantineConsistency/'+row['module']+'.olean';assert rel not in inv;obj=run/'lib'/rel;inv[rel]={'sha256':row['object_sha256'],'resolved_path':str(obj.absolute())}
 assert inventory(run)==inv;expected.append(inv)
for path,h in m['parent_external_direct_paths'].items():assert H(path)==h and str(Path(path).resolve())==m['parent_external_resolved_paths'][path]
assert all(not os.path.lexists(p) for p in m['parent_external_absent_paths'])
for name,row in survey['external'].items():
 for path,item in row['companions'].items():
  if item is None:assert not os.path.lexists(path)
  else:assert Path(path).is_file() and str(Path(path).resolve())==item['realpath'] and H(path)==item['sha256']
sources={};seen=set();indices=set('DiophantineConsistency.'+n for n in order)
for name in order:
 p=SRC/(name+'.lean');raw=p.read_bytes();imports=re.findall(r'^import\s+([A-Z][\w.]*)',raw.decode(),re.M);assert imports
 assert all(dep not in indices or dep in seen for dep in imports);seen.add('DiophantineConsistency.'+name)
 sources[name]={'sha256':hashlib.sha256(raw).hexdigest(),'imports':imports}
for name in order:
 for suffix in SIDECARS:assert not os.path.lexists(B/'lib'/'DiophantineConsistency'/(name+suffix)),('output already exists',name,suffix)
# Guard all potential package/toolchain candidates for the suffix modules.
fallback={}
for name in order:
 for root in (PKG,TOOL):
  for suffix in SIDECARS:
   p=(root/'DiophantineConsistency'/(name+suffix)).absolute()
   if os.path.lexists(p):assert p.is_file();fallback[str(p)]={'sha256':H(p),'realpath':str(p.resolve())}
   else:fallback[str(p)]=None

def audit():
 assert all(str(Path(p).resolve())==p and H(p)==h for p,h in gate.items())
 assert inventory(P258)==base==m['parent_inventory'] and inventory(A)==expected[0] and inventory(B)==expected[1]
 for x in r['runs']:guards(x['guards'])
 for path,h in m['parent_external_direct_paths'].items():assert H(path)==h and str(Path(path).resolve())==m['parent_external_resolved_paths'][path]
 assert all(not os.path.lexists(p) for p in m['parent_external_absent_paths'])
 for row in survey['external'].values():
  for path,item in row['companions'].items():
   if item is None:assert not os.path.lexists(path)
   else:assert Path(path).is_file() and str(Path(path).resolve())==item['realpath'] and H(path)==item['sha256']
 for path,item in fallback.items():
  if item is None:assert not os.path.lexists(path)
  else:assert Path(path).is_file() and str(Path(path).resolve())==item['realpath'] and H(path)==item['sha256']
 assert all(H(SRC/(n+'.lean'))==row['sha256'] for n,row in sources.items())
 assert H(__file__)==hashlib.sha256(prep).hexdigest() and H(Path(__file__).resolve().parent/'replay.py')==hashlib.sha256(driver).hexdigest()
audit();OUT.mkdir();snap=OUT/'sources'/'DiophantineConsistency';snap.mkdir(parents=True)
for n,row in sources.items():
 with (snap/(n+'.lean')).open('xb') as f:f.write((SRC/(n+'.lean')).read_bytes())
 assert H(snap/(n+'.lean'))==row['sha256']
audit();assert all(H(snap/(n+'.lean'))==row['sha256'] for n,row in sources.items())
out={'status':'FOCUSED_SQUARE_NATIVE_INPUT','workspace_root':str(R),'parent':str(B),'parent_inventory':expected[1],
 'model_receipt_sha256':H(MODEL/'receipt.json'),'sources':sources,'order':order,'gate_guard':gate,'origin_guard':m['origin_guard'],
 'model_guards':[x['guards'] for x in r['runs']],'parent_external_direct_paths':m['parent_external_direct_paths'],
 'parent_external_resolved_paths':m['parent_external_resolved_paths'],'parent_external_absent_paths':m['parent_external_absent_paths'],
 'external':survey['external'],'fallback_companions':fallback,'lean_sha256':m['lean_sha256'],
 'preparer_sha256':hashlib.sha256(prep).hexdigest(),'driver_sha256':hashlib.sha256(driver).hexdigest(),
 'boundary':'Focused source-directed same-provider suffix on matched fixed-snapshot square-model peers. Original 258 project ancestry, 848 author-only ancestry, external package-transitive ancestry and dynamic imports remain inherited. Workspace checks cover the six rebuilt sources only; no full current-source closure is claimed.'}
with (OUT/'prepare.py').open('xb') as f:f.write(prep)
with (OUT/'replay.py').open('xb') as f:f.write(driver)
with (OUT/'manifest.json').open('x') as f:json.dump(out,f,indent=2,sort_keys=True);f.write('\n')
print('PASS_INPUT',len(order),'manifest',H(OUT/'manifest.json'),flush=True)
